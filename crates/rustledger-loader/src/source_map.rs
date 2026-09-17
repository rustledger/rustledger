//! Source map for tracking file locations.

use rustledger_parser::Span;
use std::path::PathBuf;
use std::sync::Arc;

/// A source file in the source map.
#[derive(Debug, Clone)]
pub struct SourceFile {
    /// Unique ID for this file.
    pub id: usize,
    /// Path to the file.
    pub path: PathBuf,
    /// Source content (shared via Arc to avoid cloning).
    pub source: Arc<str>,
    /// Line start offsets (byte positions where each line starts).
    ///
    /// Built on first use, not on construction. Every consumer is a
    /// diagnostic — `line_col`, `line`, `line_start`, `num_lines` — so a
    /// ledger that reports nothing never needs it, and building it eagerly
    /// meant scanning the whole source for newlines and keeping a `usize`
    /// per line: 3.9% of a warm `check` and 320 KB on a 40,000-line ledger,
    /// for a table nothing read.
    line_starts: std::sync::OnceLock<Vec<usize>>,
}

/// Line and column (1-based, the column in CHARACTERS) for a byte offset in
/// `source`.
///
/// For callers holding only a `&str`. Parse errors are reported before a
/// `SourceMap` exists, so they cannot use [`SourceFile::line_col`]; before
/// #2341 `check.rs` carried its own copy of this and the two conventions
/// disagreed on every non-ASCII line.
///
/// [`SourceFile::line_col`] answers the same question with a cached line-start
/// table, which is what a file reporting thousands of diagnostics needs. The
/// two strategies are pinned to agree by `char_columns_agree_between_surfaces`
/// below; this one is the definition of the rule.
#[must_use]
pub fn line_col_in(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

impl SourceFile {
    /// Create a new source file.
    const fn new(id: usize, path: PathBuf, source: Arc<str>) -> Self {
        Self {
            id,
            path,
            source,
            line_starts: std::sync::OnceLock::new(),
        }
    }

    /// The line-start table, built on first use.
    fn line_starts(&self) -> &[usize] {
        self.line_starts.get_or_init(|| {
            std::iter::once(0)
                .chain(self.source.match_indices('\n').map(|(i, _)| i + 1))
                .collect()
        })
    }

    /// Get the line and column (1-based) for a byte offset.
    ///
    /// The column counts CHARACTERS, not bytes. It counted bytes until #2341,
    /// which put two conventions in one `rledger check --format json` output:
    /// the parse phase converted with a private character-counting helper in
    /// `check.rs` while every validate-phase diagnostic came through here, so
    /// on a line holding `Assets:Café` the two disagreed by one column per
    /// extra byte and an editor placed the caret in the wrong place.
    ///
    /// Counting characters costs a walk of the line, not of the file: the line
    /// is still found with the cached line-start table and `partition_point`,
    /// and only the remainder of that one line is scanned. The helper this
    /// replaced rescanned from byte 0 on every call.
    #[must_use]
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        // `partition_point`, not `rposition`: the table is sorted ascending,
        // so the linear scan this replaces was O(lines) per lookup — fine for
        // one diagnostic, quadratic for a file that reports thousands. The
        // predicate is monotone over a sorted slice, so the count of entries
        // satisfying it is one past the last that does; entry 0 is always 0,
        // so the count is never zero and the subtraction cannot underflow.
        let starts = self.line_starts();
        let line = starts.partition_point(|&start| start <= offset) - 1;

        // Characters on this line that START before the offset -- the same
        // rule `line_col_in` applies, and the reason this counts rather than
        // slices. Slicing needs `offset` to be a character boundary, and an
        // offset landing INSIDE a multi-byte character made `get` return
        // `None`: the drift guard caught that answering column 1, which would
        // have put a caret at the start of the line. Counting also handles an
        // offset past the end without a panic.
        let line_start = starts[line];
        let col = self.source[line_start..]
            .char_indices()
            .take_while(|(i, _)| line_start + i < offset)
            .count();

        (line + 1, col + 1)
    }

    /// Get the source text for a span.
    #[must_use]
    pub fn span_text(&self, span: &Span) -> &str {
        &self.source[span.start..span.end.min(self.source.len())]
    }

    /// Get a specific line (1-based).
    #[must_use]
    pub fn line(&self, line_num: usize) -> Option<&str> {
        let starts = self.line_starts();
        if line_num == 0 || line_num > starts.len() {
            return None;
        }

        let start = starts[line_num - 1];
        let end = if line_num < starts.len() {
            starts[line_num] - 1 // Exclude newline
        } else {
            self.source.len()
        };

        Some(&self.source[start..end])
    }

    /// Get the total number of lines.
    #[must_use]
    pub fn num_lines(&self) -> usize {
        self.line_starts().len()
    }

    /// Get the byte offset where a line starts (1-based line number).
    ///
    /// Returns `None` if the line number is out of range.
    #[must_use]
    pub fn line_start(&self, line_num: usize) -> Option<usize> {
        let starts = self.line_starts();
        if line_num == 0 || line_num > starts.len() {
            return None;
        }
        Some(starts[line_num - 1])
    }
}

/// A map of source files for error reporting.
#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    /// Create a new source map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a file to the source map.
    ///
    /// Returns the file ID.
    ///
    /// # Panics
    ///
    /// Panics if adding this file would produce an ID that collides with
    /// [`rustledger_parser::SYNTHESIZED_FILE_ID`] (i.e., with more than
    /// `u16::MAX - 1` = 65,534 loaded files). Directives stored in
    /// `Spanned<T>` use a `u16` for `file_id`, and the topmost value is
    /// reserved as a sentinel for plugin-synthesized directives.
    pub fn add_file(&mut self, path: PathBuf, source: Arc<str>) -> usize {
        let id = self.files.len();
        assert!(
            id < rustledger_parser::SYNTHESIZED_FILE_ID as usize,
            "SourceMap exceeded {} files; file_id {id} collides with SYNTHESIZED_FILE_ID sentinel",
            rustledger_parser::SYNTHESIZED_FILE_ID,
        );
        self.files.push(SourceFile::new(id, path, source));
        id
    }

    /// Get a file by ID.
    #[must_use]
    pub fn get(&self, id: usize) -> Option<&SourceFile> {
        self.files.get(id)
    }

    /// Get a file by path.
    #[must_use]
    pub fn get_by_path(&self, path: &std::path::Path) -> Option<&SourceFile> {
        self.files.iter().find(|f| f.path == path)
    }

    /// Get all files.
    #[must_use]
    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }

    /// Format a span for display.
    #[must_use]
    pub fn format_span(&self, file_id: usize, span: &Span) -> String {
        if let Some(file) = self.get(file_id) {
            let (line, col) = file.line_col(span.start);
            format!("{}:{}:{}", file.path.display(), line, col)
        } else {
            format!("?:{}..{}", span.start, span.end)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_col() {
        let source: Arc<str> = "line 1\nline 2\nline 3".into();
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source);

        assert_eq!(file.line_col(0), (1, 1)); // Start of line 1
        assert_eq!(file.line_col(5), (1, 6)); // "1" in line 1
        assert_eq!(file.line_col(7), (2, 1)); // Start of line 2
        assert_eq!(file.line_col(14), (3, 1)); // Start of line 3
    }

    /// The two surfaces of the same rule must agree (#2341).
    ///
    /// `line_col_in` walks the string; `SourceFile::line_col` finds the line
    /// with a cached table and then counts characters within it. Different
    /// strategies, one answer -- including on the non-ASCII lines that made
    /// the old byte-counting column wrong, on CRLF, and at offsets sitting on
    /// and past the end.
    #[test]
    fn char_columns_agree_between_surfaces() {
        for source in [
            "2026-01-01 open Assets:Café\n  Assets:Café  -1 ABC\n",
            "a\r\nb\r\n",
            "ascii only\nsecond line\n",
            "\u{1f600} emoji first\nthen ascii\n",
            "no trailing newline",
            "",
        ] {
            let file = SourceFile::new(0, std::path::PathBuf::from("t.beancount"), source.into());
            for offset in 0..=source.len() + 2 {
                assert_eq!(
                    file.line_col(offset),
                    line_col_in(source, offset),
                    "offset {offset} in {source:?}",
                );
            }
        }
    }

    #[test]
    fn test_get_line() {
        let source: Arc<str> = "line 1\nline 2\nline 3".into();
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source);

        assert_eq!(file.line(1), Some("line 1"));
        assert_eq!(file.line(2), Some("line 2"));
        assert_eq!(file.line(3), Some("line 3"));
        assert_eq!(file.line(0), None);
        assert_eq!(file.line(4), None);
    }

    #[test]
    fn test_line_start() {
        let source: Arc<str> = "line 1\nline 2\nline 3".into();
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source);

        // Happy path - valid line numbers
        assert_eq!(file.line_start(1), Some(0)); // Line 1 starts at byte 0
        assert_eq!(file.line_start(2), Some(7)); // Line 2 starts at byte 7 (after "line 1\n")
        assert_eq!(file.line_start(3), Some(14)); // Line 3 starts at byte 14

        // Boundary conditions
        assert_eq!(file.line_start(0), None); // Line 0 is invalid (1-based)
        assert_eq!(file.line_start(4), None); // Line 4 is out of range
        assert_eq!(file.line_start(100), None); // Way out of range
    }

    #[test]
    fn test_source_map() {
        let mut sm = SourceMap::new();
        let id = sm.add_file(PathBuf::from("test.beancount"), "content".into());

        assert_eq!(id, 0);
        assert!(sm.get(0).is_some());
        assert!(sm.get(1).is_none());
    }
}
