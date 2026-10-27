//! Source map for tracking file locations.

use rustledger_parser::Span;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Owned file contents, shared cheaply.
///
/// A newtype over `Arc<String>` rather than `Arc<str>`: `Arc<str>::from(String)`
/// always copies the bytes into a fresh allocation (std has no zero-copy
/// `String -> Arc<str>`), so every file read paid a second full-file buffer
/// plus a `memcpy`. `Arc<String>` takes the `String`'s allocation as-is: a
/// `read` keeps the buffer `String::from_utf8` already owns.
///
/// Migrating from `Arc<str>`: a `String` converts zero-copy with
/// `SourceText::from(string)`; an `Arc<str>` converts with
/// `SourceText::from(&*arc)`, which copies.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceText(Arc<String>);

impl SourceText {
    /// The contents as a `str`.
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<&str> for SourceText {
    fn from(s: &str) -> Self {
        Self(Arc::new(s.to_owned()))
    }
}

impl From<String> for SourceText {
    fn from(s: String) -> Self {
        Self(Arc::new(s))
    }
}

impl std::ops::Deref for SourceText {
    type Target = str;

    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl AsRef<str> for SourceText {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

/// A source file in the source map.
#[derive(Debug, Clone)]
pub struct SourceFile {
    /// Unique ID for this file.
    pub id: usize,
    /// Path to the file: its identity, symlinks resolved on disk (see
    /// [`crate::FileSystem::normalize`]). Two includes of one file share it.
    pub path: PathBuf,
    /// The path the file was opened by: absolute, `.` and `..` collapsed
    /// textually, symlinks NOT resolved (see
    /// [`crate::FileSystem::normalize_lexical`]). Relative paths written in
    /// the file — `include`, `document`, `option "documents"` — resolve
    /// against its parent, [`Self::dir`], as beancount resolves them (#2635).
    /// Equal to [`Self::path`] unless a symlink is on the way.
    pub opened_path: PathBuf,
    /// Source content (shared via [`SourceText`] to avoid cloning).
    pub source: SourceText,
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
/// The definition of the rule, for a one-off lookup in a `&str`. For many
/// lookups in one text use [`LineIndex`], which answers identically. Parse
/// errors are reported before a `SourceMap` exists, so they cannot use
/// [`SourceFile::line_col`]; before
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

/// Byte offsets at which each line of `source` starts (entry 0 is always 0).
fn line_starts_of(source: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(source.match_indices('\n').map(|(i, _)| i + 1))
        .collect()
}

/// [`line_col_in`]'s answer, found through a line-start table: the line by
/// `partition_point`, then only that one line is walked.
fn line_col_indexed(source: &str, starts: &[usize], offset: usize) -> (usize, usize) {
    // `partition_point`, not `rposition`: the table is sorted ascending,
    // so a linear scan would be O(lines) per lookup — fine for one
    // diagnostic, quadratic for a file that reports thousands. The
    // predicate is monotone over a sorted slice, so the count of entries
    // satisfying it is one past the last that does; entry 0 is always 0,
    // so the count is never zero and the subtraction cannot underflow.
    let line = starts.partition_point(|&start| start <= offset) - 1;

    // Characters on this line that START before the offset -- the same
    // rule `line_col_in` applies, and the reason this counts rather than
    // slices. Slicing needs `offset` to be a character boundary, and an
    // offset landing INSIDE a multi-byte character made `get` return
    // `None`: the drift guard caught that answering column 1, which would
    // have put a caret at the start of the line. Counting also handles an
    // offset past the end without a panic.
    let line_start = starts[line];
    let col = source[line_start..]
        .char_indices()
        .take_while(|(i, _)| line_start + i < offset)
        .count();

    (line + 1, col + 1)
}

/// [`line_col_in`] for many lookups in one `&str`: the line-start table is
/// built once, so each lookup walks one line instead of the file.
///
/// For callers that have the text but no [`SourceFile`] — parse errors are
/// reported before a [`SourceMap`] exists. Rescanning from byte 0 per lookup
/// made `check --format json` quadratic in the number of parse errors (#2632).
#[derive(Debug, Clone)]
pub struct LineIndex<'a> {
    source: &'a str,
    starts: Vec<usize>,
}

impl<'a> LineIndex<'a> {
    /// Index `source`.
    #[must_use]
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            starts: line_starts_of(source),
        }
    }

    /// Line and column (1-based, the column in CHARACTERS) for a byte offset,
    /// exactly as [`line_col_in`] answers it.
    #[must_use]
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        line_col_indexed(self.source, &self.starts, offset)
    }
}

impl SourceFile {
    /// Create a new source file.
    #[cfg(test)]
    fn new(id: usize, path: PathBuf, source: SourceText) -> Self {
        let opened_path = path.clone();
        Self::new_opened(id, path, opened_path, source)
    }

    /// Create a new source file reached by `opened_path`.
    const fn new_opened(
        id: usize,
        path: PathBuf,
        opened_path: PathBuf,
        source: SourceText,
    ) -> Self {
        Self {
            id,
            path,
            opened_path,
            source,
            line_starts: std::sync::OnceLock::new(),
        }
    }

    /// The directory relative paths in this file resolve against: the parent
    /// of [`Self::opened_path`], or `.` when it has none.
    #[must_use]
    pub fn dir(&self) -> &Path {
        self.opened_path.parent().unwrap_or_else(|| Path::new("."))
    }

    /// The line-start table, built on first use.
    fn line_starts(&self) -> &[usize] {
        self.line_starts
            .get_or_init(|| line_starts_of(&self.source))
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
        line_col_indexed(&self.source, self.line_starts(), offset)
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
    /// The placeholder locations handed out by
    /// [`Self::placeholder_file_id`], in id order from
    /// [`rustledger_parser::FIRST_PLACEHOLDER_FILE_ID`]. Behind a lock
    /// because plugins run with a shared `&SourceMap` (the loader and the
    /// LSP hand one to [`crate::run_plugins`]); placeholders are only added,
    /// never changed, so an id stays valid for the map's life.
    placeholders: parking_lot::Mutex<Placeholders>,
}

/// See [`SourceMap::placeholder_file_id`].
#[derive(Debug, Default)]
struct Placeholders {
    /// `(name, line)` of each placeholder, by `id - FIRST_PLACEHOLDER_FILE_ID`.
    locations: Vec<(PathBuf, u32)>,
    /// The id of each `(name, line)`, so one location gets one id.
    ids: rustc_hash::FxHashMap<(PathBuf, u32), u16>,
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
    /// Panics if adding this file would produce an ID at or above
    /// [`rustledger_parser::FIRST_PLACEHOLDER_FILE_ID`] (i.e., with more than
    /// 61,440 loaded files). Directives stored in `Spanned<T>` use a `u16`
    /// for `file_id`, and the ids from there up are reserved for placeholder
    /// locations and the plugin-synthesized sentinel
    /// [`rustledger_parser::SYNTHESIZED_FILE_ID`].
    pub fn add_file(&mut self, path: PathBuf, source: SourceText) -> usize {
        let opened_path = path.clone();
        self.add_opened_file(path, opened_path, source)
    }

    /// Add a file reached by `opened_path` whose identity is `path`; see
    /// [`SourceFile::opened_path`].
    ///
    /// Returns the file ID.
    ///
    /// # Panics
    ///
    /// As [`Self::add_file`].
    pub fn add_opened_file(
        &mut self,
        path: PathBuf,
        opened_path: PathBuf,
        source: SourceText,
    ) -> usize {
        let id = self.files.len();
        assert!(
            id < rustledger_parser::FIRST_PLACEHOLDER_FILE_ID as usize,
            "SourceMap exceeded {} files; file_id {id} collides with the reserved placeholder ids",
            rustledger_parser::FIRST_PLACEHOLDER_FILE_ID,
        );
        self.files
            .push(SourceFile::new_opened(id, path, opened_path, source));
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

    /// The `file_id` of the placeholder location `name`, line `line`: a
    /// location with no source text, such as beancount's `<check_closing>:0`
    /// or the main file at line 0 (#2713).
    ///
    /// A plugin gives a directive it creates such a location; the loader
    /// turns it into this id, so an error on the directive is reported at
    /// `name:line`, as `bean-check` reports it, instead of with no location.
    /// The id is in [`rustledger_parser::FIRST_PLACEHOLDER_FILE_ID`]'s range,
    /// so nothing mistakes it for a source file: [`Self::get`] does not find
    /// it, and the directive has no source identity, as a synthesized one
    /// has none. One `(name, line)` gets one id.
    ///
    /// Returns [`rustledger_parser::SYNTHESIZED_FILE_ID`] (no location) once
    /// the range's 4,095 ids are taken.
    pub fn placeholder_file_id(&self, name: &Path, line: u32) -> u16 {
        let mut table = self.placeholders.lock();
        let key = (name.to_path_buf(), line);
        if let Some(&id) = table.ids.get(&key) {
            return id;
        }
        let id = usize::from(rustledger_parser::FIRST_PLACEHOLDER_FILE_ID) + table.locations.len();
        // The sentinel and above are not placeholders.
        let id = match u16::try_from(id) {
            Ok(id) if id != rustledger_parser::SYNTHESIZED_FILE_ID => id,
            _ => return rustledger_parser::SYNTHESIZED_FILE_ID,
        };
        table.locations.push(key.clone());
        table.ids.insert(key, id);
        id
    }

    /// The name and line of the placeholder location `file_id` (see
    /// [`Self::placeholder_file_id`]), or `None` when `file_id` is not one.
    #[must_use]
    pub fn placeholder(&self, file_id: u16) -> Option<(PathBuf, u32)> {
        if rustledger_parser::is_source_file_id(file_id)
            || file_id == rustledger_parser::SYNTHESIZED_FILE_ID
        {
            // Without taking the lock: callers ask for every directive a
            // file does not hold, most of them synthesized.
            return None;
        }
        let index = file_id - rustledger_parser::FIRST_PLACEHOLDER_FILE_ID;
        let table = self.placeholders.lock();
        table.locations.get(usize::from(index)).cloned()
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

    /// #2713: a placeholder location gets an id in the reserved range, one
    /// id per `(name, line)`, that resolves back to its name and line and is
    /// never a source file.
    #[test]
    fn placeholder_ids_resolve_and_are_not_source_files() {
        let mut map = SourceMap::new();
        map.add_file(PathBuf::from("main.beancount"), SourceText::from("x"));
        let a = map.placeholder_file_id(Path::new("<check_closing>"), 0);
        let b = map.placeholder_file_id(Path::new("main.beancount"), 0);
        assert_eq!(a, rustledger_parser::FIRST_PLACEHOLDER_FILE_ID);
        assert_eq!(b, a + 1);
        assert_eq!(map.placeholder_file_id(Path::new("<check_closing>"), 0), a);
        assert_ne!(map.placeholder_file_id(Path::new("<check_closing>"), 1), a);
        assert_eq!(
            map.placeholder(a),
            Some((PathBuf::from("<check_closing>"), 0))
        );
        assert_eq!(
            map.placeholder(b),
            Some((PathBuf::from("main.beancount"), 0))
        );
        assert!(!rustledger_parser::is_source_file_id(a));
        assert!(map.get(a as usize).is_none());
        assert_eq!(map.placeholder(0), None);
        assert_eq!(
            map.placeholder(rustledger_parser::SYNTHESIZED_FILE_ID),
            None
        );
    }

    /// Once the range is used up, a location is given no id, rather than one
    /// that collides with the synthesized sentinel.
    #[test]
    fn placeholder_ids_stop_below_the_sentinel() {
        let map = SourceMap::new();
        let room =
            rustledger_parser::SYNTHESIZED_FILE_ID - rustledger_parser::FIRST_PLACEHOLDER_FILE_ID;
        for line in 0..u32::from(room) {
            let id = map.placeholder_file_id(Path::new("<p>"), line);
            assert!(id < rustledger_parser::SYNTHESIZED_FILE_ID);
        }
        assert_eq!(
            map.placeholder_file_id(Path::new("<p>"), u32::from(room)),
            rustledger_parser::SYNTHESIZED_FILE_ID
        );
        // A location already given an id keeps it.
        assert_eq!(
            map.placeholder_file_id(Path::new("<p>"), 0),
            rustledger_parser::FIRST_PLACEHOLDER_FILE_ID
        );
    }

    #[test]
    fn test_line_col() {
        let source: SourceText = "line 1\nline 2\nline 3".into();
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
            let index = LineIndex::new(source);
            for offset in 0..=source.len() + 2 {
                let expected = line_col_in(source, offset);
                assert_eq!(
                    file.line_col(offset),
                    expected,
                    "offset {offset} in {source:?}"
                );
                assert_eq!(
                    index.line_col(offset),
                    expected,
                    "LineIndex: offset {offset} in {source:?}"
                );
            }
        }
    }

    #[test]
    fn test_get_line() {
        let source: SourceText = "line 1\nline 2\nline 3".into();
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source);

        assert_eq!(file.line(1), Some("line 1"));
        assert_eq!(file.line(2), Some("line 2"));
        assert_eq!(file.line(3), Some("line 3"));
        assert_eq!(file.line(0), None);
        assert_eq!(file.line(4), None);
    }

    #[test]
    fn test_line_start() {
        let source: SourceText = "line 1\nline 2\nline 3".into();
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

    #[test]
    fn test_source_text_from_string_keeps_allocation() {
        let s = String::from("2024-01-01 open Assets:Cash\n");
        let data = s.as_ptr();
        let text = SourceText::from(s);
        assert_eq!(text.as_str().as_ptr(), data);
    }

    #[test]
    fn test_source_text_deref_to_str() {
        let text = SourceText::from("line 1\nline 2");
        let as_str: &str = &text;
        assert_eq!(as_str, "line 1\nline 2");
        // str methods resolve through `Deref`.
        assert_eq!(text.lines().count(), 2);
        assert_eq!(AsRef::<str>::as_ref(&text), "line 1\nline 2");
    }

    #[test]
    fn test_source_text_eq_compares_contents() {
        let a = SourceText::from("abc");
        let b = SourceText::from(String::from("abc"));
        assert_eq!(a, b);
        assert_eq!(a.clone(), a);
        assert_ne!(a, SourceText::from("xyz"));
    }

    #[test]
    fn test_source_text_from_str_copies_contents() {
        let original = "include \"other.beancount\"";
        let text = SourceText::from(original);
        assert_eq!(text.as_str(), original);
        assert_ne!(text.as_str().as_ptr(), original.as_ptr());
    }
}
