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
    line_starts: Vec<usize>,
}

impl SourceFile {
    /// Create a new source file.
    fn new(id: usize, path: PathBuf, source: Arc<str>) -> Self {
        let line_starts = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(i, _)| i + 1))
            .collect();

        Self {
            id,
            path,
            source,
            line_starts,
        }
    }

    /// Get the line and column (1-based) for a byte offset.
    #[must_use]
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let line = self
            .line_starts
            .iter()
            .rposition(|&start| start <= offset)
            .unwrap_or(0);

        let col = offset - self.line_starts[line];

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
        if line_num == 0 || line_num > self.line_starts.len() {
            return None;
        }

        let start = self.line_starts[line_num - 1];
        let end = if line_num < self.line_starts.len() {
            self.line_starts[line_num] - 1 // Exclude newline
        } else {
            self.source.len()
        };

        Some(&self.source[start..end])
    }

    /// Get the total number of lines.
    #[must_use]
    pub const fn num_lines(&self) -> usize {
        self.line_starts.len()
    }

    /// Get the byte offset where a line starts (1-based line number).
    ///
    /// Returns `None` if the line number is out of range.
    #[must_use]
    pub fn line_start(&self, line_num: usize) -> Option<usize> {
        if line_num == 0 || line_num > self.line_starts.len() {
            return None;
        }
        Some(self.line_starts[line_num - 1])
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
