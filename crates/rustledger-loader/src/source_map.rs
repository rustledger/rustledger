//! Source map for tracking file locations.

use rustledger_parser::Span;
use std::path::PathBuf;

/// A source file in the source map.
#[derive(Debug, Clone)]
pub struct SourceFile {
    /// Unique ID for this file.
    pub id: usize,
    /// Path to the file.
    pub path: PathBuf,
    /// Source content.
    pub source: String,
    /// Line start offsets (byte positions where each line starts).
    line_starts: Vec<usize>,
}

impl SourceFile {
    /// Create a new source file.
    fn new(id: usize, path: PathBuf, source: String) -> Self {
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
    pub fn num_lines(&self) -> usize {
        self.line_starts.len()
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
    pub fn add_file(&mut self, path: PathBuf, source: String) -> usize {
        let id = self.files.len();
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
        let source = "line 1\nline 2\nline 3";
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source.to_string());

        assert_eq!(file.line_col(0), (1, 1)); // Start of line 1
        assert_eq!(file.line_col(5), (1, 6)); // "1" in line 1
        assert_eq!(file.line_col(7), (2, 1)); // Start of line 2
        assert_eq!(file.line_col(14), (3, 1)); // Start of line 3
    }

    #[test]
    fn test_get_line() {
        let source = "line 1\nline 2\nline 3";
        let file = SourceFile::new(0, PathBuf::from("test.beancount"), source.to_string());

        assert_eq!(file.line(1), Some("line 1"));
        assert_eq!(file.line(2), Some("line 2"));
        assert_eq!(file.line(3), Some("line 3"));
        assert_eq!(file.line(0), None);
        assert_eq!(file.line(4), None);
    }

    #[test]
    fn test_source_map() {
        let mut sm = SourceMap::new();
        let id = sm.add_file(PathBuf::from("test.beancount"), "content".to_string());

        assert_eq!(id, 0);
        assert!(sm.get(0).is_some());
        assert!(sm.get(1).is_none());
    }
}
