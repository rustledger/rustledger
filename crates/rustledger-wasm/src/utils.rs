//! Utility functions for WASM bindings.

/// Line number lookup table for converting byte offsets to line numbers.
pub struct LineLookup {
    line_starts: Vec<usize>,
}

impl LineLookup {
    /// Create a new line lookup from source text.
    #[must_use]
    pub fn new(source: &str) -> Self {
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(source.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        Self { line_starts }
    }

    /// Convert a byte offset to a 1-based line number.
    #[must_use]
    pub fn byte_to_line(&self, byte: usize) -> u32 {
        self.line_starts.partition_point(|&start| start <= byte) as u32
    }

    /// Convert a byte offset to a 1-based `(line, column)`. The column is the
    /// byte offset within the line + 1 — equal to the character column for
    /// ASCII text; on lines with multi-byte UTF-8 it may read higher (we don't
    /// retain the source here to count characters). Lines are exact.
    #[must_use]
    pub fn byte_to_line_col(&self, byte: usize) -> (u32, u32) {
        let line = self
            .line_starts
            .partition_point(|&start| start <= byte)
            .max(1);
        let line_start = self.line_starts.get(line - 1).copied().unwrap_or(0);
        (line as u32, (byte.saturating_sub(line_start) as u32) + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_to_line_simple() {
        let source = "line1\nline2\nline3\n";
        let lookup = LineLookup::new(source);

        // Line 1: bytes 0-5 (l,i,n,e,1,\n)
        assert_eq!(lookup.byte_to_line(0), 1);
        assert_eq!(lookup.byte_to_line(4), 1);
        assert_eq!(lookup.byte_to_line(5), 1);

        // Line 2: bytes 6-11
        assert_eq!(lookup.byte_to_line(6), 2);
        assert_eq!(lookup.byte_to_line(10), 2);

        // Line 3: bytes 12-17
        assert_eq!(lookup.byte_to_line(12), 3);
    }

    #[test]
    fn test_byte_to_line_empty() {
        let lookup = LineLookup::new("");
        assert_eq!(lookup.byte_to_line(0), 1);
    }

    #[test]
    fn test_byte_to_line_col() {
        let source = "ab\ncde\n"; // line1="ab"(0,1,\n@2), line2="cde"(3,4,5,\n@6), len=7
        let lookup = LineLookup::new(source);
        assert_eq!(lookup.byte_to_line_col(0), (1, 1)); // 'a'
        assert_eq!(lookup.byte_to_line_col(1), (1, 2)); // 'b'
        assert_eq!(lookup.byte_to_line_col(2), (1, 3)); // '\n' (col past 'b')
        assert_eq!(lookup.byte_to_line_col(3), (2, 1)); // 'c' (start of line 2)
        assert_eq!(lookup.byte_to_line_col(5), (2, 3)); // 'e'
        // End-of-file on a trailing newline maps to the next (empty) line, col 1
        // — this matches the CLI's `byte_offset_to_line_col` for an end-exclusive
        // span boundary at EOF (both walk past the final '\n').
        assert_eq!(lookup.byte_to_line_col(7), (3, 1));
        // Empty source: offset 0 is (1, 1).
        assert_eq!(LineLookup::new("").byte_to_line_col(0), (1, 1));
    }

    #[test]
    fn test_byte_to_line_no_trailing_newline() {
        let source = "line1\nline2";
        let lookup = LineLookup::new(source);

        assert_eq!(lookup.byte_to_line(0), 1);
        assert_eq!(lookup.byte_to_line(6), 2);
        assert_eq!(lookup.byte_to_line(10), 2);
    }
}
