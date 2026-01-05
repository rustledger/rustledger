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
    fn test_byte_to_line_no_trailing_newline() {
        let source = "line1\nline2";
        let lookup = LineLookup::new(source);

        assert_eq!(lookup.byte_to_line(0), 1);
        assert_eq!(lookup.byte_to_line(6), 2);
        assert_eq!(lookup.byte_to_line(10), 2);
    }
}
