//! Source location tracking.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::Range;

/// A span in the source code, represented as a byte range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
}

impl Span {
    /// Create a new span.
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Create a span from a range.
    #[must_use]
    pub const fn from_range(range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }

    /// Get the length of this span in bytes.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check if the span is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Merge this span with another, returning a span that covers both.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Get the source text for this span.
    #[must_use]
    pub fn text<'a>(&self, source: &'a str) -> &'a str {
        &source[self.start..self.end]
    }

    /// Convert to a chumsky span.
    #[must_use]
    pub const fn into_range(self) -> Range<usize> {
        self.start..self.end
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::from_range(range)
    }
}

impl From<Span> for Range<usize> {
    fn from(span: Span) -> Self {
        span.start..span.end
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}


/// A value with an associated source span.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Spanned<T> {
    /// The value.
    pub value: T,
    /// The source span.
    pub span: Span,
}

impl<T> Spanned<T> {
    /// Create a new spanned value.
    #[must_use]
    pub const fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }

    /// Map the inner value.
    #[must_use]
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            value: f(self.value),
            span: self.span,
        }
    }

    /// Get a reference to the inner value.
    #[must_use]
    pub const fn inner(&self) -> &T {
        &self.value
    }

    /// Unwrap the spanned value, discarding the span.
    #[must_use]
    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T: fmt::Display> fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
