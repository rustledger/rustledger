//! Source location tracking.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::Range;

/// A span in the source code, represented as a byte range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
}

impl Span {
    /// The zero span (`0..0`). Used as the location for programmatically
    /// synthesized values that have no source representation. Pair with
    /// [`SYNTHESIZED_FILE_ID`] on the containing [`Spanned`] to make the
    /// "no source" intent unambiguous.
    ///
    /// ```
    /// use rustledger_core::Span;
    /// assert_eq!(Span::ZERO, Span::new(0, 0));
    /// assert!(Span::ZERO.is_empty());
    /// ```
    pub const ZERO: Self = Self { start: 0, end: 0 };

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

    /// Convert to a byte-offset `Range<usize>` for downstream span consumers.
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

/// Sentinel `file_id` indicating a directive was synthesized by a plugin
/// rather than parsed from a source file.
///
/// Regular source files get sequential IDs starting at 0 (see
/// `rustledger_loader::SourceMap::add_file`), so this sentinel is safely out
/// of the normal range. Code that formats error locations or looks up files
/// in a `SourceMap` should treat this as "no source location" and, where
/// appropriate, hint to the user that a plugin generated the directive.
///
/// See issue #896.
pub const SYNTHESIZED_FILE_ID: u16 = u16::MAX;

/// A value with an associated source location (span and file).
///
/// `PartialEq` / `Eq` / `Hash` are implemented manually to delegate to
/// the inner value only — two `Spanned<T>` values are considered equal
/// when their `T`s are equal, regardless of where they came from in
/// source. This matches the principle that "what" a value is should
/// not depend on where it lives. Consumers that genuinely need
/// location-sensitive equality compare `.span` and `.file_id`
/// explicitly.
///
/// Note: the rkyv-archived form (`ArchivedSpanned<T>`, present under the
/// `rkyv` feature) does **not** automatically receive `PartialEq` /
/// `Eq`. The host doesn't compare archived values today; if a future
/// code path needs to, add `rkyv(compare = (PartialEq))` to the derive
/// attribute below or hand-roll a manual impl on the archived type.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Spanned<T> {
    /// The value.
    pub value: T,
    /// The source span (byte offsets within the file).
    pub span: Span,
    /// The source file ID (index into `SourceMap`).
    /// Uses `u16` to minimize struct size (max 65,535 files).
    pub file_id: u16,
}

impl<T> Spanned<T> {
    /// Create a new spanned value with `file_id` defaulting to 0.
    ///
    /// Use `with_file_id` to set the correct file ID after creation.
    #[must_use]
    pub const fn new(value: T, span: Span) -> Self {
        Self {
            value,
            span,
            file_id: 0,
        }
    }

    /// Wrap a value that was programmatically synthesized (no source
    /// representation). Uses [`Span::ZERO`] and [`SYNTHESIZED_FILE_ID`]
    /// so downstream consumers can detect "no source" without sentinel
    /// checks on the inner value's fields.
    ///
    /// Used by plugin-synthesized AST nodes, test fixtures, CLI commands
    /// that build directives in-memory, and any other producer that does
    /// not parse from source bytes.
    #[must_use]
    pub const fn synthesized(value: T) -> Self {
        Self {
            value,
            span: Span::ZERO,
            file_id: SYNTHESIZED_FILE_ID,
        }
    }

    /// Set the file ID for this spanned value.
    ///
    /// Accepts `usize` for API convenience but stores as `u16` internally.
    ///
    /// # Panics
    ///
    /// Debug builds will panic if `file_id` exceeds `u16::MAX` (65,535).
    #[must_use]
    pub fn with_file_id(mut self, file_id: usize) -> Self {
        debug_assert!(
            u16::try_from(file_id).is_ok(),
            "file_id {} exceeds u16::MAX; at most {} files are supported",
            file_id,
            u16::MAX
        );
        self.file_id = file_id as u16;
        self
    }

    /// Map the inner value, preserving span and `file_id`.
    #[must_use]
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            value: f(self.value),
            span: self.span,
            file_id: self.file_id,
        }
    }

    /// Get a reference to the inner value.
    #[must_use]
    pub const fn inner(&self) -> &T {
        &self.value
    }

    /// Unwrap the spanned value, discarding the span and `file_id`.
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

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for Spanned<T> {}

impl<T: std::hash::Hash> std::hash::Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

/// `Spanned<T>` is a transparent wrapper that adds source location to a
/// value. Following the convention used by other transparent wrappers in
/// the standard library (`Box<T>`, `Rc<T>`, `Cow<'_, T>`, `MutexGuard<T>`),
/// it implements `Deref` so callers can read inner fields and call inner
/// methods without spelling `.value` everywhere. Consumers that genuinely
/// need to inspect the source location reach for `.span`, `.file_id`, or
/// `.value` (for ownership) explicitly.
impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_new() {
        let span = Span::new(10, 20);
        assert_eq!(span.start, 10);
        assert_eq!(span.end, 20);
    }

    #[test]
    fn test_span_from_range() {
        let span = Span::from_range(5..15);
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 15);
    }

    #[test]
    fn test_span_len() {
        let span = Span::new(10, 25);
        assert_eq!(span.len(), 15);
    }

    #[test]
    fn test_span_is_empty() {
        let empty = Span::new(5, 5);
        let non_empty = Span::new(5, 10);
        assert!(empty.is_empty());
        assert!(!non_empty.is_empty());
    }

    #[test]
    fn test_span_merge() {
        let a = Span::new(10, 20);
        let b = Span::new(15, 30);
        let merged = a.merge(&b);
        assert_eq!(merged.start, 10);
        assert_eq!(merged.end, 30);

        // Test with non-overlapping spans
        let c = Span::new(5, 8);
        let merged2 = a.merge(&c);
        assert_eq!(merged2.start, 5);
        assert_eq!(merged2.end, 20);
    }

    #[test]
    fn test_span_text() {
        let source = "hello world";
        let span = Span::new(0, 5);
        assert_eq!(span.text(source), "hello");

        let span2 = Span::new(6, 11);
        assert_eq!(span2.text(source), "world");
    }

    #[test]
    fn test_span_into_range() {
        let span = Span::new(3, 7);
        let range: Range<usize> = span.into_range();
        assert_eq!(range, 3..7);
    }

    #[test]
    fn test_span_from_impl() {
        let span: Span = (5..10).into();
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 10);
    }

    #[test]
    fn test_range_from_span() {
        let span = Span::new(2, 8);
        let range: Range<usize> = span.into();
        assert_eq!(range, 2..8);
    }

    #[test]
    fn test_span_display() {
        let span = Span::new(10, 20);
        assert_eq!(format!("{span}"), "10..20");
    }

    #[test]
    fn test_spanned_new() {
        let spanned = Spanned::new("value", Span::new(0, 5));
        assert_eq!(spanned.value, "value");
        assert_eq!(spanned.span, Span::new(0, 5));
    }

    #[test]
    fn test_spanned_map() {
        let spanned = Spanned::new(5, Span::new(0, 1));
        let mapped = spanned.map(|x| x * 2);
        assert_eq!(mapped.value, 10);
        assert_eq!(mapped.span, Span::new(0, 1));
    }

    #[test]
    fn test_spanned_inner() {
        let spanned = Spanned::new("test", Span::new(0, 4));
        assert_eq!(spanned.inner(), &"test");
    }

    #[test]
    fn test_spanned_into_inner() {
        let spanned = Spanned::new(String::from("owned"), Span::new(0, 5));
        let inner = spanned.into_inner();
        assert_eq!(inner, "owned");
    }

    #[test]
    fn test_spanned_display() {
        let spanned = Spanned::new(42, Span::new(0, 2));
        assert_eq!(format!("{spanned}"), "42");
    }

    #[test]
    fn test_spanned_with_file_id() {
        let spanned = Spanned::new("value", Span::new(0, 5)).with_file_id(3);
        assert_eq!(spanned.value, "value");
        assert_eq!(spanned.span, Span::new(0, 5));
        assert_eq!(spanned.file_id, 3);
    }

    #[test]
    fn test_spanned_eq_ignores_location() {
        // PartialEq/Eq/Hash on Spanned<T> delegate to the inner value:
        // two values with the same content but different source
        // locations are equal. Anyone who needs location-sensitive
        // equality compares .span / .file_id explicitly.
        use std::collections::HashSet;
        let a = Spanned::new("x", Span::new(0, 1)).with_file_id(0);
        let b = Spanned::new("x", Span::new(100, 200)).with_file_id(7);
        let c = Spanned::new("y", Span::new(0, 1)).with_file_id(0);
        assert_eq!(a, b, "different locations, same value → equal");
        assert_ne!(a, c, "same location, different value → not equal");
        let mut set: HashSet<Spanned<&str>> = HashSet::new();
        set.insert(a);
        set.insert(b);
        assert_eq!(set.len(), 1, "Hash also delegates to inner value");
    }

    #[test]
    fn test_span_zero_constant() {
        assert_eq!(Span::ZERO, Span::new(0, 0));
        assert!(Span::ZERO.is_empty());
    }

    #[test]
    fn test_spanned_synthesized_uses_synth_file_id_and_zero_span() {
        // Programmatically-built values get Span::ZERO + SYNTHESIZED_FILE_ID
        // so consumers can detect "no source" without sentinel checks on
        // the inner value.
        let s = Spanned::synthesized("anything");
        assert_eq!(s.span, Span::ZERO);
        assert_eq!(s.file_id, SYNTHESIZED_FILE_ID);
    }
}
