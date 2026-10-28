//! Pins the memory footprint of the directive payloads.
//!
//! The loader keeps several `Vec<Spanned<Directive>>` alive at once (the
//! parse result, the booked stream, the plugin round-trip), so every byte
//! on these types is multiplied by millions of directives and megabytes
//! of peak RSS. That is the whole argument for keeping rare data
//! (metadata maps, comment lists, cost specs) behind `Option<Box<..>>`
//! instead of inline (`MetaMap`/`CommentList`, `Posting::cost`).
//!
//! These are upper bounds, not exact sizes: a future shrink passes, a
//! regression (a new inline field on a hot type) fails. The companion
//! `spans_stay_narrow` bounds keep `Spanned<T>` honest the same way.

use rustledger_core::directive::*;
use rustledger_core::span::*;
use std::mem::size_of;

#[test]
fn directive_payloads_stay_compact() {
    assert!(
        size_of::<Posting>() <= 104,
        "Posting grew to {} bytes; per-txn posting heaps pay this twice per \
         transaction. Box rare fields instead (see `MetaMap`/`CommentList` \
         for the pattern)",
        size_of::<Posting>()
    );
    assert!(
        size_of::<Spanned<Posting>>() <= 128,
        "Spanned<Posting> grew to {} bytes",
        size_of::<Spanned<Posting>>()
    );
    assert!(
        size_of::<Transaction>() <= 128,
        "Transaction grew to {} bytes",
        size_of::<Transaction>()
    );
    assert!(
        size_of::<Directive>() <= 136,
        "Directive grew to {} bytes; its size is the MAX variant, so one \
         fat variant inflates every directive in the ledger",
        size_of::<Directive>()
    );
    assert!(
        size_of::<Spanned<Directive>>() <= 160,
        "Spanned<Directive> grew to {} bytes; the loader copies millions of \
         these",
        size_of::<Spanned<Directive>>()
    );
}

#[test]
fn rare_collections_stay_boxed() {
    assert!(
        size_of::<MetaMap>() <= 8,
        "MetaMap grew to {} bytes; it must stay a niche-optimized \
         Option<Box<..>>",
        size_of::<MetaMap>()
    );
    assert!(
        size_of::<CommentList>() <= 8,
        "CommentList grew to {} bytes; it must stay a niche-optimized \
         Option<Box<..>>",
        size_of::<CommentList>()
    );
}

#[test]
fn spans_stay_narrow() {
    assert_eq!(size_of::<Span>(), 16, "Span is two usizes by construction");
    assert!(
        size_of::<Spanned<()>>() <= 24,
        "Spanned<()> grew to {} bytes",
        size_of::<Spanned<()>>()
    );
}
