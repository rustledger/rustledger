//! Cross-file `InternedStr` deduplication.
//!
//! Each parsed file has its own per-file [`StringInterner`], so the
//! same string (account name, currency code, tag, link, payee,
//! narration) appearing in two included files lands in two different
//! `Arc<str>` allocations. The [`InternedStr`] `PartialEq` fast path
//! (`Arc::ptr_eq`) then fails on cross-file equality and falls back
//! to byte comparison.
//!
//! This module provides the merge step: walk a slice of directives
//! through a single shared [`StringInterner`] so identical strings
//! share one `Arc`. After this pass, equality checks across the entire
//! directive list hit the pointer-equality fast path.
//!
//! Coverage: every `InternedStr` and `Vec<InternedStr>` field reachable
//! from a `Directive` is re-interned — including `Transaction.payee`,
//! `Transaction.narration`, `Transaction.tags`, `Transaction.links`,
//! and `Document.tags` / `Document.links`. (Earlier versions of this
//! pass only covered posting-level `account` / `currency` fields;
//! Copilot review on PR #1081 expanded the walk.)
//!
//! The dedup walk is feature-independent (no `cache` / `rkyv`
//! dependency) so it can run on every load path, not just cache hits.
//! [`Loader::load`](crate::Loader::load) invokes it automatically; the
//! cache-hit path in `rustledger`'s `check` command and the WASM
//! parsed-ledger constructor call it explicitly.

use rustledger_core::Directive;
use rustledger_core::intern::{InternedStr, StringInterner};
use rustledger_core::{IncompleteAmount, PriceAnnotation};
use rustledger_parser::Spanned;

/// Re-intern all strings in directives to deduplicate memory.
///
/// Walks through all directives and re-interns account names and
/// currencies using a shared [`StringInterner`], so identical strings
/// share a single `Arc<str>` allocation. Returns the number of strings
/// that were deduplicated (i.e., strings that were found to already
/// exist in the interner).
pub fn reintern_directives(directives: &mut [Spanned<Directive>]) -> usize {
    let mut interner = StringInterner::with_capacity(1024);
    let mut dedup_count = 0;
    for spanned in directives.iter_mut() {
        dedup_count += reintern_directive(&mut spanned.value, &mut interner);
    }
    dedup_count
}

/// Re-intern strings in a slice of plain directives (without `Spanned` wrapper).
///
/// Used by WASM caching where `Spanned<Directive>` is not present.
pub fn reintern_plain_directives(directives: &mut [Directive]) -> usize {
    let mut interner = StringInterner::with_capacity(1024);
    let mut dedup_count = 0;
    for directive in directives.iter_mut() {
        dedup_count += reintern_directive(directive, &mut interner);
    }
    dedup_count
}

/// Single-lookup helper used by [`reintern_directive`]. The
/// `intern_with_status` API on [`StringInterner`] does one hash probe
/// and returns both the interned value and a "was it already there?"
/// flag — replacing the earlier `contains` + `intern` double-lookup.
/// Caught by Copilot review on PR #1081. Returns `true` when the
/// string was already present (i.e., this call contributed a dedup
/// hit).
fn do_intern(s: &mut InternedStr, interner: &mut StringInterner) -> bool {
    let (new, was_new) = interner.intern_with_status(s.as_str());
    *s = new;
    !was_new
}

/// Re-intern every entry of a slice of domain-typed identifiers
/// (e.g., [`rustledger_core::Currency`], [`rustledger_core::Account`],
/// [`rustledger_core::Tag`], [`rustledger_core::Link`]), tallying the
/// dedup hits into `dedup_count`. Calls `get_inner` to reach the
/// underlying `InternedStr`. Hoisted to module scope rather than
/// nested inside [`reintern_directive`] so clippy's
/// `items_after_statements` lint stays happy.
fn intern_typed_vec<T>(
    v: &mut [T],
    interner: &mut StringInterner,
    dedup_count: &mut usize,
    get_inner: fn(&mut T) -> &mut InternedStr,
) {
    for s in v.iter_mut() {
        if do_intern(get_inner(s), interner) {
            *dedup_count += 1;
        }
    }
}

/// Re-intern all `InternedStr` fields in a single directive,
/// deduplicating identical strings to share a single `Arc<str>`
/// allocation. Returns the count of strings that were already present
/// in the interner (i.e., this directive's contribution to the
/// dedup-hit total).
fn reintern_directive(directive: &mut Directive, interner: &mut StringInterner) -> usize {
    let mut dedup_count = 0;

    match directive {
        Directive::Transaction(txn) => {
            // Transaction-level InternedStr fields. The pre-Copilot
            // version of this walk skipped these — cross-file payees /
            // narrations / tags / links never hit `Arc::ptr_eq`.
            if let Some(ref mut payee) = txn.payee
                && do_intern(payee, interner)
            {
                dedup_count += 1;
            }
            if do_intern(&mut txn.narration, interner) {
                dedup_count += 1;
            }
            intern_typed_vec(
                &mut txn.tags,
                interner,
                &mut dedup_count,
                rustledger_core::Tag::as_interned_mut,
            );
            intern_typed_vec(
                &mut txn.links,
                interner,
                &mut dedup_count,
                rustledger_core::Link::as_interned_mut,
            );

            for posting in &mut txn.postings {
                if do_intern(posting.account.as_interned_mut(), interner) {
                    dedup_count += 1;
                }
                // Units
                if let Some(ref mut units) = posting.units {
                    match units {
                        IncompleteAmount::Complete(amt) => {
                            if do_intern(amt.currency.as_interned_mut(), interner) {
                                dedup_count += 1;
                            }
                        }
                        IncompleteAmount::CurrencyOnly(cur) => {
                            if do_intern(cur.as_interned_mut(), interner) {
                                dedup_count += 1;
                            }
                        }
                        IncompleteAmount::NumberOnly(_) => {}
                    }
                }
                // Cost spec
                if let Some(ref mut cost) = posting.cost
                    && let Some(ref mut cur) = cost.currency
                    && do_intern(cur.as_interned_mut(), interner)
                {
                    dedup_count += 1;
                }
                // Price annotation
                if let Some(ref mut price) = posting.price {
                    match price {
                        PriceAnnotation::Unit(amt) | PriceAnnotation::Total(amt) => {
                            if do_intern(amt.currency.as_interned_mut(), interner) {
                                dedup_count += 1;
                            }
                        }
                        PriceAnnotation::UnitIncomplete(inc)
                        | PriceAnnotation::TotalIncomplete(inc) => match inc {
                            IncompleteAmount::Complete(amt) => {
                                if do_intern(amt.currency.as_interned_mut(), interner) {
                                    dedup_count += 1;
                                }
                            }
                            IncompleteAmount::CurrencyOnly(cur) => {
                                if do_intern(cur.as_interned_mut(), interner) {
                                    dedup_count += 1;
                                }
                            }
                            IncompleteAmount::NumberOnly(_) => {}
                        },
                        PriceAnnotation::UnitEmpty | PriceAnnotation::TotalEmpty => {}
                    }
                }
            }
        }
        Directive::Balance(bal) => {
            if do_intern(bal.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
            if do_intern(bal.amount.currency.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Open(open) => {
            if do_intern(open.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
            intern_typed_vec(
                &mut open.currencies,
                interner,
                &mut dedup_count,
                rustledger_core::Currency::as_interned_mut,
            );
        }
        Directive::Close(close) => {
            if do_intern(close.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Commodity(comm) => {
            if do_intern(comm.currency.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Pad(pad) => {
            if do_intern(pad.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
            if do_intern(pad.source_account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Note(note) => {
            if do_intern(note.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Document(doc) => {
            if do_intern(doc.account.as_interned_mut(), interner) {
                dedup_count += 1;
            }
            // Pre-Copilot this skipped tags/links. They're now covered.
            intern_typed_vec(
                &mut doc.tags,
                interner,
                &mut dedup_count,
                rustledger_core::Tag::as_interned_mut,
            );
            intern_typed_vec(
                &mut doc.links,
                interner,
                &mut dedup_count,
                rustledger_core::Link::as_interned_mut,
            );
        }
        Directive::Price(price) => {
            if do_intern(price.currency.as_interned_mut(), interner) {
                dedup_count += 1;
            }
            if do_intern(price.amount.currency.as_interned_mut(), interner) {
                dedup_count += 1;
            }
        }
        Directive::Event(_) | Directive::Query(_) | Directive::Custom(_) => {
            // These don't contain InternedStr fields
        }
    }

    dedup_count
}
