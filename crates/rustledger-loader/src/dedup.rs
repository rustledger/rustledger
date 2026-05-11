//! Cross-file `InternedStr` deduplication.
//!
//! Each parsed file has its own per-file [`StringInterner`], so the
//! same account / currency / tag string appearing in two included
//! files lands in two different `Arc<str>` allocations. The
//! [`InternedStr`] `PartialEq` fast path (`Arc::ptr_eq`) then fails on
//! cross-file equality and falls back to byte comparison.
//!
//! This module provides the merge step: walk a slice of directives
//! through a single shared [`StringInterner`] so identical strings
//! share one `Arc`. After this pass, equality checks across the entire
//! directive list hit the pointer-equality fast path.
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

/// Re-intern all `InternedStr` fields in a single directive, deduplicating
/// identical strings to share a single `Arc<str>` allocation.
fn reintern_directive(directive: &mut Directive, interner: &mut StringInterner) -> usize {
    fn do_intern(s: &mut InternedStr, interner: &mut StringInterner) -> bool {
        let already_exists = interner.contains(s.as_str());
        *s = interner.intern(s.as_str());
        already_exists
    }

    let mut dedup_count = 0;

    match directive {
        Directive::Transaction(txn) => {
            for posting in &mut txn.postings {
                if do_intern(&mut posting.account, interner) {
                    dedup_count += 1;
                }
                // Units
                if let Some(ref mut units) = posting.units {
                    match units {
                        IncompleteAmount::Complete(amt) => {
                            if do_intern(&mut amt.currency, interner) {
                                dedup_count += 1;
                            }
                        }
                        IncompleteAmount::CurrencyOnly(cur) => {
                            if do_intern(cur, interner) {
                                dedup_count += 1;
                            }
                        }
                        IncompleteAmount::NumberOnly(_) => {}
                    }
                }
                // Cost spec
                if let Some(ref mut cost) = posting.cost
                    && let Some(ref mut cur) = cost.currency
                    && do_intern(cur, interner)
                {
                    dedup_count += 1;
                }
                // Price annotation
                if let Some(ref mut price) = posting.price {
                    match price {
                        PriceAnnotation::Unit(amt) | PriceAnnotation::Total(amt) => {
                            if do_intern(&mut amt.currency, interner) {
                                dedup_count += 1;
                            }
                        }
                        PriceAnnotation::UnitIncomplete(inc)
                        | PriceAnnotation::TotalIncomplete(inc) => match inc {
                            IncompleteAmount::Complete(amt) => {
                                if do_intern(&mut amt.currency, interner) {
                                    dedup_count += 1;
                                }
                            }
                            IncompleteAmount::CurrencyOnly(cur) => {
                                if do_intern(cur, interner) {
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
            if do_intern(&mut bal.account, interner) {
                dedup_count += 1;
            }
            if do_intern(&mut bal.amount.currency, interner) {
                dedup_count += 1;
            }
        }
        Directive::Open(open) => {
            if do_intern(&mut open.account, interner) {
                dedup_count += 1;
            }
            for cur in &mut open.currencies {
                if do_intern(cur, interner) {
                    dedup_count += 1;
                }
            }
        }
        Directive::Close(close) => {
            if do_intern(&mut close.account, interner) {
                dedup_count += 1;
            }
        }
        Directive::Commodity(comm) => {
            if do_intern(&mut comm.currency, interner) {
                dedup_count += 1;
            }
        }
        Directive::Pad(pad) => {
            if do_intern(&mut pad.account, interner) {
                dedup_count += 1;
            }
            if do_intern(&mut pad.source_account, interner) {
                dedup_count += 1;
            }
        }
        Directive::Note(note) => {
            if do_intern(&mut note.account, interner) {
                dedup_count += 1;
            }
        }
        Directive::Document(doc) => {
            if do_intern(&mut doc.account, interner) {
                dedup_count += 1;
            }
        }
        Directive::Price(price) => {
            if do_intern(&mut price.currency, interner) {
                dedup_count += 1;
            }
            if do_intern(&mut price.amount.currency, interner) {
                dedup_count += 1;
            }
        }
        Directive::Event(_) | Directive::Query(_) | Directive::Custom(_) => {
            // These don't contain InternedStr fields
        }
    }

    dedup_count
}
