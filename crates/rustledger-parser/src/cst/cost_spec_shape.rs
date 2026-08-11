//! Cost-spec component-shape validation (#2008 cases 1 and 2).
//!
//! beancount's cost spec is a comma-separated component list:
//!
//! ```text
//! cost_comp_list  : cost_comp | cost_comp_list COMMA cost_comp
//! cost_comp       : compound_amount | DATE | STRING | ASTERISK
//! compound_amount : number_expr? (HASH number_expr?)? CURRENCY
//! ```
//!
//! Two things follow that our lossless, error-recovering parser did not
//! enforce, so both loaded silently here and fail in beancount:
//!
//! - **An empty component** — `{, 100.0 USD, , }`. beancount: `syntax error,
//!   unexpected COMMA, expecting HASH or CAPITAL or CURRENCY`.
//! - **Trailing junk after a complete component** — `{45.23 USD / 2015-07-16
//!   / "blabla"}`. beancount: `syntax error, unexpected SLASH, expecting RCURL
//!   or COMMA`.
//!
//! # Why this is not "SLASH is illegal in a cost spec"
//!
//! `number_expr` is arithmetic, and `/` is one of its operators — `{10.00 * 3
//! USD}` is valid and archives 30.00 (#1939/#1942). The defect in case 2 is
//! **positional**: `CURRENCY` completes a `compound_amount`, so after it only
//! `COMMA` or `}` may follow. beancount's own message says exactly that
//! ("expecting RCURL or COMMA"), not that the token is banned. A rule phrased
//! as "reject SLASH" would have passed the two #2008 fixtures and broken every
//! ledger that divides in a cost spec.
//!
//! Unlike [`super::txn_header`], this needs no green mirror. It is called from
//! inside `convert::extract_unclosed_cost_brace_errors`' existing `COST_SPEC`
//! walk — one pass, not a second one alongside it — and that walk runs for
//! BOTH paths because it sits outside the `use_green` branch. So there is one
//! walker and nothing to drift. The rule is still expressed over
//! `(SyntaxKind, Range<usize>)` so it stays testable without a tree.

use crate::SyntaxKind;

/// What is wrong with a cost spec's component list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CostSpecDefect {
    /// A comma-delimited component with nothing in it.
    EmptyComponent,
    /// A token after the `CURRENCY` that completed a component.
    TrailingJunk,
}

const fn is_cost_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::WHITESPACE
            | SyntaxKind::NEWLINE
            | SyntaxKind::COMMENT
            | SyntaxKind::PERCENT_COMMENT
            | SyntaxKind::SHEBANG
            | SyntaxKind::EMACS_DIRECTIVE
    )
}

/// The first shape defect in a cost spec, if any.
///
/// `tokens` is the `COST_SPEC` token run **including** its braces; the braces are
/// skipped here so callers can hand over the node's children unchanged.
///
/// Reports at most one defect, like [`super::txn_header::first_header_defect`]
/// and for the same reason: beancount stops at the first, and a malformed spec
/// otherwise cascades.
/// Generic over the payload carried alongside each kind so the rule has ONE
/// implementation with two uses: the diagnostic path passes byte ranges and
/// gets the offending one back, while `convert::cost_spec_from_tokens` passes
/// `()` and only asks whether the spec is malformed at all (#2008). A separate
/// kind-only predicate would be the same rule written twice, which is the
/// drift this module was created to avoid.
pub(super) fn first_cost_spec_defect<P, I>(tokens: I) -> Option<(CostSpecDefect, P)>
where
    I: IntoIterator<Item = (SyntaxKind, P)>,
{
    // `{}` is a valid, meaningful empty cost spec ("infer the lot"), so
    // emptiness is only a defect once a COMMA has claimed there are multiple
    // components. Tracked by counting commas rather than by a "first
    // component" special case, which is the shape that gets this wrong: the
    // leading `{,` and the trailing `,}` are both empty components too.
    let mut saw_comma = false;
    let mut component_has_content = false;
    // Flags, not payloads: nothing reads these back, and keeping them
    // payload-free is what lets the rule stay generic over `P`.
    let mut component_complete = false;
    let mut pending_empty = false;

    for (kind, range) in tokens {
        // Every opener form: `{`, `{{` (total cost) and `{#`.
        if is_cost_trivia(kind)
            || matches!(
                kind,
                SyntaxKind::L_BRACE | SyntaxKind::L_DOUBLE_BRACE | SyntaxKind::L_BRACE_HASH
            )
        {
            continue;
        }
        match kind {
            // `}}` closes a `{{total}}` spec. Omitting it here cost 42 false
            // positives across the corpus - every `{{...}}` in the sweep read
            // as junk after a complete component. The opener/closer set has to
            // cover all three forms or the rule fires on valid total-cost
            // syntax, which is common in real ledgers.
            SyntaxKind::COMMA | SyntaxKind::R_BRACE | SyntaxKind::R_DOUBLE_BRACE => {
                let closing = kind != SyntaxKind::COMMA;
                if !closing {
                    saw_comma = true;
                }
                if !component_has_content && (saw_comma || pending_empty) {
                    // Report at the delimiter, as beancount does ("unexpected
                    // COMMA"). For `{}` this is unreachable: no comma is seen,
                    // and `pending_empty` is still None.
                    return Some((CostSpecDefect::EmptyComponent, range));
                }
                if closing {
                    return None;
                }
                pending_empty = true;
                component_has_content = false;
                component_complete = false;
            }
            // CURRENCY completes a `compound_amount`; DATE and STRING are
            // whole components on their own.
            //
            // `*` is deliberately NOT here even though `cost_comp : ASTERISK`
            // makes it a component: `*` is also `number_expr`'s multiplication
            // operator, so `{10.00 * 3 USD}` would be read as a complete `*`
            // component followed by junk. Treating it as ordinary content
            // costs only `{* 100 USD}` (missing comma), which is outside
            // #2008's evidence and not worth guessing at.
            SyntaxKind::CURRENCY | SyntaxKind::DATE | SyntaxKind::STRING => {
                if component_complete {
                    return Some((CostSpecDefect::TrailingJunk, range));
                }
                component_has_content = true;
                component_complete = true;
            }
            _ => {
                if component_complete {
                    return Some((CostSpecDefect::TrailingJunk, range));
                }
                component_has_content = true;
            }
        }
    }
    None
}

/// Diagnostic text. `text` is the source slice of the reported range; built
/// here so the two walkers cannot word the same defect differently.
pub(super) fn cost_defect_message(defect: CostSpecDefect, text: &str) -> String {
    match defect {
        CostSpecDefect::EmptyComponent => format!(
            "empty cost-spec component before {text:?}: \
             each comma-separated component needs a number, currency, date, \
             string or `*`"
        ),
        // "the closing brace", not a literal `}`: a `{{total}}` spec closes
        // with `}}`, and naming the wrong one in a message about malformed
        // syntax is exactly the kind of misdirection #2008 is about.
        CostSpecDefect::TrailingJunk => format!(
            "unexpected {text:?} in cost spec: the component is already \
             complete, so only `,` or the closing brace may follow"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use SyntaxKind as K;
    use std::ops::Range;

    fn toks(items: &[(K, &str)]) -> Vec<(K, Range<usize>)> {
        let mut at = 0usize;
        items
            .iter()
            .map(|(k, t)| {
                let r = at..at + t.len();
                at = r.end;
                (*k, r)
            })
            .collect()
    }
    const WS: (K, &str) = (K::WHITESPACE, " ");
    const LB: (K, &str) = (K::L_BRACE, "{");
    const RB: (K, &str) = (K::R_BRACE, "}");

    #[test]
    fn empty_cost_spec_is_valid() {
        assert_eq!(first_cost_spec_defect(toks(&[LB, RB])), None);
        assert_eq!(first_cost_spec_defect(toks(&[LB, WS, RB])), None);
    }

    #[test]
    fn ordinary_specs_are_valid() {
        // {100.0 USD}
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "100.0"),
                WS,
                (K::CURRENCY, "USD"),
                RB
            ])),
            None
        );
        // {100.0 USD, 2015-01-01}
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "100.0"),
                WS,
                (K::CURRENCY, "USD"),
                (K::COMMA, ","),
                WS,
                (K::DATE, "2015-01-01"),
                RB
            ])),
            None
        );
        // {100.0 USD, "lot-label", *}
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "100.0"),
                WS,
                (K::CURRENCY, "USD"),
                (K::COMMA, ","),
                (K::STRING, "\"lot\""),
                (K::COMMA, ","),
                (K::STAR, "*"),
                RB
            ])),
            None
        );
        // { # 500.00 USD } — total-cost marker
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                WS,
                (K::HASH, "#"),
                WS,
                (K::NUMBER, "500.00"),
                WS,
                (K::CURRENCY, "USD"),
                RB
            ])),
            None
        );
    }

    /// The rule must not become "SLASH is illegal": `/` is a `number_expr`
    /// operator and dividing in a cost spec is valid (#1939/#1942).
    #[test]
    fn arithmetic_inside_a_component_is_valid() {
        for op in [
            (K::STAR, "*"),
            (K::SLASH, "/"),
            (K::PLUS, "+"),
            (K::MINUS, "-"),
        ] {
            assert_eq!(
                first_cost_spec_defect(toks(&[
                    LB,
                    (K::NUMBER, "10.00"),
                    WS,
                    op,
                    WS,
                    (K::NUMBER, "3"),
                    WS,
                    (K::CURRENCY, "USD"),
                    RB
                ])),
                None,
                "arithmetic operator {op:?} must be allowed before the currency"
            );
        }
    }

    /// #2008 case 1 — `{, 100.0 USD, , }`.
    #[test]
    fn empty_components_are_rejected() {
        // leading `{,`
        let leading = toks(&[
            LB,
            (K::COMMA, ","),
            WS,
            (K::NUMBER, "100.0"),
            WS,
            (K::CURRENCY, "USD"),
            RB,
        ]);
        assert_eq!(
            first_cost_spec_defect(leading.clone()).map(|(d, _)| d),
            Some(CostSpecDefect::EmptyComponent)
        );
        // reported AT the comma, as beancount does
        assert_eq!(first_cost_spec_defect(leading).map(|(_, r)| r), Some(1..2));
        // consecutive `,,`
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "1"),
                WS,
                (K::CURRENCY, "USD"),
                (K::COMMA, ","),
                (K::COMMA, ","),
                RB
            ]))
            .map(|(d, _)| d),
            Some(CostSpecDefect::EmptyComponent)
        );
        // trailing `,}`
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "1"),
                WS,
                (K::CURRENCY, "USD"),
                (K::COMMA, ","),
                WS,
                RB
            ]))
            .map(|(d, _)| d),
            Some(CostSpecDefect::EmptyComponent)
        );
    }

    /// #2008 case 2 — `{45.23 USD / 2015-07-16 / "blabla"}`.
    #[test]
    fn junk_after_a_complete_component_is_rejected() {
        let stream = toks(&[
            LB,
            (K::NUMBER, "45.23"),
            WS,
            (K::CURRENCY, "USD"),
            WS,
            (K::SLASH, "/"),
            WS,
            (K::DATE, "2015-07-16"),
            WS,
            (K::SLASH, "/"),
            WS,
            (K::STRING, "\"blabla\""),
            RB,
        ]);
        // The `/` right after `USD` — beancount reports there too.
        let expected = stream[5].1.clone();
        let (defect, range) = first_cost_spec_defect(stream).expect("junk must be reported");
        assert_eq!(defect, CostSpecDefect::TrailingJunk);
        assert_eq!(range, expected);
    }

    /// A second currency in one component is junk as well.
    #[test]
    fn two_currencies_in_one_component_are_rejected() {
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                (K::NUMBER, "2"),
                WS,
                (K::CURRENCY, "AAPL"),
                WS,
                (K::CURRENCY, "USD"),
                RB
            ]))
            .map(|(d, _)| d),
            Some(CostSpecDefect::TrailingJunk)
        );
    }

    /// The `{{total}}` form. Omitting `}}` from the closer set produced 42
    /// false positives across the 731-file corpus - every real total-cost
    /// spec - so this is pinned rather than left to the sweep.
    #[test]
    fn double_brace_total_cost_is_valid() {
        const LLB: (K, &str) = (K::L_DOUBLE_BRACE, "{{");
        const RRB: (K, &str) = (K::R_DOUBLE_BRACE, "}}");
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LLB,
                (K::NUMBER, "500.00"),
                WS,
                (K::CURRENCY, "USD"),
                RRB
            ])),
            None
        );
        // with a lot date, and the `{#` opener form
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LLB,
                (K::NUMBER, "500.00"),
                WS,
                (K::CURRENCY, "USD"),
                (K::COMMA, ","),
                WS,
                (K::DATE, "2015-01-01"),
                RRB
            ])),
            None
        );
        assert_eq!(
            first_cost_spec_defect(toks(&[
                (K::L_BRACE_HASH, "{#"),
                WS,
                (K::NUMBER, "500.00"),
                WS,
                (K::CURRENCY, "USD"),
                RB
            ])),
            None
        );
    }

    /// `{USD}` is #2008 case 5 and is deliberately NOT handled here: beancount
    /// rejects it from the booker ("Too many missing numbers for currency
    /// group"), which is a per-currency-group judgment this rule cannot make
    /// from one spec's tokens. It must stay clean so the split is explicit.
    #[test]
    fn currency_only_is_left_to_the_booker() {
        assert_eq!(
            first_cost_spec_defect(toks(&[LB, (K::CURRENCY, "USD"), RB])),
            None
        );
        assert_eq!(
            first_cost_spec_defect(toks(&[
                LB,
                WS,
                (K::HASH, "#"),
                WS,
                (K::CURRENCY, "USD"),
                RB
            ])),
            None
        );
    }
}
