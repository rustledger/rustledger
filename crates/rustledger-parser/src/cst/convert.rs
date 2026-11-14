//! CST -> `ParseResult` converter.
//!
//! [`parse_via_cst`] is the implementation behind the public
//! [`crate::parse`] entry point. It walks the structured CST from
//! [`crate::parse_structured`] via the typed-AST surface in
//! [`crate::cst::ast`] and produces the legacy AST-shaped
//! [`ParseResult`] that downstream consumers (loader, booking,
//! validate, query, LSP) consume.
//!
//! ## Conversion scope
//!
//! Per-directive converters: Open, Close, Commodity, Note,
//! Document, Event, Query, Price, Balance, Pad, Custom, and
//! Transaction (with its full posting / cost-spec / price-
//! annotation / metadata / trailing-comments machinery).
//!
//! State-only directives (Pushtag / Poptag / Pushmeta / Popmeta)
//! mutate `tag_stack` / `meta_stack` inherited by subsequent
//! directives; mismatched-pop and unclosed-at-EOF emit specific
//! `ParseErrorKind` variants. Arithmetic AMOUNT expressions
//! (`120 / 3 USD` ≡ `40 USD`) are evaluated; the same logic
//! powers numeric values in BALANCE and PRICE directives.
//!
//! Field-level extractors populate `ParseResult.options`,
//! `.includes`, `.plugins`, `.comments`, `.currency_occurrences`,
//! `.account_occurrences`.
//!
//! ## Error surfacing
//!
//! A single [`walk_descendants_once`] pass collects standalone
//! comments, currency occurrences, account occurrences, and inline
//! `ERROR_TOKEN` / mid-file-BOM errors. Specialized extractors run alongside for
//! `ERROR_NODE` classification, transaction body errors, unclosed
//! cost braces, indented top-level directives, and bare-currency
//! values in custom directives.

use rust_decimal::Decimal;
use rustledger_core::cost::{CostNumber, CostSpec};
use rustledger_core::directive::{PriceAnnotation, PriceKind};
use rustledger_core::{
    Account, Amount, Currency, Directive, IncompleteAmount, InternedStr, Link, LinkSet, MetaValue,
    Metadata, MetadataBuilder, NaiveDate, Posting, Span, Spanned, Tag, TagSet, naive_date,
};

use crate::ParseResult;
use crate::cst::ast::{
    self, AstNode, AstToken, BalanceDirective, CloseDirective, CommodityDirective, CustomDirective,
    DocumentDirective, EventDirective, IncludeDirective, MetaEntry, NoteDirective, OpenDirective,
    OptionDirective, PadDirective, PluginDirective, PostingFlagKind, PriceDirective,
    QueryDirective, SourceFile, Transaction as AstTransaction, TransactionFlagKind,
};

/// Parse Beancount source via the CST and produce the AST-shaped
/// [`ParseResult`]. This is the implementation behind
/// [`crate::parse`]; the public entry delegates here unconditionally.
///
/// See the module-level rustdoc for the conversion scope.
#[must_use]
pub fn parse_via_cst(source: &str) -> ParseResult {
    parse_via_cst_opts(source, /* collect_occurrences = */ true)
}

/// Like [`parse_via_cst`], but only collects `currency_occurrences` /
/// `account_occurrences` when `collect_occurrences` is true.
///
/// Those two indices are consumed **solely by the LSP** (rename / references /
/// highlight). The loader / CLI processing path never reads them, so passing
/// `false` skips the per-`ACCOUNT`/`CURRENCY` `Account::new` / `Currency::new`
/// construction and the per-token in-`ERROR_NODE` ancestor walk inside
/// `walk_descendants_once` — profiling flagged that walk as the #1
/// allocation-count site. Inline errors and top-level comments are still
/// collected unconditionally (the processing path needs them).
#[must_use]
pub fn parse_via_cst_opts(source: &str, collect_occurrences: bool) -> ParseResult {
    parse_via_cst_inner(source, collect_occurrences, /* use_green = */ true)
}

/// Test/fuzz hook: parse like [`crate::parse`] but force the **red** conversion
/// path (green transaction conversion disabled). Used by the `green_eq_red`
/// differential fuzz target to assert the green-wired path is output-equivalent.
#[doc(hidden)]
#[must_use]
pub fn parse_red_only(source: &str) -> ParseResult {
    parse_via_cst_inner(
        source, /* collect_occurrences = */ true, /* use_green = */ false,
    )
}

fn parse_via_cst_inner(source: &str, collect_occurrences: bool, use_green: bool) -> ParseResult {
    // BOM detection mirrors the legacy parser's behavior: strip a
    // leading 3-byte BOM from the source before tokenizing and
    // record its presence in the result. Spans index the original
    // source frame INCLUDING the BOM offset.
    let (stripped, has_leading_bom) = crate::bom::strip_leading(source);
    let bom_offset: u32 = if has_leading_bom { 3 } else { 0 };

    let source_file = SourceFile::parse(stripped);

    // Count first, allocate once: both vecs grow 1:1 with producing
    // directives, and doubling a `Vec<Spanned<Directive>>` on the way to
    // 2M entries re-copied 2^21 × 192 B of entries (402,653,184 B total,
    // DHAT `profile_pipeline` on `1M.beancount`). The count is a walk of
    // the root's green children (a slice, no allocation, no red nodes),
    // the same pattern `green.rs` uses for `posting_count` (measured
    // 81.0 -> 71.2 ms there). It is an upper bound: the loop below emits
    // only the producing kinds, not the state-only ones (option /
    // include / plugin / push* / pop*).
    let directive_capacity = directive_child_count(&source_file);
    let mut directives: Vec<Spanned<Directive>> = Vec::with_capacity(directive_capacity);
    let mut directive_nodes: Vec<crate::SyntaxNode> = Vec::with_capacity(directive_capacity);
    let mut options: Vec<(String, String, Span)> = Vec::new();
    let mut includes: Vec<(String, Span)> = Vec::new();
    let mut plugins: Vec<(String, Option<String>, Span)> = Vec::new();
    // Single-pass descendants walk that yields inline errors,
    // top-level comments, and currency occurrences (replaces three
    // separate `descendants_with_tokens` walks at 3·O(N) → 1·O(N)).
    let DescendantsWalkResult {
        inline_errors,
        top_level_comments,
        currency_occurrences,
        account_occurrences,
        cost_brace_errors,
        link_meta_errors,
        custom_pushmeta_errors,
    } = if use_green {
        // Green-tree walk (no per-node red allocation); byte-identical to red.
        super::green::walk_descendants(
            source_file.syntax(),
            stripped,
            bom_offset,
            collect_occurrences,
        )
    } else {
        walk_descendants_once(&source_file, bom_offset, collect_occurrences)
    };

    // Fused single pass over the top-level children replaces the
    // five former per-child traversals (error-node, transaction-body,
    // indented-directive, custom-value diagnostics + section-marker
    // comments). See `walk_top_level_once`.
    let TopLevelWalkResult {
        errors: top_level_errors,
        section_marker_comments,
    } = if use_green {
        super::green::walk_top_level(source_file.syntax(), stripped, bom_offset)
    } else {
        walk_top_level_once(&source_file, stripped, bom_offset)
    };

    let mut comments: Vec<Spanned<String>> = top_level_comments;
    comments.extend(section_marker_comments);
    // Merge in source order; the two helpers' classifiers are
    // disjoint today (STAR-first vs COMMENT-kind-first) but
    // dedup-by-start keeps the invariant local.
    comments.sort_by_key(|s| s.span.start);
    comments.dedup_by_key(|s| s.span.start);
    let mut errors = top_level_errors;
    // Three per-node shape rules — unclosed cost braces, links as metadata
    // values, tags/links as custom/pushmeta values — in a FIXED order that
    // both paths below reproduce.
    //
    // Green folds them into `walk_descendants`, which already visits every
    // node, so they cost a `match` per node and nothing else. Red still runs
    // them as three standalone whole-tree `descendants()` scans, each behind a
    // byte-scan guard (`contains('{')` and friends) that skips the scan when
    // the source cannot contain the construct at all.
    //
    // The guards are what made this cost invisible for so long: they are free
    // on a ledger with no '{', '^' or '#', which is exactly the `simple`
    // profiling shape. Real ledgers have tags and cost specs, and there the
    // three red scans measured 7.46% of all instructions on `tagged` and
    // 2.15% on `investment` (cachegrind ablation, 10k txns). Green — the path
    // every caller but the parity test takes — no longer pays any of it.
    //
    // The green path needs no guards: no '{' in the source means the parser
    // built no COST_SPEC node, so the folded rule finds nothing to report.
    if use_green {
        errors.extend(cost_brace_errors);
        errors.extend(link_meta_errors);
        errors.extend(custom_pushmeta_errors);
    } else {
        if stripped.contains('{') {
            errors.extend(extract_unclosed_cost_brace_errors(
                &source_file,
                stripped,
                bom_offset,
            ));
        }
        if stripped.contains('^') {
            errors.extend(extract_link_metadata_value_errors(&source_file, bom_offset));
        }
        if stripped.contains('^') || stripped.contains('#') {
            errors.extend(extract_custom_pushmeta_taglink_errors(
                &source_file,
                bom_offset,
            ));
        }
    }
    errors.extend(
        inline_errors
            .into_iter()
            .map(|e| name_a_currency_tail(e, stripped, bom_offset)),
    );
    let warnings = Vec::new();

    // pushtag/poptag/pushmeta/popmeta state, a stack across directives:
    // transactions, notes and documents inherit the active pushed-tag set
    // (#2544), and only transactions inherit the pushed-meta set, under
    // their own keys (#2812), as in beancount. See `apply_inherited_state`.
    // We pair each entry
    // with the originating directive's span so unclosed-at-EOF
    // diagnostics can point at the offending push.
    let mut tag_stack: Vec<(Tag, Span)> = Vec::new();
    // Vec-of-tuples (NOT a `Metadata` map) so legacy semantics
    // are preserved: `pushmeta x: 1` then `pushmeta x: 2` should
    // shadow (peek returns 2) and `popmeta x` should pop the
    // most recent, leaving x=1 active. A HashMap would have lost
    // the shadowed entry on the second push.
    let mut meta_stack: Vec<(String, MetaValue, Span)> = Vec::new();

    // Starts of the errors the walks above already reported, for the header
    // check below: a header that already has an error is not checked again
    // (one error per problem, as beancount reports the first one on a line).
    let mut prior_error_starts: Vec<usize> = errors.iter().map(|e| e.span.start).collect();
    prior_error_starts.sort_unstable();
    let mut header_tokens = Vec::new();
    // `(error start, header start, grammar failure point)` for each directive
    // the converter dropped with a whole-node error, in order, BOM frame. The
    // node's span takes in leading blank and comment lines, so the header
    // start is what places the error on its line; the failure point is
    // `usize::MAX` when the header grammar finds no defect.
    let mut grammar_failures: Vec<(usize, usize, usize)> = Vec::new();

    for directive in source_file.directives() {
        // Helper to push a successfully-converted directive
        // alongside its CST node so the post-pass span fixup
        // can index them in parallel.
        let cst_node = directive.syntax().clone();
        // `is_directive_producing` tracks whether THIS arm is
        // expected to emit a `Spanned<Directive>` (the 12
        // directive types). The catch-all below uses it to
        // surface a `SyntaxError` when a producing converter
        // returned `None` without emitting a more specific
        // diagnostic - the silent-drop class of bug the integ
        // tests caught for `2024-01-01 open` (no account),
        // `balance Assets:X` (no amount), etc.
        let is_directive_producing = matches!(
            directive,
            ast::Directive::Open(_)
                | ast::Directive::Close(_)
                | ast::Directive::Commodity(_)
                | ast::Directive::Note(_)
                | ast::Directive::Document(_)
                | ast::Directive::Event(_)
                | ast::Directive::Query(_)
                | ast::Directive::Price(_)
                | ast::Directive::Balance(_)
                | ast::Directive::Pad(_)
                | ast::Directive::Custom(_)
                | ast::Directive::Transaction(_)
        );
        let errors_before = errors.len();
        let pushed_directive = match directive {
            ast::Directive::Open(node) => convert_open(&node, bom_offset, &mut errors),
            ast::Directive::Close(node) => convert_close(&node, bom_offset, &mut errors),
            ast::Directive::Commodity(node) => convert_commodity(&node, bom_offset, &mut errors),
            ast::Directive::Note(node) => convert_note(&node, bom_offset, &mut errors),
            ast::Directive::Document(node) => convert_document(&node, bom_offset, &mut errors),
            ast::Directive::Event(node) => convert_event(&node, bom_offset, &mut errors),
            ast::Directive::Query(node) => convert_query(&node, bom_offset, &mut errors),
            ast::Directive::Price(node) => convert_price(&node, bom_offset, &mut errors),
            ast::Directive::Balance(node) => convert_balance(&node, bom_offset, &mut errors),
            ast::Directive::Pad(node) => convert_pad(&node, bom_offset, &mut errors),
            ast::Directive::Custom(node) => convert_custom(&node, bom_offset, &mut errors),
            ast::Directive::Transaction(node) => {
                // Green-tree conversion (no red-node allocation) with a red
                // fallback for transactions it doesn't yet handle exactly. The
                // green path returns `Some` only when its output is identical to
                // red's, so the hybrid is output-equivalent to the pure-red path.
                let green = node.syntax().green();
                let base =
                    u32::from(node.syntax().text_range().start()) as usize + bom_offset as usize;
                let green_dir = if use_green {
                    super::green::convert_transaction(green, base)
                } else {
                    None
                };
                match green_dir {
                    Some(d) => Some(d),
                    None => convert_transaction(&node, bom_offset, &mut errors),
                }
            }
            ast::Directive::Option(node) => {
                if let Some(triple) = convert_option(&node, bom_offset) {
                    options.push(triple);
                }
                None
            }
            ast::Directive::Include(node) => {
                if let Some(pair) = convert_include(&node, bom_offset) {
                    includes.push(pair);
                }
                None
            }
            ast::Directive::Plugin(node) => {
                if let Some(triple) = convert_plugin(&node, bom_offset) {
                    plugins.push(triple);
                }
                None
            }
            // State-only side effects: mutate the inherited
            // tag/meta sets that apply to subsequent directives.
            // A header with an invalid token on it is never reduced by
            // beancount's grammar, so it pushes or pops nothing there: a later
            // `poptag` of the tag is reported as absent, an earlier push stays
            // unbalanced (`header_has_invalid_token`).
            ast::Directive::Pushtag(node) => {
                if !header_has_invalid_token(node.syntax())
                    && let Some(tag_token) = node.tag()
                {
                    let span = node_span(node.syntax(), bom_offset);
                    tag_stack.push((Tag::new(tag_token.text().trim_start_matches('#')), span));
                }
                None
            }
            ast::Directive::Poptag(node) => {
                if !header_has_invalid_token(node.syntax())
                    && let Some(tag_token) = node.tag()
                {
                    let name = tag_token.text().trim_start_matches('#');
                    if let Some(pos) = tag_stack.iter().rposition(|(t, _)| t.as_str() == name) {
                        tag_stack.remove(pos);
                    } else {
                        errors.push(crate::ParseError::new(
                            crate::ParseErrorKind::InvalidPoptag(name.to_string()),
                            node_span(node.syntax(), bom_offset),
                        ));
                    }
                }
                None
            }
            ast::Directive::Pushmeta(node) => {
                if !header_has_invalid_token(node.syntax())
                    && let Some(key_token) = node.key()
                    && let Some(value) = pushmeta_value(node.syntax())
                {
                    let key = key_token.text_without_colon().to_string();
                    let span = node_span(node.syntax(), bom_offset);
                    meta_stack.push((key, value, span));
                }
                None
            }
            ast::Directive::Popmeta(node) => {
                if !header_has_invalid_token(node.syntax())
                    && let Some(key_token) = node.key()
                {
                    let key = key_token.text_without_colon().to_string();
                    if let Some(pos) = meta_stack.iter().rposition(|(k, _, _)| k == &key) {
                        meta_stack.remove(pos);
                    } else {
                        errors.push(crate::ParseError::new(
                            crate::ParseErrorKind::InvalidPopmeta(key),
                            node_span(node.syntax(), bom_offset),
                        ));
                    }
                }
                None
            }
        };
        // A header line beancount's grammar refuses (#2802). Checked only when
        // nothing else has reported an error on this directive yet, and it
        // REPORTS BUT DOES NOT DROP, for the same reason as
        // `reject_tags_and_links`: the directive still loads, so one stray
        // character does not cascade into unopened-account errors.
        let converted_or_stateful = pushed_directive.is_some() || !is_directive_producing;
        if converted_or_stateful
            && errors.len() == errors_before
            && let Some(err) = directive_header_check(
                &cst_node,
                stripped,
                bom_offset,
                &prior_error_starts,
                &mut header_tokens,
            )
        {
            errors.push(err);
        }
        if pushed_directive.is_some() && cst_node.kind() == crate::SyntaxKind::TRANSACTION {
            posting_line_check(
                &cst_node,
                stripped,
                bom_offset,
                &prior_error_starts,
                errors_before,
                &mut errors,
                &mut header_tokens,
            );
        }
        if converted_or_stateful {
            meta_entry_check(
                &cst_node,
                stripped,
                bom_offset,
                &prior_error_starts,
                errors_before,
                &mut errors,
                &mut header_tokens,
            );
        }
        if let Some(mut spanned) = pushed_directive {
            apply_inherited_state(&mut spanned.value, &tag_stack, &meta_stack);
            directives.push(spanned);
            directive_nodes.push(cst_node);
        } else if is_directive_producing && errors.len() == errors_before {
            // Producing converter silently dropped the directive
            // (typically: a required field like an account on
            // `open`, an amount on `balance`, or a source account
            // on `pad` was missing). Mirror the legacy parser's
            // top-level error-recovery path which emits a
            // `SyntaxError("unexpected input")` for the failed
            // span so downstream tooling sees the same shape.
            // The node's span takes in the blank and comment lines before it;
            // the error starts at the header, where beancount reports it.
            let mut span = node_span(&cst_node, bom_offset);
            // Where beancount's grammar fails on the header line, so a bad
            // date after that point does not swallow this error
            // (`report_invalid_dates`).
            if super::directive_header::directive_keyword(cst_node.kind()).is_some() {
                let off = bom_offset as usize;
                let end = header_line_tokens(&cst_node, &mut header_tokens);
                let header_start = header_tokens
                    .first()
                    .map_or(span.start, |(_, r)| r.start + off);
                let failed_at = super::directive_header::first_header_defect(
                    cst_node.kind(),
                    &header_tokens,
                    end,
                    stripped,
                )
                .map_or(usize::MAX, |defect| defect.range.start + off);
                span = Span::new(header_start.min(span.end), span.end);
                grammar_failures.push((span.start, header_start, failed_at));
            }
            errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                span,
            ));
        }
    }

    // Unclosed pushtag/pushmeta at EOF - legacy emits one error
    // per leftover stack entry, pointing at the originating push
    // directive's span.
    for (tag, span) in &tag_stack {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::UnclosedPushtag(tag.as_str().to_string()),
            *span,
        ));
    }
    for (key, _, span) in &meta_stack {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::UnclosedPushmeta(key.clone()),
            *span,
        ));
    }
    report_invalid_dates(
        source_file.syntax(),
        stripped,
        bom_offset,
        &grammar_failures,
        &mut errors,
    );
    // After `report_invalid_dates`, so an invalid date on a header is among
    // the errors that swallow the indented line after it.
    report_no_metadata_continuations(source_file.syntax(), stripped, bom_offset, &mut errors);
    // After `report_invalid_dates` too: a metadata line with an error of its
    // own (an invalid date included) is no repeat.
    report_duplicate_metadata(source_file.syntax(), bom_offset, &mut errors);
    errors.sort_by_key(|e| e.span.start);
    quiet_after_invalid_tokens(&mut errors, source_file.syntax(), stripped, bom_offset);
    drop_errors_inside_a_line_error(&mut errors, stripped, bom_offset, &grammar_failures);
    name_misspelled_booleans(&mut errors, stripped, bom_offset);
    name_mid_line_hash_comments(&mut errors, stripped, bom_offset);

    // Post-pass: align directive spans with the legacy parser's
    // convention (skip leading trivia, extend through inter-
    // directive trivia to the next directive's start).
    fixup_directive_spans(&source_file, bom_offset, &directive_nodes, &mut directives);

    // Pre-compute the file-wide formatter alignment from the
    // same `source_file` we just walked, so the formatter (and
    // every LSP handler that calls it) can skip the O(N_postings)
    // re-walk on every format request. See
    // `ParseResult::alignment` rustdoc for the cache contract;
    // the equivalence with a fresh `compute_alignment` call is
    // pinned by `parse_result_alignment_cache::*` (lib.rs tests).
    // NOT computed here: `compute_alignment` walks the tree through the red
    // ast accessors, and rowan allocates a `Box<NodeData>` per red node with
    // no recycling. Doing it eagerly charged every parse for a formatter pass
    // it usually never reads — 5.7%-12.3% of instructions by workload. See
    // `ParseResult::alignment`, which computes on first use and caches.
    let alignment = std::sync::OnceLock::new();

    // Capture the green root before we drop `source_file`. `.green()`
    // borrows (`&GreenNodeData`), so promote to an owned `GreenNode`; it is
    // reference-counted internally, cheap to clone, and `Send + Sync` — safe
    // to stash in the `Arc<ParseResult>` the LSP shares across threads.
    //
    // `to_owned()`, not `into_owned()`: rowan 0.17 changed `green()` from
    // returning `Cow<GreenNodeData>` to returning `&GreenNodeData`, so the
    // promotion now goes through `ToOwned` instead of `Cow::into_owned`.
    let syntax_root = source_file.syntax().green().to_owned();

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        account_occurrences,
        has_leading_bom,
        syntax_root,
        alignment,
    }
}

// ---- Directive converters --------------------------------------

/// Valid booking methods per beancount v3 - must match the
/// whitelist legacy `parser::parse_open_directive` enforces. An
/// `open` directive whose explicit booking string isn't on this
/// list is rejected (directive dropped, `InvalidBookingMethod`
/// error emitted) by both the legacy parser and `convert_open`.
const VALID_BOOKING_METHODS: &[&str] = &[
    "FIFO",
    "STRICT",
    "STRICT_WITH_SIZE",
    "LIFO",
    "HIFO",
    "NONE",
    "AVERAGE",
];

/// Reject `#tag` / `^link` tokens on a directive that does not take them.
///
/// beancount allows tags and links on TRANSACTIONS, and in v3 on `note` and
/// `document` — nowhere else. rledger accepted them everywhere, silently: each
/// `convert_*` reads the fields it wants and ignores the rest, so a trailing
/// token was never objected to by anything. `2018-06-01 open Assets:A #tag`
/// loaded clean here and is a parse error there (#1949).
///
/// Deliberately scans DIRECT child tokens only. Metadata lives in `META_ENTRY`
/// child NODES, and a metadata VALUE may legitimately be a tag (`k: #x`), so a
/// descendant walk would reject valid input — the opposite mistake, and a worse
/// one.
///
/// Not called from `note` or `document`: both take tags and links in beancount
/// v3 and we already agree with it there. A blanket rule over non-transaction
/// directives would break the two cases that are currently right, which is why
/// this is a per-directive call rather than one check in the dispatcher.
///
/// REPORTS BUT DOES NOT DROP, and that is a deliberate divergence in the error
/// SET (both tools still reject the file). beancount treats this as a parser
/// syntax error, so the directive never exists and every later reference to it
/// cascades:
///
///   2018-06-01 open Assets:N #tag
///   2018-06-02 * "t"
///     Assets:N   1.00 USD
///     ...
///
///   beancount   `ParserSyntaxError` + `ValidationError`: unknown account
///   rledger     the tag error alone; the account is still opened
///
/// Keeping the directive means the user gets one error naming the real
/// problem instead of that error plus a cascade of unopened-account noise
/// pointing at innocent lines. The compat oracle cannot flag the difference,
/// because its error axis compares only WHETHER a file errs and not which
/// errors, so it is written down here rather than left to be rediscovered.
fn reject_tags_and_links(
    node: &crate::SyntaxNode,
    directive: &str,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    for t in node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
    {
        let kind = t.kind();
        if !matches!(kind, K::TAG | K::LINK) {
            continue;
        }
        let what = if kind == K::TAG { "tag" } else { "link" };
        let range = t.text_range();
        let off = bom_offset as usize;
        let span = Span::new(
            usize::from(range.start()) + off,
            usize::from(range.end()) + off,
        );
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(format!(
                "the {directive} directive does not take a {what} ({}); \
                 tags and links belong to transactions, and to note and \
                 document directives",
                t.text()
            )),
            span,
        ));
    }
}

fn convert_open(
    node: &OpenDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "open", bom_offset, errors);
    let account = Account::new(node.account()?.text());
    let currencies: Vec<Currency> = node.currencies().map(|c| Currency::new(c.text())).collect();
    let mut booking = node.booking_method().and_then(|s| s.text_decoded());
    let span = node_span(node.syntax(), bom_offset);
    if let Some(b) = booking.take_if(|b| !VALID_BOOKING_METHODS.contains(&b.as_str())) {
        // beancount checks the booking method when it builds the directive,
        // which it never does for a statement with an invalid token in it, on
        // its header or a metadata line: the token is its only error there
        // (`open Assets:C$;c "x"`, #2872). Here the directive is kept, as
        // one with an invalid token is, without the booking method, and the
        // token's own error is the one reported.
        if !holds_an_invalid_token(node.syntax().green()) {
            errors.push(crate::ParseError::new(
                crate::ParseErrorKind::InvalidBookingMethod(b),
                span,
            ));
            return None;
        }
    }
    let meta = convert_meta_entries(node.syntax());

    let open = rustledger_core::directive::Open {
        date,
        account,
        currencies,
        booking,
        meta: meta.into(),
    };
    Some(Spanned::new(Directive::Open(open), span))
}

fn convert_close(
    node: &CloseDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "close", bom_offset, errors);
    let account = Account::new(node.account()?.text());
    let meta = convert_meta_entries(node.syntax());

    let close = rustledger_core::directive::Close {
        date,
        account,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Close(close), span))
}

fn convert_commodity(
    node: &CommodityDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "commodity", bom_offset, errors);
    let currency = Currency::new(node.currency()?.text());
    let meta = convert_meta_entries(node.syntax());

    let commodity = rustledger_core::directive::Commodity {
        date,
        currency,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Commodity(commodity), span))
}

/// Collect the `#tag` / `^link` tokens on a directive's HEADER line.
///
/// Stops at the newline that ends the header -- but only after the header has
/// actually started. A directive node can begin with leading trivia: when a
/// blank line precedes it, the node's first token is a NEWLINE, and breaking
/// on that dropped every tag. Both `note` and `document` did this, so a
/// `document` written the way ledgers are normally formatted -- a blank line
/// between directives -- silently lost its tags long before `note` gained any
/// (#2160 review).
///
/// The formatter already had this right: its header walks guard on a
/// `seen_content` flag for the same reason (`cst/format.rs`). The converter
/// was the outlier.
///
/// The header is deemed started once the directive's STRING has been seen:
/// the comment for a `note`, the path for a `document`. Tags and links follow
/// it on the same line, and metadata lines live in `META_ENTRY` child nodes
/// rather than as direct tokens, so they cannot leak in.
fn header_tags_and_links(node: &crate::SyntaxNode) -> (TagSet, LinkSet) {
    let mut tags = TagSet::new();
    let mut links = LinkSet::new();
    let mut header_started = false;
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::STRING => header_started = true,
            crate::SyntaxKind::NEWLINE if header_started => break,
            crate::SyntaxKind::TAG => {
                tags.insert(Tag::new(t.text().trim_start_matches('#')));
            }
            crate::SyntaxKind::LINK => {
                links.insert(Link::new(t.text().trim_start_matches('^')));
            }
            _ => {}
        }
    }
    (tags, links)
}

fn convert_note(
    node: &NoteDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let account = Account::new(node.account()?.text());
    let comment = node.text()?.text_decoded()?;
    // Trailing tags/links on the note header, collected the same way
    // `convert_document` does -- see `header_tags_and_links` for why "the
    // first NEWLINE" is the wrong place to stop.
    //
    // beancount v3 accepts these on a `note`. We parsed them and threw them
    // away, because `Note` had nowhere to put them (#2160) -- note this
    // directive does NOT call `reject_tags_and_links`, unlike `commodity` and
    // `event`, so they were accepted and silently dropped rather than
    // diagnosed.
    let (tags, links) = header_tags_and_links(node.syntax());
    let meta = convert_meta_entries(node.syntax());

    let note = rustledger_core::directive::Note {
        date,
        account,
        comment,
        tags,
        links,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Note(note), span))
}

fn convert_document(
    node: &DocumentDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let account = Account::new(node.account()?.text());
    let path = node.path()?.text_decoded()?;
    // Trailing tags/links on the document header (legacy
    // `parse_document_directive` collects them in a loop after
    // the path STRING). TAG / LINK tokens only appear in the
    // header, not in the META_ENTRY children walked separately
    // below -- see `header_tags_and_links` for where the walk
    // has to start and stop.
    let (tags, links) = header_tags_and_links(node.syntax());
    let meta = convert_meta_entries(node.syntax());

    let document = rustledger_core::directive::Document {
        date,
        account,
        path,
        tags,
        links,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Document(document), span))
}

fn convert_event(
    node: &EventDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "event", bom_offset, errors);
    let event_type = node.event_type()?.text_decoded()?;
    let value = node.value()?.text_decoded()?;
    let meta = convert_meta_entries(node.syntax());

    let event = rustledger_core::directive::Event {
        date,
        event_type,
        value,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Event(event), span))
}

fn convert_query(
    node: &QueryDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    // `query` was in neither camp: it did not keep tags and links the way a
    // transaction, note or document does, and it did not refuse them the way
    // the other seven directives do. So it took them and dropped them --
    // `Query` has no field to put them in -- while the message the refusal
    // arm emits states the very rule this omission broke.
    //
    // beancount rejects them: `2024-01-01 query "n" "SELECT date" #qtag`
    // gives `syntax error, unexpected TAG, expecting end of file or EOL`
    // (3.2.3), and its `Query` namedtuple is `(meta, date, name,
    // query_string)` with nowhere to keep one either (#2194).
    reject_tags_and_links(node.syntax(), "query", bom_offset, errors);
    let name = node.name()?.text_decoded()?;
    let query = node.query()?.text_decoded()?;
    let meta = convert_meta_entries(node.syntax());

    let q = rustledger_core::directive::Query {
        date,
        name,
        query,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Query(q), span))
}

/// The span of a `balance` / `price` value that holds MORE than the single
/// signed number those directives can represent — extra `NUMBER` tokens, or a
/// misplaced `,`.
///
/// Both directives fall back to "take the first `NUMBER` token and apply a
/// leading sign" when the value is not an arithmetic expression. That fallback
/// reads only the first token, so anything after it was DISCARDED IN SILENCE:
/// `price HOOL 1,23,4.50 USD` stored `1 USD`, a thousandfold error with exit 0.
/// Postings have rejected the same shapes all along (the lexer's grouping regex
/// is strict, and a split number never forms one `NUMBER` token) — this closes
/// the same hole for the directive family (#1892 follow-up).
///
/// Deliberately NOT flagged:
/// - a `~ tolerance` clause, whose second number is legitimate — the scan stops
///   at the `TILDE`;
/// - arithmetic (`0.25 + 0.75 USD`), which is evaluated before this is
///   consulted, so a well-formed expression never reaches it.
fn malformed_directive_value(node: &crate::SyntaxNode) -> Option<crate::TextRange> {
    let mut numbers = 0usize;
    let mut saw_comma = false;
    let mut start: Option<crate::TextRange> = None;
    let mut end: Option<crate::TextRange> = None;
    for t in node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
    {
        match t.kind() {
            // Tolerance begins; its number is not part of the value.
            crate::SyntaxKind::TILDE => break,
            // The trailing currency closes the value. A `price` directive's
            // BASE currency precedes the number, so only break once a number
            // has been seen.
            crate::SyntaxKind::CURRENCY if numbers > 0 => break,
            crate::SyntaxKind::NUMBER => {
                numbers += 1;
                start.get_or_insert(t.text_range());
                end = Some(t.text_range());
            }
            crate::SyntaxKind::COMMA => {
                saw_comma = true;
                start.get_or_insert(t.text_range());
                end = Some(t.text_range());
            }
            _ => {}
        }
    }
    if !saw_comma && numbers <= 1 {
        return None;
    }
    Some(crate::TextRange::new(start?.start(), end?.end()))
}

fn convert_price(
    node: &PriceDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "price", bom_offset, errors);
    let base_currency = Currency::new(node.base_currency()?.text());
    if let Some(range) = has_top_level_tilde(node.syntax()) {
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "a price has no tolerance: `~` is only valid on a balance \
                 assertion"
                    .to_string(),
            ),
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
        return None;
    }
    // Same arithmetic support as `convert_balance`: a price
    // directive's value can use `+`, `-`, `*`, `/`, and parens.
    let number =
        directive_arithmetic_value(node.syntax(), ToleranceForm::Forbidden).or_else(|| {
            // The fallback keeps only the first NUMBER, so refuse a value that
            // carries more than one — see `malformed_directive_value`.
            if let Some(range) = malformed_directive_value(node.syntax()) {
                let start: u32 = range.start().into();
                let end: u32 = range.end().into();
                let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                errors.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(
                        "malformed amount: expected one number, optionally signed, \
                     or an arithmetic expression. A thousands separator must be \
                     inside the number, as in `-1,234.00`"
                            .to_string(),
                    ),
                    span,
                ));
                return None;
            }
            let mut n = parse_decimal_token(node.number()?.text())?;
            if node_has_minus_before_number(node.syntax()) {
                // Python's rule: negating a zero yields a POSITIVE zero, so a
                // literal `-0.00` loads as `0.00` exactly as beancount parses it.
                // A bare `-n` would keep the sign bit and render `-0.00`.
                n = rustledger_core::negate_python(n);
            }
            Some(n)
        })?;
    let quote_currency = Currency::new(node.quote_currency()?.text());
    let amount = Amount::new(number, quote_currency);
    let meta = convert_meta_entries(node.syntax());

    let price = rustledger_core::directive::Price {
        date,
        currency: base_currency,
        amount,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Price(price), span))
}

fn convert_balance(
    node: &BalanceDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "balance", bom_offset, errors);
    let account = Account::new(node.account()?.text());
    // Beancount accepts arithmetic in the balance assertion's
    // value (`balance Assets:X 0.25 + 0.75 GBP` ≡ 1.00 GBP).
    // Falls back to the first NUMBER token if the expression
    // can't be evaluated, with the legacy sign-flip behavior.
    let number =
        directive_arithmetic_value(node.syntax(), ToleranceForm::Allowed).or_else(|| {
            // The fallback keeps only the first NUMBER, so refuse a value that
            // carries more than one — see `malformed_directive_value`.
            if let Some(range) = malformed_directive_value(node.syntax()) {
                let start: u32 = range.start().into();
                let end: u32 = range.end().into();
                let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                errors.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(
                        "malformed amount: expected one number, optionally signed, \
                     or an arithmetic expression. A thousands separator must be \
                     inside the number, as in `-1,234.00`"
                            .to_string(),
                    ),
                    span,
                ));
                return None;
            }
            let mut n = parse_decimal_token(node.number()?.text())?;
            if node_has_minus_before_number(node.syntax()) {
                // Python's rule: negating a zero yields a POSITIVE zero, so a
                // literal `-0.00` loads as `0.00` exactly as beancount parses it.
                // A bare `-n` would keep the sign bit and render `-0.00`.
                n = rustledger_core::negate_python(n);
            }
            Some(n)
        })?;
    let currency = Currency::new(node.currency()?.text());
    let amount = Amount::new(number, currency);
    let tolerance = check_balance_tolerance(node.syntax(), bom_offset, errors);
    let meta = convert_meta_entries(node.syntax());

    let balance = rustledger_core::directive::Balance {
        date,
        account,
        amount,
        tolerance,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Balance(balance), span))
}

/// Diagnose a tolerance clause that says something the model cannot keep.
///
/// beancount's grammar is `NUMBER ~ NUMBER CURRENCY`: one currency, trailing,
/// and it rejects any currency before the `~`. This function READS the
/// tolerance of every spelling that has one meaning, and diagnoses the ones
/// that have none or contradict themselves, each for its own reason:
///
/// - `1.00 USD ~ 0.01 USD` is READ as `1.00 ~ 0.01 USD` (the currency is
///   stated twice and agrees). It is still a syntax error, as in beancount:
///   the header check (`directive_header`, #2802) reports the `~` after the
///   currency, and the directive is kept with this one reading.
/// - `1.00 USD ~ 0.01 EUR` is DIAGNOSED. A tolerance denominated in a
///   different currency than the amount is not redundancy, it is an
///   assertion the model has no field for — and `rledger format` used to
///   erase the EUR from the file on its way past.
/// - `1.00 ~ 0.001 0.02 USD` is DIAGNOSED. Two juxtaposed numbers with no
///   operator have no reading at all; this took the first and dropped the
///   rest silently. (`~ 0.005 + 0.005` is arithmetic and still evaluates.)
///
/// The table is in `docs/reference/compatibility.md` (#2193, #2802).
fn check_balance_tolerance(
    node: &crate::SyntaxNode,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Decimal> {
    // Validate AND extract in one walk. Splitting them cost a second full
    // token scan per `balance`, which measured +5.8% on a 56,000-balance
    // ledger -- small in a real ledger, where most directives are
    // transactions, but paid on every balance for nothing.
    //
    // Most balance directives carry no tolerance at all, so answer that
    // first, from an iterator rather than a Vec.
    // Answer "is there a tolerance at all" WITHOUT allocating: on a ledger of
    // balances the overwhelming majority have none, and collecting their
    // tokens first measured +4% against main, which reached the same answer
    // through a `skip_while` that left an empty Vec. The collect below now
    // happens only for the directives that actually carry a `~`.
    if !node
        .children_with_tokens()
        .any(|el| el.kind() == crate::SyntaxKind::TILDE)
    {
        return None;
    }
    let toks: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .collect();
    let tilde = toks
        .iter()
        .position(|t| t.kind() == crate::SyntaxKind::TILDE)?;
    let (head, tail) = toks.split_at(tilde);
    let tail = &tail[1..];

    let currency_of = |ts: &[crate::SyntaxToken]| {
        ts.iter()
            .find(|t| t.kind() == crate::SyntaxKind::CURRENCY)
            .cloned()
    };
    if let (Some(before), Some(after)) = (currency_of(head), currency_of(tail))
        && before.text() != after.text()
    {
        let range = after.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(format!(
                "a balance tolerance must be in the same currency as the amount: \
                 the amount is {} and the tolerance is {}. Drop the second \
                 currency, or correct it",
                before.text(),
                after.text(),
            )),
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
    }

    // A second `~` is its own mistake and deserves its own sentence. Without
    // this it fell into the juxtaposed-numbers arm below, whose message says
    // the numbers are "side by side" when a tilde sits between them --
    // a diagnostic describing input the author did not write.
    if let Some(extra) = tail.iter().find(|t| t.kind() == crate::SyntaxKind::TILDE) {
        let range = extra.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "a balance takes one tolerance: `AMOUNT ~ TOLERANCE CURRENCY`".to_string(),
            ),
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
        return None;
    }

    // Numbers in the tolerance region, i.e. before its trailing CURRENCY.
    // Sliced out of `tail` rather than collected: `cost_region_value` takes
    // the same `&[SyntaxToken]`, so the two Vecs this used to build (one of
    // references, one cloning every token back out) bought nothing.
    let end = tail
        .iter()
        .position(|t| t.kind() == crate::SyntaxKind::CURRENCY)
        .unwrap_or(tail.len());
    let region = &tail[..end];
    let numbers = region
        .iter()
        .filter(|t| t.kind() == crate::SyntaxKind::NUMBER)
        .count();

    // A `~` with nothing after it announces a tolerance that is not there.
    // It was accepted as though unwritten, and `rledger format` then deleted
    // the tilde -- the same erase-the-difference behavior as the mismatched
    // currency. beancount calls it a syntax error.
    if numbers == 0 {
        // An invalid token right after the `~` is the line's error, the
        // lexer's own: beancount's grammar never sees a missing tolerance.
        if tail
            .first()
            .is_some_and(|t| t.kind() == crate::SyntaxKind::ERROR_TOKEN)
        {
            return None;
        }
        let range = toks[tilde].text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "a `~` must be followed by a tolerance: `AMOUNT ~ TOLERANCE CURRENCY`".to_string(),
            ),
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
        return None;
    }
    // Stay quiet unless the region is made only of things an expression can
    // contain. On `~ .005 + .005` the lexer already reports the real problem
    // (a number with no integer part, which we reject and beancount accepts)
    // and this would add "the second was being discarded" on top -- a claim
    // about input that never parsed, next to the diagnostic that explains it.
    let expression_shaped = region.iter().all(|t| {
        matches!(
            t.kind(),
            crate::SyntaxKind::NUMBER
                | crate::SyntaxKind::PLUS
                | crate::SyntaxKind::MINUS
                | crate::SyntaxKind::STAR
                | crate::SyntaxKind::SLASH
                | crate::SyntaxKind::L_PAREN
                | crate::SyntaxKind::R_PAREN
        )
    });
    if expression_shaped
        && numbers > 1
        && cost_region_value(region).is_none()
        && let Some(second) = region
            .iter()
            .filter(|t| t.kind() == crate::SyntaxKind::NUMBER)
            .nth(1)
    {
        let range = second.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "a balance tolerance takes one number, or an arithmetic \
                 expression. Two numbers side by side have no reading, and the \
                 second was being discarded"
                    .to_string(),
            ),
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
    }

    tolerance_value(region)
}

/// Evaluate a tolerance region: an expression when it is one, else its first
/// NUMBER.
///
/// `10.00 ~ 0.005 * 2 USD` asserts a tolerance of 0.010. Taking the first
/// NUMBER instead truncated it to 0.005 and REJECTED files beancount accepts
/// -- and the E2002 message printed the truncated figure, so the diagnostic
/// advertised the bug (#1944). Same root cause as the cost-spec truncation in
/// #1939: a number-bearing position that never reached the shared evaluator.
fn tolerance_value(region: &[crate::SyntaxToken]) -> Option<Decimal> {
    if region.is_empty() {
        return None;
    }
    if let Some(value) = cost_region_value(region) {
        return Some(value);
    }
    region
        .iter()
        .find(|t| t.kind() == crate::SyntaxKind::NUMBER)
        .and_then(|t| parse_decimal_token(t.text()))
}

fn convert_pad(
    node: &PadDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    reject_tags_and_links(node.syntax(), "pad", bom_offset, errors);
    let account = Account::new(node.target_account()?.text());
    let source_account = Account::new(node.source_account()?.text());
    let meta = convert_meta_entries(node.syntax());

    let pad = rustledger_core::directive::Pad {
        date,
        account,
        source_account,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Pad(pad), span))
}

fn convert_custom(
    node: &CustomDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let custom_type = node.custom_type()?.text_decoded()?;
    let values = extract_custom_values(node.syntax());
    let meta = convert_meta_entries(node.syntax());

    let custom = rustledger_core::directive::Custom {
        date,
        custom_type,
        values,
        meta: meta.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Custom(custom), span))
}

/// Walk the heterogeneous value tokens after the `custom "type"`
/// header. The legacy parser tries each value type in this order:
/// string > account > bool > amount (NUMBER+CURRENCY) > number >
/// date > currency. We replicate that priority on the flat token
/// stream, with one structural pass that pairs an immediately-
/// adjacent NUMBER+CURRENCY into an [`Amount`].
fn extract_custom_values(node: &crate::SyntaxNode) -> Vec<MetaValue> {
    // Collect tokens by kind, skipping trivia. We do a two-pass:
    // first form Amount pairs (NUMBER + CURRENCY adjacent, ignoring
    // whitespace), then emit remaining tokens individually.
    let raw: Vec<rowan::SyntaxToken<crate::BeancountLanguage>> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_value_walk_trivia(t.kind()))
        .collect();

    // One value at a time through the shared walk: this is what gives custom
    // directives the same MINUS-sign, Tag/Link, arithmetic and
    // `NUMBER CURRENCY` → Amount handling as pushmeta, and the same value
    // boundaries as the errors raised for them.
    value_groups(&raw)
        .into_iter()
        .filter_map(|(_, group)| match group {
            ValueGroup::Value(value, _) => Some(value),
            // An expression with no value is rejected (by
            // `unevaluable_value_expressions` or the header-line grammar
            // check), so nothing is emitted for it (#2806).
            ValueGroup::NoValue { .. } => None,
        })
        // Drop the values the directive is simultaneously being REJECTED
        // for. `value_tokens_to_meta` is shared with metadata, where a
        // `#tag` is legal, but a custom directive accepts none of these --
        // matching beancount, measured across all eight value types.
        //
        // Emitting them anyway made `Custom.values` contain entries the
        // parser had already errored on, so a consumer reading `values`
        // without also reading `errors` saw data the parser had declared
        // invalid (#2190). The errors themselves are raised by
        // `custom_value_check` (bare currency) and
        // `extract_custom_pushmeta_taglink_errors` (tag/link); this keeps
        // the emitted values in step with them.
        //
        // A CURRENCY that pairs with a preceding NUMBER has already become
        // an `Amount` by here, so a surviving `Currency` is exactly the
        // bare one those checks reject. Valid values on the same line are
        // unaffected: `custom "b" "ok" #atag 42` keeps `"ok"` and `42`.
        .filter(|value| {
            !matches!(
                value,
                MetaValue::Tag(_) | MetaValue::Link(_) | MetaValue::Currency(_)
            )
        })
        .collect()
}

fn strip_string_quotes(raw: &str) -> Option<&str> {
    let bytes = raw.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len() - 1] != b'"' {
        return None;
    }
    Some(&raw[1..raw.len() - 1])
}

fn convert_option(node: &OptionDirective, bom_offset: u32) -> Option<(String, String, Span)> {
    let key = node.key()?.text_decoded()?;
    let value = node.value()?.text_decoded()?;
    Some((
        key,
        value,
        single_line_directive_span(node.syntax(), bom_offset),
    ))
}

fn convert_include(node: &IncludeDirective, bom_offset: u32) -> Option<(String, Span)> {
    let path = node.path()?.text_decoded()?;
    Some((path, single_line_directive_span(node.syntax(), bom_offset)))
}

fn convert_plugin(
    node: &PluginDirective,
    bom_offset: u32,
) -> Option<(String, Option<String>, Span)> {
    let module = node.module()?.text_decoded()?;
    let config = node.config().and_then(|c| c.text_decoded());
    Some((
        module,
        config,
        single_line_directive_span(node.syntax(), bom_offset),
    ))
}

// ---- Transaction + Posting + sub-nodes -------------------------

fn convert_transaction(
    node: &AstTransaction,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;

    // Flag: explicit (TransactionFlag), or '*' for a header with no flag
    // token, which `transaction_header_check` reports as a syntax error
    // (#2905); the transaction is kept, as for every header defect.
    let flag = node.flag().map_or('*', |f| flag_char_from_transaction(&f));

    // Payee and narration: the shared slot rule `txn_header::header_strings`
    // (#2932), which reads the header's strings together with any invalid
    // token among them (the one token that can have swallowed a string), so
    // that a string never moves to a different field under error recovery;
    // every other token leaves the count rule standing. Green
    // `convert_transaction_header` and the typed `payee()` / `narration()`
    // accessors use the same rule.
    let slots = node.string_slots();
    let nth = |i: usize| {
        node.strings()
            .nth(i)
            .and_then(|s| s.text_decoded())
            .unwrap_or_default()
    };
    let payee = slots.payee().map(|i| InternedStr::from(nth(i)));
    let narration = InternedStr::from(slots.directive_narration().map(nth).unwrap_or_default());

    // Tags / links from the TRANSACTION node: the typed AST
    // accessor `tags()`/`links()` is scoped to the header region.
    // Trailing TAG / LINK tokens appearing on body lines (after
    // the header NEWLINE, OUTSIDE any POSTING / META_ENTRY child
    // node) are also part of the transaction's tag/link set per
    // Beancount semantics - `extract_transaction_body_errors`
    // already exempts them from the malformed-body diagnostic for
    // this reason. Aggregate them here so they don't silently
    // disappear.
    let mut tags: TagSet = node
        .tags()
        .map(|t| Tag::new(t.text().trim_start_matches('#')))
        .collect();
    let mut links: LinkSet = node
        .links()
        .map(|l| Link::new(l.text().trim_start_matches('^')))
        .collect();
    // Only body lines BEFORE the first posting count (#2575): see
    // `body_tag_joins_transaction`. Mirrors green `convert_transaction_header`.
    let mut posting_seen = false;
    for el in node.syntax().children_with_tokens() {
        let t = match el {
            rowan::NodeOrToken::Token(t) => t,
            // Nodes (POSTING / META_ENTRY) own their own internal
            // tokens; we don't recurse into them.
            rowan::NodeOrToken::Node(n) => {
                posting_seen |= n.kind() == crate::SyntaxKind::POSTING;
                continue;
            }
        };
        if !body_tag_joins_transaction(posting_seen) {
            continue;
        }
        match t.kind() {
            crate::SyntaxKind::TAG => {
                let stripped = t.text().trim_start_matches('#');
                tags.insert(Tag::new(stripped));
            }
            crate::SyntaxKind::LINK => {
                let stripped = t.text().trim_start_matches('^');
                links.insert(Link::new(stripped));
            }
            _ => {}
        }
    }

    // Transaction-level metadata (META_ENTRY children directly on
    // the TRANSACTION node, NOT on POSTING children). A repeated key keeps
    // its first value, as in beancount (#2893).
    let meta = convert_meta_entries_keeping_first(node.syntax());

    // Postings + pre-posting comments. The CST puts inter-
    // posting trivia (including `; comment` lines) as flat
    // tokens DIRECT under TRANSACTION between two POSTING
    // nodes. Walk in source order: COMMENT tokens accumulate
    // into `pending`, then attach to the next POSTING node's
    // `comments` field when we reach it. Tokens before the
    // header NEWLINE are skipped (they're transaction-header
    // content). Comments that remain in `pending` after the
    // final posting belong to the transaction itself
    // (legacy: `txn.trailing_comments = pending_comments`).
    let (postings, trailing_comments) = collect_postings_with_comments(node, bom_offset, errors);

    // Deprecated `|` separator between payee and narration: a
    // PIPE token in the header region. Legacy treats this as a
    // recoverable warning-shaped error (`DeprecatedPipeSymbol`)
    // and keeps the directive, so we do the same here.
    if header_has_pipe(node) {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::DeprecatedPipeSymbol,
            node_span(node.syntax(), bom_offset),
        ));
    }

    let txn = rustledger_core::directive::Transaction {
        date,
        flag,
        payee,
        narration,
        tags,
        links,
        meta: meta.into(),
        postings,
        trailing_comments: trailing_comments.into(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Transaction(txn), span))
}

/// Returns true if the TRANSACTION header (direct-child tokens
/// up to the first NEWLINE) contains a `PIPE` token. The legacy
/// parser surfaces a `DeprecatedPipeSymbol` diagnostic for this
/// shape; the CST lexer classifies `|` as `PIPE`, so we just
/// scan the header directly.
///
/// beancount warns about the pipe from its grammar, as it reads it, so a
/// header with no flag (#2905), which its grammar fails on at the first
/// string, is discarded to the end of the line, pipe included, with no
/// warning. Only that defect is asked about here: it is always the first
/// token after the date, so it always precedes the pipe.
fn header_has_pipe(node: &AstTransaction) -> bool {
    // Leading trivia (blank lines, comments) can precede the header inside the
    // node; `HeaderEnd` skips it (#2628).
    let mut header = HeaderEnd::default();
    let mut pipe_at = None;
    for el in node.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if !header.in_header(t.kind()) {
            break;
        }
        if t.kind() == crate::SyntaxKind::PIPE {
            pipe_at = Some(usize::from(t.text_range().start()));
            break;
        }
    }
    let Some(pipe_at) = pipe_at else {
        return false;
    };
    let tokens = node.header_tokens().map(|t| {
        let r = t.text_range();
        (t.kind(), usize::from(r.start())..usize::from(r.end()))
    });
    !matches!(
        super::txn_header::first_header_defect(tokens),
        Some((defect, range))
            if defect == super::txn_header::HeaderDefect::MissingFlag && range.start < pipe_at
    )
}

/// Walk a `TRANSACTION`'s children in source order, attaching any
/// inter-posting `; comment` lines that appear as flat tokens
/// between `POSTING` nodes to the NEXT posting's `comments`
/// field. Matches the legacy parser, which collects
/// `pending_comments` while reading the body and applies them to
/// the next posting it parses.
///
/// Tokens before the header-terminator NEWLINE belong to the
/// transaction header (date/flag/strings/tags/links) and are
/// skipped, as is any leading trivia before the header: a comment
/// on the header line or on a line before the transaction never
/// becomes a posting comment ([`HeaderEnd`], #2628).
///
/// Returns `(postings, trailing_comments)`: the second element is
/// any pending comments left over AFTER the final posting, which
/// legacy assigns to `Transaction::trailing_comments`.
fn collect_postings_with_comments(
    node: &AstTransaction,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> (Vec<Spanned<Posting>>, Vec<String>) {
    // Sized to the POSTING children up front, as the green fast path does
    // (`green.rs`, `posting_count`): growing by push left a 2-posting
    // transaction at capacity 4, 256 unused bytes held for the life of the
    // ledger on every transaction that takes this path (#2834).
    let posting_count = node
        .syntax()
        .children()
        .filter(|n| n.kind() == crate::SyntaxKind::POSTING)
        .count();
    let mut out = Vec::with_capacity(posting_count);
    let mut pending: Vec<String> = Vec::new();
    // Leading trivia (blank lines, comment lines) sits inside the node before
    // the header; only the NEWLINE after the header content ends it (#2628).
    let mut header = HeaderEnd::default();
    for el in node.syntax().children_with_tokens() {
        match el {
            rowan::NodeOrToken::Token(t) => {
                if header.in_header(t.kind()) {
                    continue;
                }
                if is_comment_kind(t.kind()) {
                    pending.push(t.text().to_string());
                } else if !is_trivia_kind(t.kind())
                    && !matches!(t.kind(), crate::SyntaxKind::TAG | crate::SyntaxKind::LINK)
                {
                    // Non-trivia, non-comment token in the
                    // transaction body that's NOT inside a
                    // POSTING / META_ENTRY child node = malformed
                    // body line (caught separately by
                    // `extract_transaction_body_errors`). Treat
                    // the same as a failed POSTING: clear pending
                    // so the malformed line's preceding comments
                    // don't migrate onto the next valid posting.
                    //
                    // EXEMPT TAG / LINK: trailing tags/links on
                    // transaction body lines (after the header)
                    // are valid Beancount - they extend the
                    // transaction's tag/link set without being
                    // a new posting. Treating them as malformed
                    // would drop legitimate preceding comments
                    // that belong to the NEXT posting. The same
                    // exemption appears in
                    // `extract_transaction_body_errors`, which
                    // does the parallel "is this a malformed
                    // body line?" classification.
                    pending.clear();
                }
            }
            rowan::NodeOrToken::Node(n) => {
                // META_ENTRY or POSTING before the header
                // NEWLINE shouldn't happen in well-formed
                // input; treat any child node as "past the
                // header" if we somehow encounter one.
                header.end();
                if let Some(p) = ast::Posting::cast(n) {
                    if let Some(mut spanned) = convert_posting(&p, bom_offset, errors) {
                        if !pending.is_empty() {
                            spanned.value.comments = std::mem::take(&mut pending).into();
                        }
                        out.push(spanned);
                    } else {
                        // Failed posting consumes any pending
                        // inter-posting comments - they belonged
                        // to it. Without this clear, a malformed
                        // posting's preceding comments would
                        // migrate forward and attach to the NEXT
                        // successful posting, misattributing them
                        // visibly to the wrong account line.
                        pending.clear();
                    }
                }
                // META_ENTRY child nodes: comments collected so
                // far don't apply to them (they're transaction
                // metadata). Drop them.
            }
        }
    }
    (out, pending)
}

fn flag_char_from_transaction(flag: &ast::TransactionFlag) -> char {
    match flag.classify() {
        TransactionFlagKind::Star | TransactionFlagKind::Txn => '*',
        TransactionFlagKind::Pending => '!',
        TransactionFlagKind::Hash => '#',
        TransactionFlagKind::Letter | TransactionFlagKind::CurrencyLetter => {
            flag.text().chars().next().unwrap_or('*')
        }
    }
}

fn convert_posting(
    node: &ast::Posting,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Posting>> {
    let account = Account::new(node.account()?.text());

    let flag = node.flag().map(|f| flag_char_from_posting(&f));

    // A well-formed posting has AT MOST one `AMOUNT` child node
    // (the units). The CST builder will accept input like
    // `Expenses:Food  5 USD + 3 USD` and produce TWO sibling
    // `AMOUNT` nodes joined by a flat PLUS token, because the
    // grammar doesn't enforce that PLUS between two complete
    // amounts is invalid. `Posting::amount()` returns only the
    // first via `first_child`, so without this guard the second
    // amount (and the joining `+`) would be silently dropped and
    // the user's transaction would balance against the wrong
    // number. Emit a `SyntaxError` pointing at the trailing
    // siblings and keep the first amount.
    let mut amount_children = node
        .syntax()
        .children()
        .filter(|n| ast::Amount::can_cast(n.kind()));
    let first_amount = amount_children.next();
    let first_amount_end: Option<u32> = first_amount.as_ref().map(|n| n.text_range().end().into());
    let mut sibling_start: Option<u32> = None;
    let mut sibling_end: u32 = 0;
    for extra in amount_children {
        let range = extra.text_range();
        let start_u32: u32 = range.start().into();
        let end_u32: u32 = range.end().into();
        if sibling_start.is_none() {
            sibling_start = Some(start_u32);
        }
        sibling_end = end_u32;
    }
    if let Some(start_u32) = sibling_start {
        // Extend the span back to the end of the FIRST AMOUNT so
        // the diagnostic underline covers any joining operator
        // (`+`, `*`, whitespace) between the kept amount and the
        // orphans. Without this, a user sees only `3 USD` in
        // `5 USD + 3 USD` highlighted - and may not realize the
        // `+ 3 USD` together is what needs to be removed.
        let underline_start = first_amount_end.unwrap_or(start_u32);
        let span = Span::new(
            (underline_start + bom_offset) as usize,
            (sibling_end + bom_offset) as usize,
        );
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "unexpected trailing tokens after posting amount".to_string(),
            ),
            span,
        ));
    }
    // The mirror of the guard above, for tokens dropped BEFORE the amount
    // rather than after it.
    //
    // `starts_amount` only opens an `AMOUNT` at `NUMBER`, `CURRENCY`,
    // `L_PAREN`, or a sign directly followed by one of those. Anything else
    // becomes a flat `POSTING` child, and nothing downstream reads flat
    // children — so `-,123.00 USD` parsed as `POSTING(MINUS COMMA
    // AMOUNT(NUMBER CURRENCY))` and booked as **+123.00**, silently losing the
    // sign. A stray comma is the way to hit this in practice, because a
    // thousands separator only belongs INSIDE a `NUMBER` token (the lexer's
    // grouping regex is strict) and a misplaced one splits the amount in two.
    //
    // Report rather than repair: `,123` and `-,123` have no agreed meaning, so
    // guessing one would be inventing data. See issue #1892's discussion.
    if let Some(range) = orphaned_amount_prefix(node.syntax()) {
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "unexpected token before posting amount: a `+`/`-` must be \
                 followed by a number, and a thousands separator must be \
                 inside one (as in `-1,234.00`)"
                    .to_string(),
            ),
            span,
        ));
    }

    let units = first_amount
        .and_then(ast::Amount::cast)
        .and_then(|amt| convert_amount_to_incomplete(&amt, errors, bom_offset));
    let cost = node.cost_spec().map(|cs| convert_cost_spec(&cs));
    let price = node
        .price_annotation()
        .map(|pa| convert_price_annotation(&pa, errors, bom_offset));
    // A repeated key keeps its first value, as in beancount (#2893). A
    // posting's written `filename:` / `lineno:` repeats the location beancount
    // sets first, so the real location stands and the written one is dropped
    // (`drop_posting_location_keys`).
    let mut meta = convert_meta_entries_keeping_first(node.syntax());
    drop_posting_location_keys(&mut meta);

    // Trailing comments on the posting line: COMMENT direct-
    // child tokens BEFORE the terminator NEWLINE. The legacy
    // parser collects same-line `;` content into
    // `posting.trailing_comments`.
    let trailing_comments: Vec<String> = node
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .take_while(|t| t.kind() != crate::SyntaxKind::NEWLINE)
        .filter(|t| is_comment_kind(t.kind()))
        .map(|t| t.text().to_string())
        .collect();

    let posting = Posting {
        account,
        units,
        cost: cost.map(Box::new),
        price: price.map(Box::new),
        flag,
        meta: meta.into(),
        comments: Default::default(),
        trailing_comments: trailing_comments.into(),
        booking: Default::default(),
    };
    let span = posting_span(node.syntax(), bom_offset);
    Some(Spanned::new(posting, span))
}

fn flag_char_from_posting(flag: &ast::PostingFlag) -> char {
    match flag.classify() {
        PostingFlagKind::Star => '*',
        PostingFlagKind::Pending => '!',
        PostingFlagKind::Hash => '#',
        PostingFlagKind::Letter | PostingFlagKind::CurrencyLetter => {
            flag.text().chars().next().unwrap_or('*')
        }
    }
}

/// Convert an AMOUNT node into an [`IncompleteAmount`]. Returns
/// `None` if neither a number nor a currency is present (which
/// shouldn't happen for a well-formed AMOUNT, but matches the
/// lossless CST contract). Sign is folded into the number.
///
/// **Arithmetic limitation**: when the AMOUNT contains an
/// arithmetic expression (`100+5 USD`), only the FIRST `NUMBER`
/// is used. A proper expression evaluator is deferred - none of
/// the directive types we currently handle outside of postings
/// use AMOUNT shapes that the legacy parser would have evaluated
/// differently.
fn convert_amount_to_incomplete(
    amt: &ast::Amount,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> Option<IncompleteAmount> {
    // Arithmetic AMOUNT expressions (`120 / 3 USD`, `(1+2) USD`):
    // run the recursive-descent evaluator on the flat token
    // stream. Fast-path plain `NUMBER CURRENCY` shapes to keep
    // the common case allocation-free.
    let number = if amt.is_arithmetic() {
        let evaluated = evaluate_amount_expression(amt);
        if evaluated.is_none() {
            // `is_arithmetic` was true but the evaluator gave up
            // (decimal overflow, division by zero, malformed
            // expression, unbalanced parens). Without this
            // emission the amount silently degrades to
            // `CurrencyOnly` and the user only sees a downstream
            // "transaction doesn't balance" - masking the actual
            // root cause. Pin the span to the AMOUNT node so the
            // diagnostic underlines the offending expression.
            let range = amt.syntax().text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "invalid arithmetic expression in amount (overflow, division by zero, \
                     an inexact quotient below 1e-28, or malformed)"
                        .to_string(),
                ),
                span,
            ));
        }
        evaluated
    } else {
        amt.number().and_then(|n| {
            let parsed = parse_decimal_token(n.text());
            if parsed.is_none() {
                // Symmetry with the arithmetic-failure path: when
                // a plain NUMBER token in an AMOUNT can't be
                // turned into a Decimal (e.g., 30+ digits - the
                // lexer's NUMBER regex has no max length but
                // `rust_decimal`'s 28-digit ceiling rejects it),
                // surface a diagnostic instead of silently
                // degrading to `CurrencyOnly`. Without this the
                // user only sees "transaction doesn't balance"
                // and never learns the parser dropped a number.
                let range = n.syntax().text_range();
                let start: u32 = range.start().into();
                let end: u32 = range.end().into();
                let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                errors.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(
                        "invalid number in amount (likely exceeds 28-digit Decimal precision)"
                            .to_string(),
                    ),
                    span,
                ));
            }
            let mut value = parsed?;
            if let Some(sign) = amt.sign()
                && sign.is_minus()
            {
                // See the sign note above — `negate_python` keeps a zero
                // unsigned, matching beancount's parse of `-0.00`.
                value = rustledger_core::negate_python(value);
            }
            Some(value)
        })
    };
    let currency = amt.currency().map(|c| Currency::new(c.text()));
    match (number, currency) {
        (Some(n), Some(c)) => Some(IncompleteAmount::Complete(Amount::new(n, c))),
        (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
        (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
        (None, None) => None,
    }
}

/// Evaluate the arithmetic expression inside an `AMOUNT` node and
/// return the resulting decimal. Returns `None` when evaluation
/// fails (division by zero, decimal overflow, malformed parens,
/// missing operand).
///
/// AMOUNT children are flat tokens (no expression sub-tree): a
/// sequence of `NUMBER`, `PLUS`, `MINUS`, `STAR`, `SLASH`,
/// `L_PAREN`, `R_PAREN`, and a trailing `CURRENCY` at depth 0
/// that's the amount's currency rather than part of the
/// expression. The currency is stripped first; the rest goes
/// through recursive descent mirroring legacy
/// `parser::parse_expr` / `parse_term` / `parse_primary`.
///
/// Operator precedence and unary handling match Python beancount:
/// `*` and `/` bind tighter than `+` and `-`; a leading or post-
/// operator `-` is unary negation.
fn evaluate_amount_expression(amt: &ast::Amount) -> Option<Decimal> {
    let tokens = amount_expression_tokens(amt);
    let mut cursor = 0usize;
    let value = parse_arith_expr(&tokens, &mut cursor)?;
    // Trailing tokens after a successful parse mean the expression
    // is malformed (`1+2 3 USD`); refuse rather than silently
    // dropping them.
    if cursor != tokens.len() {
        return None;
    }
    Some(value)
}

/// Evaluate the arithmetic expression that appears as the
/// numeric value of a `BALANCE` / `PRICE` directive, returning
/// the resulting decimal or `None` if not arithmetic (single
/// NUMBER, callers fall back to `parse_decimal_token`).
///
/// Unlike `AMOUNT`, these directives don't wrap their value in
/// a dedicated node - the tokens are flat under the directive
/// node. The relevant region is from the FIRST `NUMBER` token up
/// to (but not including) the FIRST `CURRENCY` token at paren-
/// depth 0 (the amount currency). For BALANCE, this correctly
/// stops before any trailing `~ NUMBER [CURRENCY]` tolerance
/// region too.
///
/// Returns `Some` only when the slice contains at least one
/// arithmetic operator (`+`, `-`, `*`, `/`) or parens - for a
/// bare single `NUMBER`, returns `None` so the caller can use
/// the existing fast path (which preserves the legacy sign-flip
/// behavior).
/// Does this directive's header carry a top-level `~`?
///
/// Only `balance` has a tolerance. A `price` with one used to be accepted
/// silently -- `price USD 1.10 ~ 0.01 EUR` evaluated to 1.10 and dropped the
/// rest on the floor, because `~` is not an arithmetic operator, so the
/// expression scan took the fast path and fell back to the first NUMBER. A
/// value the author wrote and the parser discarded without a word is worse
/// than a diagnosed error.
fn has_top_level_tilde(node: &crate::SyntaxNode) -> Option<crate::TextRange> {
    let mut depth: i32 = 0;
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            // Skip child nodes rather than stopping at one. A price's only
            // child node is a META_ENTRY, whose own tokens are not direct
            // children of this node, so nothing here can see a `~` written
            // inside metadata -- but bailing out at the first node would mean
            // a header that ever gains one stops being checked at all.
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::L_PAREN => depth += 1,
            crate::SyntaxKind::R_PAREN => depth -= 1,
            crate::SyntaxKind::TILDE if depth == 0 => return Some(t.text_range()),
            _ => {}
        }
    }
    None
}

/// Whether a `~` may end this directive's amount expression.
///
/// `balance` takes a tolerance; `price` does not. The distinction matters
/// because stopping at `~` unconditionally makes a price with a tolerance
/// evaluate its amount and DISCARD the tolerance silently, which is worse
/// than the malformed-value error it used to get.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ToleranceForm {
    /// `balance ACCOUNT AMOUNT ~ TOLERANCE CURRENCY`
    Allowed,
    /// No tolerance in this directive's grammar.
    Forbidden,
}

fn directive_arithmetic_value(
    node: &crate::SyntaxNode,
    tolerance: ToleranceForm,
) -> Option<Decimal> {
    let raw: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        // Skip the directive header (DATE, keyword, ACCOUNT / base CURRENCY)
        // and stop at the first token that can BEGIN a value.
        //
        // This used to skip to the first `NUMBER`, which also swallowed a
        // leading `(`: `(1 + 5) / 2.1 USD` became `1 + 5 ) / 2.1`, failed to
        // parse, and fell through to "take the first NUMBER" — so the
        // directive silently asserted against **1**. A leading sign was
        // likewise dropped and re-applied by the caller. Neither header token
        // can be a `NUMBER`, `L_PAREN` or a sign, so this cannot over-skip.
        .skip_while(|t| {
            !matches!(
                t.kind(),
                crate::SyntaxKind::NUMBER
                    | crate::SyntaxKind::L_PAREN
                    | crate::SyntaxKind::MINUS
                    | crate::SyntaxKind::PLUS
            )
        })
        .collect();
    let mut depth: i32 = 0;
    let mut first_currency_idx: Option<usize> = None;
    let mut tilde_idx: Option<usize> = None;
    for (i, t) in raw.iter().enumerate() {
        match t.kind() {
            crate::SyntaxKind::L_PAREN => depth += 1,
            crate::SyntaxKind::R_PAREN => depth -= 1,
            crate::SyntaxKind::CURRENCY if depth == 0 && first_currency_idx.is_none() => {
                first_currency_idx = Some(i);
            }
            // `~` ends the amount and begins the tolerance, which is read
            // separately. Without this the tolerance was swallowed INTO the
            // expression: `0.25 + 0.75 ~ 0.01 USD` became `0.25 + 0.75 ~ 0.01`,
            // which is not arithmetic, so the whole value was reported
            // malformed. Only a currency-less amount reached that state --
            // `0.25 + 0.75 USD ~ 0.01 USD` stopped at the first CURRENCY and
            // parsed -- which is why the plain-number form (`100.00 ~ 0.01
            // USD`) worked and only its arithmetic sibling did not (#2191).
            crate::SyntaxKind::TILDE
                if tolerance == ToleranceForm::Allowed && depth == 0 && tilde_idx.is_none() =>
            {
                tilde_idx = Some(i);
            }
            _ => {}
        }
    }
    let end = match (first_currency_idx, tilde_idx) {
        (Some(c), Some(t)) => c.min(t),
        (Some(i), None) | (None, Some(i)) => i,
        (None, None) => raw.len(),
    };
    let tokens: Vec<crate::SyntaxToken> = raw.into_iter().take(end).collect();
    // Fast-path: zero or one token = no arithmetic.
    let has_op = tokens.iter().any(|t| {
        matches!(
            t.kind(),
            crate::SyntaxKind::PLUS
                | crate::SyntaxKind::MINUS
                | crate::SyntaxKind::STAR
                | crate::SyntaxKind::SLASH
                | crate::SyntaxKind::L_PAREN
        )
    });
    if !has_op {
        return None;
    }
    let mut cursor = 0usize;
    let value = parse_arith_expr(&tokens, &mut cursor)?;
    if cursor != tokens.len() {
        return None;
    }
    Some(value)
}

/// Collect AMOUNT's expression tokens - every non-trivia direct-
/// child token EXCEPT the trailing `CURRENCY` at paren-depth 0
/// (which is the amount's currency, not part of the expression).
/// Parens at any depth are preserved so `parse_arith_primary` can
/// recurse through them.
fn amount_expression_tokens(amt: &ast::Amount) -> Vec<crate::SyntaxToken> {
    let raw: Vec<crate::SyntaxToken> = amt
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .collect();
    // Find the index of the LAST `CURRENCY` at depth 0 - same
    // disambiguator as `Amount::currency()`. Tokens before that
    // index form the arithmetic expression.
    let mut depth: i32 = 0;
    let mut trailing_currency_idx: Option<usize> = None;
    for (i, t) in raw.iter().enumerate() {
        match t.kind() {
            crate::SyntaxKind::L_PAREN => depth += 1,
            crate::SyntaxKind::R_PAREN => depth -= 1,
            crate::SyntaxKind::CURRENCY if depth == 0 => trailing_currency_idx = Some(i),
            _ => {}
        }
    }
    let end = trailing_currency_idx.unwrap_or(raw.len());
    raw.into_iter().take(end).collect()
}

/// `expr := term (('+' | '-') term)*` - left-associative.
///
/// The value of the expression at `cursor`, or `None` when it is malformed or
/// does not evaluate. [`read_arith_expr`] tells those two apart.
fn parse_arith_expr<T: TokenView>(tokens: &[T], cursor: &mut usize) -> Option<Decimal> {
    match read_arith_expr(tokens, cursor) {
        ArithRead::Value(value) => Some(value),
        ArithRead::Malformed | ArithRead::NoValue => None,
    }
}

/// The result of reading an arithmetic expression with [`read_arith_expr`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ArithRead {
    /// Malformed (a dangling operator, an unclosed parenthesis): the cursor
    /// stops where the expression breaks off.
    Malformed,
    /// Well formed, but with no value (division by zero, overflow): the
    /// cursor is past the expression.
    NoValue,
    /// Evaluates to this value.
    Value(Decimal),
}

/// The error side of the steps behind [`read_arith_expr`], so they can use `?`.
struct Malformed;

/// One step of [`read_arith_expr`]. `Ok(None)` is a well-formed step with no
/// value.
type ArithStep = Result<Option<Decimal>, Malformed>;

/// The canonical expression reader behind [`parse_arith_expr`]. It keeps
/// reading after a step fails to evaluate, so the cursor always ends where
/// the expression does, which is what a caller needs to report it (#2806).
fn read_arith_expr<T: TokenView>(tokens: &[T], cursor: &mut usize) -> ArithRead {
    match read_arith_sum(tokens, cursor) {
        Err(Malformed) => ArithRead::Malformed,
        Ok(None) => ArithRead::NoValue,
        Ok(Some(value)) => ArithRead::Value(value),
    }
}

/// `expr := term (('+' | '-') term)*`, the step behind [`read_arith_expr`].
fn read_arith_sum<T: TokenView>(tokens: &[T], cursor: &mut usize) -> ArithStep {
    let mut result = read_arith_term(tokens, cursor)?;
    while let Some(op) = tokens.get(*cursor).map(TokenView::kind) {
        match op {
            crate::SyntaxKind::PLUS => {
                *cursor += 1;
                let rhs = read_arith_term(tokens, cursor)?;
                result = result.zip(rhs).and_then(|(a, b)| a.checked_add(b));
            }
            crate::SyntaxKind::MINUS => {
                *cursor += 1;
                let rhs = read_arith_term(tokens, cursor)?;
                result = result.zip(rhs).and_then(|(a, b)| a.checked_sub(b));
            }
            _ => break,
        }
    }
    Ok(result)
}

/// `term := primary (('*' | '/') primary)*` - left-associative.
fn read_arith_term<T: TokenView>(tokens: &[T], cursor: &mut usize) -> ArithStep {
    let mut result = read_arith_primary(tokens, cursor)?;
    while let Some(op) = tokens.get(*cursor).map(TokenView::kind) {
        match op {
            crate::SyntaxKind::STAR => {
                *cursor += 1;
                let rhs = read_arith_primary(tokens, cursor)?;
                result = result.zip(rhs).and_then(|(a, b)| a.checked_mul(b));
            }
            crate::SyntaxKind::SLASH => {
                *cursor += 1;
                let rhs = read_arith_primary(tokens, cursor)?;
                // Python's division, as beancount's grammar computes it:
                // the ideal exponent on an exact quotient (`10/4` is `2.5`,
                // where `checked_div` gave `2.50`), 28 significant digits on
                // an inexact one (#2813). `None` on a zero divisor.
                result = result
                    .zip(rhs)
                    .and_then(|(a, b)| rustledger_core::py_div(a, b));
            }
            _ => break,
        }
    }
    Ok(result)
}

/// `primary := '(' expr ')' | '-' primary | '+' primary | NUMBER`.
fn read_arith_primary<T: TokenView>(tokens: &[T], cursor: &mut usize) -> ArithStep {
    let t = tokens.get(*cursor).ok_or(Malformed)?;
    match t.kind() {
        crate::SyntaxKind::L_PAREN => {
            *cursor += 1;
            let inner = read_arith_sum(tokens, cursor)?;
            // Mandatory closer; an unbalanced parenthesis is malformed
            // - `Amount::currency()` already refuses to surface a
            // currency for unbalanced parens, so the amount as a
            // whole degrades cleanly to `NumberOnly`/`None`.
            let close = tokens.get(*cursor).ok_or(Malformed)?;
            if close.kind() != crate::SyntaxKind::R_PAREN {
                return Err(Malformed);
            }
            *cursor += 1;
            Ok(inner)
        }
        crate::SyntaxKind::MINUS => {
            *cursor += 1;
            Ok(read_arith_primary(tokens, cursor)?.map(|inner| -inner))
        }
        crate::SyntaxKind::PLUS => {
            *cursor += 1;
            read_arith_primary(tokens, cursor)
        }
        crate::SyntaxKind::NUMBER => {
            *cursor += 1;
            Ok(parse_decimal_token(t.text()))
        }
        _ => Err(Malformed),
    }
}

/// The slice of a cost-spec segment holding its NUMBER expression: from the
/// first token that can begin a value up to the first `CURRENCY` at paren
/// depth 0.
///
/// Depth matters because a currency cannot appear inside the parens of a
/// numeric expression, but stopping at the first `CURRENCY` unconditionally
/// would be wrong the moment one ever could.
fn cost_number_region<T: TokenView>(seg: &[T]) -> &[T] {
    use crate::SyntaxKind as K;
    let start = seg
        .iter()
        .position(|t| matches!(t.kind(), K::NUMBER | K::L_PAREN | K::MINUS | K::PLUS))
        .unwrap_or(seg.len());
    let mut depth = 0i32;
    let mut end = seg.len();
    for (i, t) in seg.iter().enumerate().skip(start) {
        match t.kind() {
            K::L_PAREN => depth += 1,
            K::R_PAREN => depth -= 1,
            K::CURRENCY if depth == 0 => {
                end = i;
                break;
            }
            // A comma ends the number region too (`{10 USD, 2014-02-25}`);
            // without this a malformed spec could drag the date into the
            // expression and fail the whole parse instead of just the number.
            K::COMMA if depth == 0 => {
                end = i;
                break;
            }
            _ => {}
        }
    }
    &seg[start..end]
}

/// Evaluate a cost-spec number region, but ONLY when it is genuinely
/// arithmetic.
///
/// Returns `None` for an UNSIGNED bare `NUMBER` so the caller keeps its
/// existing single-token latch, leaving the overwhelmingly common case on the
/// allocation-free path.
///
/// A SIGNED number is not in that set: `MINUS`/`PLUS` counts as an operator, so
/// `{-200.00 USD}` routes through the evaluator. That is deliberate and is
/// itself a fix — the latch only ever read `NUMBER` tokens and never applied a
/// leading sign, so a negative cost was booked as POSITIVE. An earlier draft of
/// this comment claimed the latch "carries legacy sign handling"; it does not,
/// and the two `TotalsAndSigns` corpus fixtures prove it.
///
/// Why this exists at all: the price path has always evaluated expressions
/// (`convert_amount_to_incomplete` -> `evaluate_amount_expression`) while the
/// cost path latched the first `NUMBER` token and silently dropped the rest, so
/// `{10.00 * 3 USD}` booked a cost of 10.00. Same computation, two
/// implementations, nothing asserting agreement — the exact drift shape
/// AGENTS.md's Canonical-Function Discipline describes. The fix is to share the
/// evaluator, not to teach this path its own arithmetic (#1939).
fn cost_region_value<T: TokenView>(seg: &[T]) -> Option<Decimal> {
    match cost_region_read(seg)? {
        ArithRead::Value(value) => Some(value),
        ArithRead::Malformed | ArithRead::NoValue => None,
    }
}

/// [`cost_region_value`] with the three outcomes kept apart: `None` when the
/// region is not an expression at all (a bare `NUMBER`, which keeps its
/// single-token latch), otherwise how the expression reads. Trailing tokens
/// after the expression make it [`ArithRead::Malformed`].
///
/// The metadata converter needs the difference: a well-formed expression with
/// no value (`kk: 1/0`) must not fall back to the latched first number (`1`).
fn cost_region_read<T: TokenView>(seg: &[T]) -> Option<ArithRead> {
    use crate::SyntaxKind as K;
    // Trivia first. `cost_spec_from_tokens` is handed EVERY child token,
    // whitespace included, and the evaluator refuses any token it does not
    // recognize — so without this the region is `10.00 WS * WS 3` and every
    // expression silently falls back to the latched first number, i.e. the bug
    // this is meant to fix, still there but now with more code. The other two
    // evaluators (`directive_arithmetic_value`, `amount_expression_tokens`)
    // both filter trivia for the same reason.
    let kept: Vec<&T> = seg.iter().filter(|t| !is_trivia_kind(t.kind())).collect();
    let region = cost_number_region(&kept);
    if !region.iter().any(|t| {
        matches!(
            t.kind(),
            K::PLUS | K::MINUS | K::STAR | K::SLASH | K::L_PAREN
        )
    }) {
        return None;
    }
    let mut cursor = 0usize;
    let read = read_arith_expr(region, &mut cursor);
    // Trailing tokens mean the expression is malformed; refuse rather than
    // silently dropping them, matching `evaluate_amount_expression`.
    if cursor != region.len() {
        return Some(ArithRead::Malformed);
    }
    Some(read)
}

fn convert_cost_spec(cs: &ast::CostSpec) -> CostSpec {
    cost_spec_from_tokens(
        cs.syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token),
    )
}

/// Minimal view of a lexed token — kind + text — implemented by both tree
/// walkers (red `SyntaxToken`, green `&GreenTokenData`) so the token-level
/// semantic helpers ([`cost_spec_from_tokens`], [`meta_value_from_tokens`])
/// are SHARED rather than hand-mirrored. Every historical green/red fuzz
/// divergence (#1704, #1713, the `{*}` merge flag) landed in a hand-mirrored
/// copy of these semantics; with one implementation the class is gone.
pub(super) trait TokenView {
    /// The token's [`crate::SyntaxKind`].
    fn kind(&self) -> crate::SyntaxKind;
    /// The token's source text.
    fn text(&self) -> &str;
}

impl<T: TokenView> TokenView for &T {
    fn kind(&self) -> crate::SyntaxKind {
        (*self).kind()
    }
    fn text(&self) -> &str {
        (*self).text()
    }
}

impl TokenView for rowan::SyntaxToken<crate::BeancountLanguage> {
    // `Self::kind`/`Self::text` resolve to the INHERENT `SyntaxToken`
    // methods (inherent associated functions take precedence over trait
    // methods in path resolution) — this is delegation, not recursion.
    // The `Self::` form is clippy's own preference here (`use_self`).
    fn kind(&self) -> crate::SyntaxKind {
        Self::kind(self)
    }
    fn text(&self) -> &str {
        Self::text(self)
    }
}

impl TokenView for &rowan::GreenTokenData {
    fn kind(&self) -> crate::SyntaxKind {
        <crate::BeancountLanguage as rowan::Language>::kind_from_raw((*self).kind())
    }
    fn text(&self) -> &str {
        (*self).text()
    }
}
/// The `{*}` merge-flag state machine.
///
/// ONE implementation, driven by both token walkers: [`cost_spec_from_tokens`]
/// feeds it inside its single pass, and [`super::ast::CostSpec::is_merge`]
/// feeds it while walking the red tree. The rule was hand-mirrored in those two
/// places until the 2026-08-01 mutation run showed EVERY mutant in this machine
/// surviving on the `convert.rs` side: the only tests exercising the rule went
/// through the `ast.rs` copy, so the canonical could have been broken outright
/// without one test failing. That is the drift this module's `TokenView` doc
/// says it exists to prevent, in the one place it had not been applied.
///
/// The rule: a `*` is the merge marker when it begins a cost COMPONENT, that
/// is, when the previous non-whitespace token is the opener or a comma. The
/// cost is a comma-separated list of components (number, currency, date,
/// label, `*`), and beancount's grammar accepts `*` as any of them, so
/// `{100.00 USD, *}` and `{2020-01-01, *}` are merges exactly as `{*}` is
/// (#2329). A `*` after a number or a closing parenthesis is the
/// multiplication operator, as in `{500 * 2 USD}`.
///
/// This used to be decided by the first token after the opener alone, so a
/// trailing `*` was silently read as not-merge: the spec booked as a plain
/// per-unit filter, a different operation, with no diagnostic.
///
/// Tokens before the first opener are ignored, as are later openers on
/// malformed input: only the first opener starts the component list.
#[derive(Default)]
pub(in crate::cst) struct MergeFlag {
    past_opener: bool,
    /// Whether the previous non-whitespace token began a component: the
    /// opener or a comma.
    at_component_start: bool,
    merge: bool,
}

impl MergeFlag {
    /// Feed the next token kind, in source order.
    pub(in crate::cst) const fn feed(&mut self, kind: crate::SyntaxKind) {
        use crate::SyntaxKind as K;
        match kind {
            K::WHITESPACE => {}
            K::L_BRACE | K::L_DOUBLE_BRACE | K::L_BRACE_HASH if !self.past_opener => {
                self.past_opener = true;
                self.at_component_start = true;
            }
            _ if !self.past_opener => {}
            K::STAR if self.at_component_start => {
                self.merge = true;
                self.at_component_start = false;
            }
            K::COMMA => self.at_component_start = true,
            _ => self.at_component_start = false,
        }
    }

    /// Whether the tokens fed so far describe a `{*}` merge cost.
    pub(in crate::cst) const fn is_merge(&self) -> bool {
        self.merge
    }
}

/// Convert the direct child tokens of a `COST_SPEC` node into a [`CostSpec`]
/// (forms `{N CCY}`, `{{T CCY}}`, `{N # T CCY}`, `{*}` merge, plus optional
/// date + label). The single source of truth for BOTH walkers (red
/// `convert_cost_spec`, green `convert_cost_spec`).
///
/// Cost numbers are plain `NUMBER` tokens (no arithmetic evaluation); an
/// unparsable one yields `number: None` with no diagnostic, so this needs no
/// bail and always returns a `CostSpec`.
///
/// There are TWO number semantics and both must be carried (#1713):
/// - the compound `{a # b}` path retries past UNPARSABLE number tokens on
///   each side of the hash (`is_none()` guards re-arm when the parse fails);
/// - the plain path uses the first NUMBER *token*, parsed or not (a latch).
///
/// A single latched tracker satisfies only the plain path: on
/// `{<garbage-number> 2 # ...}` the compound side must retry to `2` while
/// the latch keeps `None` (the historical `fuzz_green_eq_red` divergence).
///
/// Compound `{a # b}` (beancount `compound_amount`): per-unit AND a lump
/// total on top; the cost totals `N*a + b`. Surfaced as written — units may
/// be interpolated later, so the combined total cannot be computed here;
/// booking derives it (#1700). An omitted side is zero, which is
/// arithmetically exact (`{# b}` ≡ `{{b}}`, `{a #}` ≡ `{a}`). The hash can
/// arrive fused with the brace as a single `L_BRACE_HASH` opener.
///
/// `is_total` = any `{{` present anywhere. The `{*}` merge flag is decided
/// by the first non-whitespace, non-opener token after an opener (`*` →
/// merge, anything else → not — a STAR elsewhere is the multiplication
/// operator, e.g. `{500 * 2 USD}`); a scan-everything pass that re-arms on
/// later openers flips the flag on malformed inputs where it must not
/// (another historical divergence).
pub(super) fn cost_spec_from_tokens(tokens: impl Iterator<Item = impl TokenView>) -> CostSpec {
    use crate::SyntaxKind as K;
    // Materialized because the arithmetic evaluator needs random access
    // (backtracking over a `(`...`)` group). Cost specs are a handful of
    // tokens, so the allocation is not on any hot path worth defending.
    let toks: Vec<_> = tokens.collect();
    let mut is_total = false;
    let mut first_number: Option<Decimal> = None; // latched (plain path)
    let mut seen_number = false;
    let mut pre_hash: Option<Decimal> = None; // retried (compound path)
    let mut past_hash = false;
    let mut post_hash_total: Option<Decimal> = None; // retried (compound path)
    let mut currency: Option<Currency> = None;
    let mut date: Option<NaiveDate> = None;
    let mut date_seen = false;
    let mut label: Option<String> = None;
    let mut label_seen = false;
    let mut merge_flag = MergeFlag::default();
    for t in &toks {
        let kind = t.kind();
        // Runs alongside the value machine below; see `MergeFlag`.
        merge_flag.feed(kind);
        match kind {
            K::L_DOUBLE_BRACE => is_total = true,
            K::NUMBER => {
                if past_hash {
                    if post_hash_total.is_none() {
                        post_hash_total = parse_decimal_token(t.text());
                    }
                } else {
                    if pre_hash.is_none() {
                        pre_hash = parse_decimal_token(t.text());
                    }
                    if !seen_number {
                        seen_number = true;
                        first_number = parse_decimal_token(t.text());
                    }
                }
            }
            K::HASH | K::L_BRACE_HASH => past_hash = true,
            K::CURRENCY if currency.is_none() => currency = Some(Currency::new(t.text())),
            K::DATE if !date_seen => {
                date_seen = true;
                date = parse_date_token(t.text());
            }
            K::STRING if !label_seen => {
                label_seen = true;
                label = decode_string_token(t.text());
            }
            _ => {}
        }
    }
    // ARITHMETIC OVERRIDE. The latches above take the first NUMBER of each
    // region, which is right for `{10.00 USD}` and wrong for both
    // `{10.00 * 3 USD}` and `{-200.00 USD}` — the latch reads NUMBER tokens
    // only, so it truncated the first and dropped the sign of the second.
    // `cost_region_value` returns None for an unsigned bare number, so that
    // case keeps the latch untouched. See #1939.
    let hash_at = toks
        .iter()
        .position(|t| matches!(t.kind(), K::HASH | K::L_BRACE_HASH));
    match hash_at {
        Some(i) => {
            if let Some(v) = cost_region_value(&toks[..i]) {
                pre_hash = Some(v);
            }
            if let Some(v) = cost_region_value(&toks[i + 1..]) {
                post_hash_total = Some(v);
            }
        }
        None => {
            if let Some(v) = cost_region_value(&toks) {
                first_number = Some(v);
            }
        }
    }

    // A malformed component list means we do not know the cost, so do not
    // report one (#2008). `{, 100.0 USD, , }` and `{45.23 USD / 2015-07-16 /
    // "blabla"}` both have a number our recovery can scrape out, and scraping
    // it is how `rledger check` came to print `E3001 does not balance:
    // residual 980.10 USD` — an arithmetic complaint about a typo, whose
    // number was produced by this function rather than by anything the author
    // wrote. Dropping to "unknown" hands the posting to interpolation, which
    // already knows how to solve for a single unknown per currency group and
    // to reject more than one.
    //
    // The currency is kept: `{, 100.0 USD, , }` names USD unambiguously, so
    // "an unknown cost in USD" is the honest reading. Same rule as `{ # USD}`
    // above — never invent a number the author did not write.
    let shape_ok =
        super::cost_spec_shape::first_cost_spec_defect(toks.iter().map(|t| (t.kind(), ())))
            .is_none();

    let number = if !shape_ok {
        None
    } else if past_hash {
        match (pre_hash, post_hash_total) {
            // `{ # USD}` — no number on EITHER side of the `#`. There is no
            // cost number here at all, so say so; `unwrap_or_default()` used to
            // invent `Compound { per_unit: 0, total: 0 }`, a perfectly
            // determinable zero cost. That is why #2008 case 5 loaded clean:
            // interpolation counts a cost spec with no determinable number as
            // one unknown for its currency and enforces "at most one per
            // currency group", but an invented zero is not an unknown, so the
            // rule never saw it.
            //
            // Reported as `None`, exactly like `{USD}`, because that is what
            // the two shapes have in common: a currency and no number.
            //
            // Scoped to BOTH sides missing. `{100 # USD}` and `{# 500 USD}`
            // still default the absent side to zero — beancount treats it as
            // MISSING and would solve for it, which is a different and larger
            // change. The corpus says that is not urgent: `{ # CCY}` appears in
            // exactly one file (the #2008 fixture), and the one-sided forms
            // appear only in other parser-lima conformance fixtures. Widening
            // this without an oracle to check against is how a compat fix
            // starts breaking real ledgers.
            (None, None) => None,
            (per_unit, total) => Some(CostNumber::Compound {
                per_unit: per_unit.unwrap_or_default(),
                total: total.unwrap_or_default(),
            }),
        }
    } else {
        match (first_number, is_total) {
            (Some(v), true) => Some(CostNumber::Total { value: v }),
            (Some(v), false) => Some(CostNumber::PerUnit { value: v }),
            (None, _) => None,
        }
    };
    CostSpec {
        number,
        currency,
        date,
        label,
        merge: merge_flag.is_merge(),
    }
}

fn convert_price_annotation(
    pa: &ast::PriceAnnotation,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> PriceAnnotation {
    let kind = if pa.is_total() {
        PriceKind::Total
    } else {
        PriceKind::Unit
    };
    let amount = pa
        .amount()
        .and_then(|a| convert_amount_to_incomplete(&a, errors, bom_offset));
    PriceAnnotation { kind, amount }
}

// ---- Metadata extraction ---------------------------------------

/// Extract the [`Metadata`] map from the directive node's
/// `META_ENTRY` sub-line children. Matches the legacy parser's
/// behavior: each entry's key (with trailing `:` stripped) maps
/// to a typed [`MetaValue`] derived from the value tokens.
///
/// Built through [`MetadataBuilder`], not repeated inserts: a directive can
/// carry any number of metadata lines, and this must stay near-linear in
/// them (#2835 review).
///
/// A repeated key keeps its first position and its last value, as beancount
/// builds a directive's metadata (`new_metadata` over the key-value list): it
/// reports no error there. A transaction and a posting are the exception,
/// read by [`convert_meta_entries_keeping_first`].
fn convert_meta_entries(node: &crate::SyntaxNode) -> Metadata {
    meta_entries_builder(node).build()
}

/// [`convert_meta_entries`] for a transaction or a posting: a repeated key
/// keeps its FIRST value, as beancount keeps it there while it reports the
/// repeat (`Duplicate metadata field on entry` / `Duplicate posting metadata
/// field`, reported by `report_duplicate_metadata`) (#2893). The green
/// converters build theirs the same way.
fn convert_meta_entries_keeping_first(node: &crate::SyntaxNode) -> Metadata {
    meta_entries_builder(node).build_keeping_first()
}

/// Drop a posting's written `filename` and `lineno` metadata. Beancount sets
/// both on every posting before its written keys, so a written one is a
/// repeat (`report_duplicate_metadata`) and the first, real location stands;
/// rledger keeps a posting's location out of its metadata, so dropping the
/// written value leaves the real one in force (#2893). Shared by the red and
/// green posting converters.
pub(super) fn drop_posting_location_keys(meta: &mut Metadata) {
    meta.retain(|key, _| !POSTING_LOCATION_KEYS.contains(&key.as_str()));
}

/// The metadata keys beancount sets on every posting itself, before its
/// written keys: shared by `drop_posting_location_keys` and the posting
/// preset in `report_duplicate_metadata`.
const POSTING_LOCATION_KEYS: [&str; 2] = ["filename", "lineno"];

/// The `META_ENTRY` children of `node`, unresolved.
fn meta_entries_builder(node: &crate::SyntaxNode) -> MetadataBuilder {
    let mut meta = MetadataBuilder::new();
    for entry in node.children().filter_map(MetaEntry::cast) {
        let Some(key_token) = entry.key() else {
            continue;
        };
        let value = meta_value_from_entry(&entry);
        meta.push(key_token.text_without_colon(), value);
    }
    meta
}

/// The span of flat `POSTING` tokens sitting between the account and the
/// amount, if any — tokens the conversion would otherwise discard in silence.
///
/// CANONICAL: both conversion paths consult this. The green path bails to red
/// when it returns `Some` (red owns the diagnostic), so the two cannot disagree
/// about which postings are well formed — the property `fuzz_green_eq_red`
/// checks.
///
/// Deliberately narrow: only a stray sign or comma counts. Those are the
/// tokens that silently CHANGE A VALUE — a dropped `-` flips the sign, and a
/// misplaced `,` splits a number. Any other junk between the account and the
/// amount (a `✨` inside an account name, a mangled transaction header) is
/// already reported as "unexpected input" by error recovery, and reporting it
/// again here would double up on the same span with a message about thousands
/// separators that does not describe the actual problem.
///
/// Trivia and the posting flag are not orphans, and neither is anything at or
/// after the first `AMOUNT`: trailing junk is already reported separately.
pub(super) const fn is_orphanable_amount_prefix(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::MINUS | crate::SyntaxKind::PLUS | crate::SyntaxKind::COMMA
    )
}

pub(super) fn orphaned_amount_prefix(node: &crate::SyntaxNode) -> Option<crate::TextRange> {
    let mut seen_account = false;
    let mut start: Option<crate::TextRange> = None;
    let mut end: Option<crate::TextRange> = None;
    for el in node.children_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                // Only the AMOUNT ends the prefix — deliberately NOT any
                // structured node. A `COST_SPEC` or `PRICE_ANNOTATION` can
                // legitimately precede the units, and a stray sign or comma
                // sitting between one of those and the amount is just as
                // orphaned as one right after the account. Their own commas
                // live INSIDE their nodes, so this cannot false-positive on
                // `{100.00 USD, 2020-01-01}`.
                if ast::Amount::can_cast(n.kind()) {
                    break;
                }
            }
            rowan::NodeOrToken::Token(t) => {
                let kind = t.kind();
                if kind == crate::SyntaxKind::ACCOUNT {
                    seen_account = true;
                    continue;
                }
                // NEWLINE FIRST: `is_trivia_kind` counts it as trivia, so
                // testing that earlier would skip it and keep scanning past the
                // end of the posting line — and would leave the check below
                // unreachable. The green mirror stops at the newline, so
                // getting this order wrong is also how the two paths drift.
                if kind == crate::SyntaxKind::NEWLINE {
                    break;
                }
                if !seen_account || is_trivia_kind(kind) || is_comment_kind(kind) {
                    continue;
                }
                if !is_orphanable_amount_prefix(kind) {
                    continue;
                }
                start.get_or_insert(t.text_range());
                end = Some(t.text_range());
            }
        }
    }
    let (s, e) = (start?, end?);
    Some(crate::TextRange::new(s.start(), e.end()))
}

/// Returns true if a node's flat direct-child tokens contain a
/// `MINUS` BEFORE the first `NUMBER`. Used to detect signed
/// numeric values in directives like Balance / Price whose typed-
/// AST accessors return the unsigned NUMBER token only.
fn node_has_minus_before_number(node: &crate::SyntaxNode) -> bool {
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::MINUS => return true,
            crate::SyntaxKind::NUMBER => return false,
            _ => {}
        }
    }
    false
}

/// One value group read by [`value_tokens_to_meta`].
#[derive(Debug, PartialEq)]
pub(super) enum ValueGroup {
    /// A value, and the index just past it.
    Value(MetaValue, usize),
    /// An arithmetic expression with no value, and the index just past it
    /// (and past an adjacent `CURRENCY`). `unevaluable` is true when it is
    /// well formed but does not evaluate (division by zero, overflow), which
    /// [`unevaluable_value_expressions`] reports. A malformed one (a dangling
    /// operator, an unclosed parenthesis) is reported by the directive's
    /// header-line grammar check instead, so it is not reported twice.
    NoValue { end: usize, unevaluable: bool },
}

impl ValueGroup {
    const fn end(&self) -> usize {
        match self {
            Self::Value(_, end) | Self::NoValue { end, .. } => *end,
        }
    }
}

/// Discriminate one *value group* of raw metadata/custom value tokens
/// (`tokens[start..]`, trivia already filtered) into a [`MetaValue`], returning
/// the value and the index just past it, for [`extract_custom_values`].
/// `extract_custom_values` once dropped the leading `MINUS` (so `custom "x"
/// -50.00` emitted `+50.00`) and dropped `Tag`/`Link` entirely. `pushmeta`
/// values are metadata values and go through [`meta_value_from_tokens`]
/// instead ([`pushmeta_value`], #2812).
///
/// Discrimination mirrors the typed [`meta_value_from_entry`] (the `META_ENTRY`
/// sibling, which additionally escape-decodes strings via the typed AST). A
/// leading `MINUS` negates the following `NUMBER`; an adjacent `CURRENCY` makes
/// it an `Amount`. An arithmetic expression (`10/4 USD`, `(1+2)`) is evaluated
/// and consumed whole, as beancount does. Returns `None` for a non-value token
/// (the caller advances).
fn value_tokens_to_meta<T: TokenView>(tokens: &[T], start: usize) -> Option<ValueGroup> {
    if let Some(found) = arithmetic_meta_value(tokens, start) {
        return Some(found);
    }
    let mut i = start;
    let mut negate = false;
    if tokens.get(i).map(TokenView::kind) == Some(crate::SyntaxKind::MINUS) {
        negate = true;
        i += 1;
    }
    let t = tokens.get(i)?;
    let value = match t.kind() {
        crate::SyntaxKind::STRING => {
            let s = strip_string_quotes(t.text())?;
            MetaValue::String(s.to_string())
        }
        crate::SyntaxKind::NUMBER => {
            let mut decimal = parse_decimal_token(t.text())?;
            if negate {
                decimal = -decimal;
            }
            // Adjacent `CURRENCY` → `Amount` (negate applies to the amount too).
            if let Some(next) = tokens.get(i + 1)
                && next.kind() == crate::SyntaxKind::CURRENCY
            {
                return Some(ValueGroup::Value(
                    MetaValue::Amount(Amount::new(decimal, Currency::new(next.text()))),
                    i + 2,
                ));
            }
            number_meta_value(t.text(), decimal)
        }
        crate::SyntaxKind::DATE => MetaValue::Date(parse_date_token(t.text())?),
        crate::SyntaxKind::ACCOUNT => MetaValue::Account(Account::new(t.text())),
        crate::SyntaxKind::CURRENCY => MetaValue::Currency(Currency::new(t.text())),
        crate::SyntaxKind::BOOL_TRUE => MetaValue::Bool(true),
        crate::SyntaxKind::BOOL_FALSE => MetaValue::Bool(false),
        crate::SyntaxKind::TAG => MetaValue::Tag(Tag::new(t.text().trim_start_matches('#'))),
        crate::SyntaxKind::LINK => MetaValue::Link(Link::new(t.text().trim_start_matches('^'))),
        _ => return None,
    };
    Some(ValueGroup::Value(value, i + 1))
}

/// The arithmetic branch of [`value_tokens_to_meta`]: read the expression
/// starting at `tokens[start]` with the shared [`read_arith_expr`], pairing an
/// adjacent `CURRENCY` into an [`Amount`]. `custom "c" 10/4 USD` is `2.5 USD`
/// in beancount and used to split into `10` and `4 USD`, with no error (#2806).
///
/// An expression with no value is one [`ValueGroup::NoValue`] group, never a
/// split into the numbers around the operator: `10/0 USD` used to become `10`
/// and `0 USD`.
///
/// Returns `None` when the run is not an expression: a lone, optionally
/// negated, `NUMBER` keeps the literal path so its `Int` vs `Number` spelling
/// is unchanged.
fn arithmetic_meta_value<T: TokenView>(tokens: &[T], start: usize) -> Option<ValueGroup> {
    use crate::SyntaxKind as K;
    if !matches!(
        tokens.get(start)?.kind(),
        K::NUMBER | K::MINUS | K::PLUS | K::L_PAREN
    ) {
        return None;
    }
    let mut cursor = start;
    let read = read_arith_expr(tokens, &mut cursor);
    if read == ArithRead::Malformed {
        // Malformed. The group also takes the value token the read broke off
        // at, where an operand was due (`10 + TRUE`, `(1+2 USD`), so nothing
        // from the rejected expression is emitted: beancount rejects the
        // whole directive. A token that cannot be a value (`~`) is left to the
        // walk, which steps over it.
        let stop = cursor.max(start + 1);
        let broke_at_value = tokens.get(stop).is_some_and(|t| {
            matches!(
                t.kind(),
                K::STRING
                    | K::NUMBER
                    | K::DATE
                    | K::ACCOUNT
                    | K::CURRENCY
                    | K::BOOL_TRUE
                    | K::BOOL_FALSE
                    | K::TAG
                    | K::LINK
            )
        });
        return Some(ValueGroup::NoValue {
            end: stop + usize::from(broke_at_value),
            unevaluable: false,
        });
    }
    let consumed: Vec<K> = tokens[start..cursor].iter().map(TokenView::kind).collect();
    if matches!(consumed.as_slice(), [K::NUMBER] | [K::MINUS, K::NUMBER]) {
        return None;
    }
    let currency = tokens.get(cursor).filter(|t| t.kind() == K::CURRENCY);
    let end = cursor + usize::from(currency.is_some());
    let ArithRead::Value(value) = read else {
        return Some(ValueGroup::NoValue {
            end,
            unevaluable: true,
        });
    };
    let value = match currency {
        Some(c) => MetaValue::Amount(Amount::new(value, Currency::new(c.text()))),
        // Render the RESULT to decide Int vs Number, as the metadata path does.
        None => number_meta_value(&value.to_string(), value),
    };
    Some(ValueGroup::Value(value, end))
}

/// Every value group of a `custom` directive, with the index it starts at.
/// `tokens` are the directive's non-trivia tokens; the values are the ones
/// after the custom type-name string.
///
/// The one walk shared by [`extract_custom_values`] and
/// [`unevaluable_value_expressions`] (both trees), so the values emitted and
/// the errors raised cannot disagree about where a value starts and ends.
pub(super) fn value_groups<T: TokenView>(tokens: &[T]) -> Vec<(usize, ValueGroup)> {
    use crate::SyntaxKind as K;
    let mut groups = Vec::new();
    let mut i = tokens
        .iter()
        .position(|t| matches!(t.kind(), K::STRING | K::META_KEY))
        .map_or(tokens.len(), |p| p + 1);
    while i < tokens.len() {
        // ONE advance for both branches, so the loop provably terminates.
        //
        // It used to advance in two places, and only the value branch was
        // guarded. That left the `else` free to move `i` BACKWARD, which does
        // not merely spin: stepping back re-enters the branch above, pushes
        // another value, steps forward, and repeats, allocating without
        // bound. Memory runs out before any per-test timeout can fire, so on
        // CI it takes the whole runner down and surfaces as "the runner has
        // received a shutdown signal", indistinguishable from infrastructure.
        // Two full mutation runs lost the same three parser shards to it
        // (runs 30765289550 and 30768895946) before the cause was found.
        //
        // `value_tokens_to_meta` returns the index past what it consumed, so
        // the assert is the contract and the clamp is the belt: in release a
        // violation costs one wasted token rather than the process.
        let next = match value_tokens_to_meta(tokens, i) {
            Some(group) => {
                let end = group.end();
                groups.push((i, group));
                end
            }
            None => i + 1,
        };
        debug_assert!(
            next > i,
            "value_tokens_to_meta must advance: returned {next} at {i}"
        );
        i = next.max(i + 1);
    }
    groups
}

/// The token ranges of the arithmetic expressions in a `custom` directive's
/// values that are well formed but do not evaluate (division by
/// zero, overflow). Each is a parse error, raised by both trees from this one
/// walk; their values are not emitted (#2806).
pub(super) fn unevaluable_value_expressions<T: TokenView>(
    tokens: &[T],
) -> Vec<std::ops::Range<usize>> {
    value_groups(tokens)
        .into_iter()
        .filter_map(|(start, group)| match group {
            ValueGroup::NoValue {
                end,
                unevaluable: true,
            } => Some(start..end),
            _ => None,
        })
        .collect()
}

/// The diagnostic for an expression from [`unevaluable_value_expressions`] or
/// [`unevaluable_meta_value`], in the style of the amount path's `invalid
/// arithmetic expression in amount`.
///
/// Stricter than Python on overflow: beancount evaluates
/// `79228162514264337593543950335 * 10` to `7.922816251426433759354395034E+29`
/// with its arbitrary-precision `Decimal`. `rust_decimal` cannot hold that
/// value (its coefficient ceiling, see AGENTS.md "Decimal Precision"), so we
/// report the expression rather than load a different number. Division by
/// zero is no deviation: beancount 3.2.3 crashes on it (exit 139). Pinned by
/// `test_meta_value_reports_an_overflowing_expression`.
pub(super) fn unevaluable_value_error(what: &str, span: Span) -> crate::ParseError {
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError(format!(
            "invalid arithmetic expression in {what} value (overflow, division by zero, \
             or an inexact quotient below 1e-28)"
        )),
        span,
    )
}

/// A token as a kind and its source text, for the header-line token buffers
/// (`(kind, range)` pairs over the source) that the value readers take.
struct TextToken<'a> {
    kind: crate::SyntaxKind,
    text: &'a str,
}

impl TokenView for TextToken<'_> {
    fn kind(&self) -> crate::SyntaxKind {
        self.kind
    }
    fn text(&self) -> &str {
        self.text
    }
}

/// The byte range of a `key: value` value that is a well-formed arithmetic
/// expression with no value (division by zero, overflow), or `None`.
/// `tokens` are one line's `(kind, range)` pairs over `src`, from the key on:
/// a metadata line, or a `pushmeta` header.
///
/// The one check behind both, reading the value region the way
/// [`meta_value_from_tokens`] does (through [`cost_region_read`]), so a
/// metadata line and a `pushmeta` cannot disagree on which values are errors.
/// They used to: `pushmeta kk: 1/0` was reported and `kk: 1/0` loaded as `1`
/// (#2806, #2812). The range runs from the first value token to the last one
/// on the line, so it covers the expression and its currency.
pub(super) fn unevaluable_meta_value(
    tokens: &[(crate::SyntaxKind, std::ops::Range<usize>)],
    src: &str,
) -> Option<std::ops::Range<usize>> {
    let key = tokens
        .iter()
        .position(|(k, _)| *k == crate::SyntaxKind::META_KEY)?;
    let value: Vec<(crate::SyntaxKind, std::ops::Range<usize>)> = tokens[key + 1..]
        .iter()
        .filter(|(k, _)| !is_trivia_kind(*k))
        .cloned()
        .collect();
    let views: Vec<TextToken<'_>> = value
        .iter()
        .map(|(kind, range)| TextToken {
            kind: *kind,
            text: src.get(range.clone()).unwrap_or_default(),
        })
        .collect();
    if cost_region_read(&views) != Some(ArithRead::NoValue) {
        return None;
    }
    Some(value.first()?.1.start..value.last()?.1.end)
}

/// Discriminate the value tokens under a `META_ENTRY` into a typed
/// [`MetaValue`] — thin wrapper over the shared [`meta_value_from_tokens`].
/// The raw-token sibling is [`value_tokens_to_meta`]; keep the two in sync.
fn meta_value_from_entry(entry: &MetaEntry) -> MetaValue {
    meta_value_from_tokens(
        entry
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token),
    )
}

/// Derive the typed [`MetaValue`] from a `META_ENTRY` node's direct child
/// tokens. The single source of truth for BOTH walkers (red
/// [`meta_value_from_entry`], green `meta_value`).
///
/// Matches the legacy parser's preference order: string > number/amount >
/// date > account > currency > bool > tag/link > none, where each candidate
/// is the FIRST token of its kind and a type that's present-but-unparsable
/// (a malformed string, an over-precision number, a bad date) falls through
/// to the next.
///
/// A `MINUS` token after the `META_KEY` and before the first `NUMBER`
/// negates the number (legacy `parse_signed_number`, e.g. `precision: -1`);
/// a first `CURRENCY` anywhere alongside the number makes it an `Amount`
/// (legacy priority where `parse_amount` runs before `parse_signed_number`).
pub(super) fn meta_value_from_tokens(tokens: impl Iterator<Item = impl TokenView>) -> MetaValue {
    use crate::SyntaxKind as K;
    // Materialized so the arithmetic evaluator can look at the value region as
    // a slice. `key: 2 * 3` is 6 in beancount and was 2 here — the same
    // first-NUMBER truncation as the cost spec in #1939, in a third place
    // (#1944).
    let toks: Vec<_> = tokens.collect();
    let mut string_t: Option<String> = None;
    let mut number_t: Option<String> = None;
    let mut currency_t: Option<String> = None;
    let mut date_t: Option<String> = None;
    let mut account_t: Option<String> = None;
    let mut bool_v: Option<bool> = None;
    let mut tag_link: Option<MetaValue> = None;
    let mut past_key = false;
    let mut minus = false;
    let mut minus_decided = false;

    for t in &toks {
        let kind = t.kind();
        // First-of-kind value tokens (the `first_token` accessor semantics).
        match kind {
            K::STRING if string_t.is_none() => string_t = Some(t.text().to_string()),
            K::NUMBER if number_t.is_none() => number_t = Some(t.text().to_string()),
            K::CURRENCY if currency_t.is_none() => currency_t = Some(t.text().to_string()),
            K::DATE if date_t.is_none() => date_t = Some(t.text().to_string()),
            K::ACCOUNT if account_t.is_none() => account_t = Some(t.text().to_string()),
            K::BOOL_TRUE if bool_v.is_none() => bool_v = Some(true),
            K::BOOL_FALSE if bool_v.is_none() => bool_v = Some(false),
            K::TAG if tag_link.is_none() => {
                tag_link = Some(MetaValue::Tag(Tag::new(t.text().trim_start_matches('#'))));
            }
            K::LINK if tag_link.is_none() => {
                tag_link = Some(MetaValue::Link(Link::new(t.text().trim_start_matches('^'))));
            }
            _ => {}
        }
        if past_key && !minus_decided {
            match kind {
                K::MINUS => {
                    minus = true;
                    minus_decided = true;
                }
                K::NUMBER => minus_decided = true,
                _ => {}
            }
        }
        // Gates the sign machine so a MINUS in or before the key position is
        // not read as a value's sign. No input reachable through the parser
        // exercises it: the key is always the first meaningful token, and the
        // malformed shapes that would put a MINUS ahead of it (`- key: 42`,
        // `-key: 42`, `key- : 42`) yield no metadata entry at all. Kept as a
        // guard on the token contract rather than deleted, since this helper
        // is shared with the green walker and takes whatever tokens it is
        // handed. Flipping this comparison survives mutation testing for the
        // same reason -- recorded so the next reader does not hunt for a test.
        if kind == K::META_KEY {
            past_key = true;
        }
    }

    if let Some(s) = string_t
        && let Some(decoded) = decode_string_token(&s)
    {
        return MetaValue::String(decoded);
    }
    // Arithmetic override, mirroring the cost-spec fix. Only when the value
    // region really is an expression; a bare number keeps the latch above and
    // its `Int` vs `Number` discrimination, which is archived (cache v11) and
    // must not shift for ordinary metadata.
    //
    // The sign is NOT reapplied on this path: a leading MINUS is part of the
    // expression the evaluator already consumed, so `minus` would double it.
    let value_region: Vec<&_> = toks
        .iter()
        .skip_while(|t| t.kind() != K::META_KEY)
        .filter(|t| !is_trivia_kind(t.kind()) && t.kind() != K::META_KEY)
        .collect();
    let read = cost_region_read(&value_region);
    // A well-formed expression with no value (`kk: 1/0`, an overflow) has no
    // value at all, not the first number of the expression, which is what it
    // used to load as. The error is raised by `unevaluable_meta_value`, from
    // the same read (#2806).
    if read == Some(ArithRead::NoValue) {
        return MetaValue::None;
    }
    if let Some(ArithRead::Value(dec)) = read {
        if let Some(c) = currency_t {
            return MetaValue::Amount(Amount::new(dec, Currency::new(&c)));
        }
        // Render the RESULT to decide Int vs Number, so `2 * 3` is Int(6) —
        // what beancount reports — rather than inheriting the first operand's
        // spelling.
        return number_meta_value(&dec.to_string(), dec);
    }
    if let Some(nt) = number_t
        && let Some(mut dec) = parse_decimal_token(&nt)
    {
        if minus {
            dec = -dec;
        }
        if let Some(c) = currency_t {
            return MetaValue::Amount(Amount::new(dec, Currency::new(&c)));
        }
        return number_meta_value(&nt, dec);
    }
    if let Some(dt) = date_t
        && let Some(date) = parse_date_token(&dt)
    {
        return MetaValue::Date(date);
    }
    if let Some(a) = account_t {
        return MetaValue::Account(Account::new(&a));
    }
    if let Some(c) = currency_t {
        return MetaValue::Currency(Currency::new(&c));
    }
    if let Some(b) = bool_v {
        return MetaValue::Bool(b);
    }
    if let Some(tl) = tag_link {
        return tl;
    }
    MetaValue::None
}

// ---- Inherited state (pushtag/poptag/pushmeta/popmeta) ---------

/// Merge active pushed-tag and pushed-meta state into a freshly
/// converted directive's value.
///
/// Pushed tags apply to every directive that carries tags: `Transaction`,
/// `Document` and `Note`, as beancount 3 does (its grammar unions the tag
/// stack into each of those three). They used to apply to transactions only
/// (#2544). The tags are a [`TagSet`], so a pushed tag the line already
/// wrote is not added twice (#2545).
///
/// Pushed metadata applies to transactions only, as in beancount 3, whose
/// grammar reads its meta stack in `transaction()` and nowhere else; an
/// `open`, `balance`, `note` or any other directive gets none (#2812). A key
/// the transaction writes itself wins over a pushed one, as beancount
/// applies the pushed values first and its explicit metadata on top (#2812;
/// rledger used to let the push override it). Postings get no pushed
/// metadata in either.
///
/// The meta stack is a `Vec` (not a map) to preserve shadow/pop
/// semantics - `pushmeta x: 1; pushmeta x: 2; popmeta x` should
/// leave `x = 1` active, which a map-replacing-on-insert can't
/// express. Iterating in push order means the latest push of a key
/// wins over earlier ones, as beancount's `value_list[-1]`.
fn apply_inherited_state(
    value: &mut Directive,
    tag_stack: &[(Tag, Span)],
    meta_stack: &[(String, MetaValue, Span)],
) {
    let tags = match value {
        Directive::Transaction(d) => Some(&mut d.tags),
        Directive::Document(d) => Some(&mut d.tags),
        Directive::Note(d) => Some(&mut d.tags),
        Directive::Balance(_)
        | Directive::Open(_)
        | Directive::Close(_)
        | Directive::Commodity(_)
        | Directive::Pad(_)
        | Directive::Event(_)
        | Directive::Query(_)
        | Directive::Price(_)
        | Directive::Custom(_) => None,
    };
    if let Some(tags) = tags {
        tags.extend(tag_stack.iter().map(|(tag, _)| tag.clone()));
    }
    if meta_stack.is_empty() {
        return;
    }
    let Directive::Transaction(txn) = value else {
        return;
    };
    // beancount's order: the pushed keys first (each where it was first
    // pushed, holding its latest value), then the written ones; a key the
    // transaction writes itself keeps the pushed position and the written
    // value. A builder resolves exactly that, since a repeated key keeps its
    // first position and its last value, and it keeps a long stack or a long
    // transaction from going quadratic.
    let mut meta = MetadataBuilder::new();
    for (k, v, _) in meta_stack {
        meta.push(k.as_str(), v.clone());
    }
    for (k, v) in std::mem::take(&mut txn.meta).into_inner() {
        meta.push(k, v);
    }
    txn.meta = meta.build().into();
}

/// The value a `pushmeta` directive pushes, or `None` when it pushes nothing.
///
/// Read by [`meta_value_from_tokens`], the metadata converter, since a
/// `pushmeta` value follows the metadata grammar (`key_value_value`). It used
/// to be read by the custom-value walk instead, which drifted: `pushmeta kk:
/// (1+2)` pushed `1`, and `"a\"b"` kept its escape (#2812).
///
/// A line with any syntax error (a malformed expression such as `pushmeta kk:
/// 1 + TRUE` or `10 *`, or anything left over after the value, such as
/// `pushmeta kk: "v" !` or `1 2`) pushes nothing, as in beancount, whose
/// grammar rejects the directive; its `popmeta` then
/// reports the absent key, as beancount does. The syntax error itself comes
/// from the header-line check. An expression with no value (`1/0`) is
/// grammatical, so it pushes the key with no value, the same `MetaValue` a
/// metadata line gets (the error comes from [`unevaluable_meta_value`]).
fn pushmeta_value(node: &crate::SyntaxNode) -> Option<MetaValue> {
    let tokens: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .collect();
    let value_region: Vec<&crate::SyntaxToken> = tokens
        .iter()
        .skip_while(|t| t.kind() != crate::SyntaxKind::META_KEY)
        .filter(|t| !is_trivia_kind(t.kind()) && t.kind() != crate::SyntaxKind::META_KEY)
        .collect();
    if cost_region_read(&value_region) == Some(ArithRead::Malformed) {
        return None;
    }
    // Any syntax error on the line pushes nothing, as in beancount, so the
    // matching `popmeta` then reports the absent key. Ask the same rule that
    // reports the error, in node-relative offsets over the node's own text.
    let text = node.text().to_string();
    let start = usize::from(node.text_range().start());
    let mut end = text.len();
    let mut header = Vec::new();
    for t in &tokens {
        let range =
            usize::from(t.text_range().start()) - start..usize::from(t.text_range().end()) - start;
        // Leading blank lines belong to the node too: skip them before
        // looking for the NEWLINE that ends the line, as the header check does.
        if header.is_empty() && (is_trivia_kind(t.kind()) || t.kind() == crate::SyntaxKind::BOM) {
            continue;
        }
        if t.kind() == crate::SyntaxKind::NEWLINE {
            end = range.start;
            break;
        }
        header.push((t.kind(), range));
    }
    if super::directive_header::first_header_defect(node.kind(), &header, end, &text).is_some() {
        return None;
    }
    // A date that is not a real calendar date (`pushmeta kk: 2024-02-30`) is
    // a lexer error in beancount, which pushes nothing (#2811).
    if invalid_value_date(&header, &text, false).is_some() {
        return None;
    }
    Some(meta_value_from_tokens(tokens.into_iter()))
}

// ---- ParseResult.comments --------------------------------------

/// Comment-like syntax kinds that the legacy parser surfaces as
/// `ParseResult.comments` entries when they appear at the top
/// level (outside any directive's content).
pub(super) const fn is_comment_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::COMMENT
            | crate::SyntaxKind::PERCENT_COMMENT
            | crate::SyntaxKind::SHEBANG
            | crate::SyntaxKind::EMACS_DIRECTIVE
    )
}

/// Whether the first non-trivia token of a top-level `ERROR_NODE` line
/// makes it an org-mode section marker: a `STAR` at column 0 of the source,
/// with nothing before it on its line.
///
/// Shared by the error-silencing and the section-comment walkers on both
/// paths (`error_node_check` / `section_marker_check` here,
/// `tl_error_node_check` / `tl_section_marker_check` in `green.rs`), so
/// the four agree on which lines are headings. An INDENTED `*` line is
/// not a heading (beancount reports a syntax error: `unexpected INDENT`,
/// or `unexpected ASTERISK` after a directive), so it is an ordinary error
/// line (#2783); silencing it as a heading let a `"` on it swallow the
/// following directives with no diagnostic. A `*` after a BOM is not one
/// either: beancount rejects the BOM (`Invalid token`), as rledger does
/// before a directive. `offset` indexes `stripped`, the post-BOM-strip
/// source, so a file's single leading BOM is already gone.
///
/// A bare `*` line, with its line ending (or the end of the source) right
/// after the `*`, is not a heading either: beancount's `^\*/.` needs one more
/// character on the line (a `\r` counts), so it reports `unexpected ASTERISK`
/// there, and the line is an ordinary error line here (#2779). That rule is
/// [`crate::logos_lexer::beancount_ignores_line`], shared with the lexer.
///
/// The lexer has its own, deliberately broader, rule for the same line:
/// `TokenIter`'s `Token::Star` arm in `logos_lexer.rs` (#2778) skips the
/// rest of any line-start `*` line (BOMs included) without lexing it.
/// The two may only disagree in the SAFE direction: a line the lexer
/// skipped can still be reported here, but nothing is silenced here
/// unless the lexer skipped it, so a silenced line can never swallow the
/// lines after it.
pub(super) fn is_section_marker(kind: crate::SyntaxKind, stripped: &str, offset: usize) -> bool {
    kind == crate::SyntaxKind::STAR
        && (offset == 0 || stripped.as_bytes().get(offset - 1) == Some(&b'\n'))
        && stripped
            .get(offset..)
            .is_some_and(crate::logos_lexer::beancount_ignores_line)
}

/// Output of the fused top-level pass [`walk_top_level_once`].
pub(super) struct TopLevelWalkResult {
    pub(super) errors: Vec<crate::ParseError>,
    pub(super) section_marker_comments: Vec<Spanned<String>>,
}

/// Single walk over `source_file`'s direct children that runs
/// every per-directive diagnostic in one pass, replacing five
/// separate `source_file.syntax().children()` traversals
/// (`extract_error_node_errors`, `extract_transaction_body_errors`,
/// `extract_indented_directive_errors`, `extract_custom_value_errors`,
/// `extract_section_marker_comments`). Each former pass re-walked
/// the top-level child list and materialized a fresh red node per
/// directive; on a large ledger that is 5·O(N) red-node churn for
/// work that is naturally per-child. The checks are independent and
/// all diagnostics are span-sorted by the caller, so fusing them is
/// order-preserving.
fn walk_top_level_once(
    source_file: &SourceFile,
    stripped: &str,
    bom_offset: u32,
) -> TopLevelWalkResult {
    let mut errors: Vec<crate::ParseError> = Vec::new();
    let mut section_marker_comments: Vec<Spanned<String>> = Vec::new();
    for child in source_file.syntax().children() {
        let kind = child.kind();
        // Applies to every recognized directive node (incl. CUSTOM).
        if ast::Directive::can_cast(kind) {
            indented_directive_check(&child, stripped, bom_offset, &mut errors);
        }
        match kind {
            crate::SyntaxKind::CUSTOM_DIRECTIVE => {
                custom_value_check(&child, bom_offset, &mut errors);
                value_expression_check(&child, "custom", bom_offset, &mut errors);
            }
            crate::SyntaxKind::TRANSACTION => {
                transaction_header_check(&child, stripped, bom_offset, &mut errors);
                transaction_body_check(&child, bom_offset, &mut errors);
            }
            crate::SyntaxKind::ERROR_NODE => {
                error_node_check(&child, stripped, bom_offset, &mut errors);
                section_marker_check(&child, stripped, bom_offset, &mut section_marker_comments);
            }
            _ => {}
        }
    }
    TopLevelWalkResult {
        errors,
        section_marker_comments,
    }
}

/// A `^link` is not a valid metadata VALUE (#1954).
///
/// beancount's grammar has no production for it — `ref: ^inv-1` fails with
/// `syntax error, unexpected LINK, expecting end of file or EOL` — while a
/// `#tag` in the same position is perfectly valid there. We accepted both.
///
/// Deliberately asymmetric, and that asymmetry is the whole point: rejecting
/// TAG here as well would break input beancount accepts, which is the mistake
/// #1953 avoided in the mirror-image case. Tags and links lex as sibling kinds
/// and are handled as a pair almost everywhere in this file, so the pairing is
/// the natural thing to reach for and the wrong thing to do.
///
/// Scoped to `META_ENTRY` nodes. A link on a TRANSACTION (`* "x" ^lnk`) is a
/// direct child of the transaction, not of a metadata entry, so it is
/// untouched — as it must be, that being the one place links belong.
///
/// NOT extended to `custom` / `pushmeta` values, which run through
/// `value_tokens_to_meta` rather than this path. beancount rejects BOTH a tag
/// and a link there, so it is a different rule needing its own evidence;
/// filed separately rather than folded in here.
fn extract_link_metadata_value_errors(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for entry in source_file.syntax().descendants() {
        if entry.kind() != crate::SyntaxKind::META_ENTRY {
            continue;
        }
        for el in entry.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            if t.kind() != crate::SyntaxKind::LINK {
                continue;
            }
            let range = t.text_range();
            let off = bom_offset as usize;
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(format!(
                    "a link ({}) is not a valid metadata value; beancount \
                     accepts a tag here but not a link",
                    t.text()
                )),
                Span::new(
                    usize::from(range.start()) + off,
                    usize::from(range.end()) + off,
                ),
            ));
        }
    }
    out
}

/// Walk every `COST_SPEC` node in the tree and emit a
/// `SyntaxError("unclosed cost specification: missing '}'")` for
/// any spec whose opener (`{`, `{{`, or `{#`) doesn't have a
/// matching closer at the spec's depth-0. Mirrors the legacy
/// parser's deferred-error emission at `parser.rs:705-707` so a
/// `10 AAPL {150 USD\n` posting or an EOF-truncated cost block
/// surfaces a diagnostic instead of silently producing a half-
/// built cost spec.
/// Tags and links are not valid `custom` or `pushmeta` VALUES (#1958).
///
/// Two different rules, and conflating them is the trap here:
///
/// | position          | `#tag`   | `^link`  |
/// |-------------------|----------|----------|
/// | metadata value    | valid    | rejected |
/// | `pushmeta k: ...` | valid    | rejected |
/// | `custom "t" ...`  | rejected | rejected |
///
/// `pushmeta` follows the METADATA rule - it pushes a metadata key/value, so a
/// tag is fine there and only a link is not. `custom` is stricter than both and
/// takes neither. Checked against beancount per position, each with a control
/// on the same directive.
///
/// This is why the check cannot live inside `value_tokens_to_meta`, which both
/// callers share: one rule in the shared helper would either let a tag through
/// in `custom` or wrongly reject one in `pushmeta`. It is the same shape as
/// #1953 (`note`/`document` DO take both) and #1954 (a tag is valid where a
/// link is not) - three times now the right answer has split a pair that lexes
/// and reads as one.
fn extract_custom_pushmeta_taglink_errors(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    use crate::SyntaxKind as K;
    let mut out = Vec::new();
    for node in source_file.syntax().descendants() {
        let (reject_tag, what) = match node.kind() {
            K::CUSTOM_DIRECTIVE => (true, "custom"),
            K::PUSHMETA_DIRECTIVE => (false, "pushmeta"),
            _ => continue,
        };
        for el in node.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            let kind = t.kind();
            let bad = match kind {
                K::LINK => true,
                K::TAG => reject_tag,
                _ => false,
            };
            if !bad {
                continue;
            }
            let noun = if kind == K::TAG { "tag" } else { "link" };
            let range = t.text_range();
            let off = bom_offset as usize;
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(format!(
                    "a {noun} ({}) is not a valid {what} value",
                    t.text()
                )),
                Span::new(
                    usize::from(range.start()) + off,
                    usize::from(range.end()) + off,
                ),
            ));
        }
    }
    out
}

fn extract_unclosed_cost_brace_errors(
    source_file: &SourceFile,
    stripped: &str,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for cs in source_file.syntax().descendants() {
        if cs.kind() != crate::SyntaxKind::COST_SPEC {
            continue;
        }
        let mut has_opener = false;
        let mut has_closer = false;
        for el in cs.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            match t.kind() {
                crate::SyntaxKind::L_BRACE
                | crate::SyntaxKind::L_DOUBLE_BRACE
                | crate::SyntaxKind::L_BRACE_HASH => has_opener = true,
                crate::SyntaxKind::R_BRACE | crate::SyntaxKind::R_DOUBLE_BRACE => has_closer = true,
                _ => {}
            }
        }
        if has_opener && !has_closer {
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "unclosed cost specification: missing '}'".to_string(),
                ),
                node_span(&cs, bom_offset),
            ));
            // An unclosed spec has no meaningful component list; reporting a
            // shape defect on top would just be noise about the truncation.
            continue;
        }

        // Component-list shape (#2008 cases 1 and 2). Fused into this walk
        // rather than given its own: `descendants()` allocates a red node per
        // node, which is why this scan already sits behind a `contains('{')`
        // guard, and a second identical pass would double a cost the codebase
        // deliberately profiled down.
        let tokens = cs
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .map(|t| {
                let r = t.text_range();
                (t.kind(), usize::from(r.start())..usize::from(r.end()))
            });
        if let Some((defect, range)) = super::cost_spec_shape::first_cost_spec_defect(tokens) {
            // `get` rather than indexing: a non-char-boundary range must not
            // panic the parser.
            let message = match stripped.get(range.clone()) {
                Some(text) => super::cost_spec_shape::cost_defect_message(defect, text),
                None => format!(
                    "malformed cost specification at bytes {}..{} ({defect:?})",
                    range.start, range.end
                ),
            };
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(message),
                Span::new(
                    range.start + bom_offset as usize,
                    range.end + bom_offset as usize,
                ),
            ));
        }
    }
    out
}

/// Walk every top-level directive in `source_file` and emit a
/// `SyntaxError("top-level directive must start at column 0")`
/// for any whose content (first non-trivia token) starts at a
/// non-zero column. Per the Beancount language spec, top-level
/// directives are required to begin at column 0; indentation is
/// reserved for postings and metadata inside a transaction body.
///
/// The CST grammar happily accepts an indented `open` / `balance`
/// / etc., which is why this surfaces at converter level instead
/// of as a lex/parse error.
fn indented_directive_check(
    child: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    // Caller dispatches: `child` is a recognized directive node.
    // Find the directive's content start - the first non-
    // trivia token. Leading WHITESPACE / NEWLINE / COMMENT
    // can land inside the directive node per the Directive-
    // Terminator Rule's inter-directive trivia attachment.
    let Some(content) = child
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .find(|t| !is_trivia_kind(t.kind()))
    else {
        return;
    };
    let content_start: usize = u32::from(content.text_range().start()) as usize;
    // Column = offset since the last NEWLINE in the source,
    // or since byte 0 if this is the first line. >0 means
    // the directive's first content token has leading WS on
    // its own line - that's the indent error.
    // Find the line start by scanning the BYTES before `content_start`, not by
    // slicing the `str`. On malformed/error-recovered input a token's start
    // offset can land inside a multi-byte UTF-8 char, and
    // `stripped[..content_start]` would then panic ("not a char boundary").
    // Byte slicing is boundary-agnostic, and a newline (`\n`) is always a single
    // ASCII byte, so the found position is a valid offset. `.get(..)` also guards
    // a (theoretical) out-of-bounds offset. Regression: fuzz_regressions.rs.
    let line_start = stripped
        .as_bytes()
        .get(..content_start)
        .and_then(|bytes| bytes.iter().rposition(|&b| b == b'\n'))
        .map_or(0, |nl| nl + 1);
    if content_start > line_start {
        let end: u32 = content.text_range().end().into();
        let span = Span::new(
            (line_start as u32 + bom_offset) as usize,
            (end + bom_offset) as usize,
        );
        out.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "top-level directive must start at column 0".to_string(),
            ),
            span,
        ));
    }
}

/// Walk each `CUSTOM` directive and emit a `SyntaxError` for
/// every bare `CURRENCY` token in the value position (a CURRENCY
/// not paired with a preceding NUMBER as an Amount).
///
/// Per the Beancount language spec, custom-directive values are
/// limited to string / date / decimal / amount / boolean -
/// `bean-check` rejects a bare currency literal with a syntax
/// error. Rustledger's `extract_custom_values` has historically
/// been more lenient, accepting ACCOUNT / TAG / LINK in value
/// position too; we keep that extension (it's covered by the
/// existing `test_parse_custom_directive` integration test) but
/// surface a diagnostic for the bare-CURRENCY case so the
/// compat metric reflects bean-check's exit-code rejection on
/// shapes like `custom "x" 10 USD "y" NZD …`.
fn custom_value_check(
    child: &crate::SyntaxNode,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    // Caller dispatches: `child` is a CUSTOM_DIRECTIVE.
    {
        // Collect non-trivia tokens, then skip past the
        // directive's header: DATE, CUSTOM_KW, and the first
        // STRING (the custom-type name). Everything after that
        // is values.
        let raw: Vec<crate::SyntaxToken> = child
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| !is_trivia_kind(t.kind()))
            .collect();
        let mut seen_type_string = false;
        let mut i = 0;
        while i < raw.len() {
            let t = &raw[i];
            if !seen_type_string {
                if t.kind() == crate::SyntaxKind::STRING {
                    seen_type_string = true;
                }
                i += 1;
                continue;
            }
            if t.kind() == crate::SyntaxKind::CURRENCY {
                // Only flag BARE CURRENCY - one that doesn't
                // follow a NUMBER (Amount-pairing). The Amount
                // pairing is handled by `extract_custom_values`
                // via i+1 lookahead, so a CURRENCY that's NOT
                // preceded by a NUMBER at i-1 is bare. A `)` closes an
                // expression that pairs the same way: `(1+2) USD` (#2806).
                let preceded_by_number = i > 0
                    && matches!(
                        raw[i - 1].kind(),
                        crate::SyntaxKind::NUMBER | crate::SyntaxKind::R_PAREN
                    );
                if !preceded_by_number {
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    let span =
                        Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                    out.push(crate::ParseError::new(
                        crate::ParseErrorKind::SyntaxError(
                            "bare currency literal is not a valid custom directive value"
                                .to_string(),
                        ),
                        span,
                    ));
                }
            }
            i += 1;
        }
    }
}

/// Report each arithmetic expression in a `custom` value that is well formed
/// but does not evaluate, such as `10/0 USD` (#2806). The
/// expressions are found by the shared [`unevaluable_value_expressions`],
/// which the green `tl_value_expression_check` calls too; the span covers the
/// expression and its currency, as the amount path's diagnostic does.
fn value_expression_check(
    child: &crate::SyntaxNode,
    what: &str,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    let raw: Vec<crate::SyntaxToken> = child
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_value_walk_trivia(t.kind()))
        .collect();
    for range in unevaluable_value_expressions(&raw) {
        let start: u32 = raw[range.start].text_range().start().into();
        let end: u32 = raw[range.end - 1].text_range().end().into();
        out.push(unevaluable_value_error(
            what,
            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize),
        ));
    }
}

/// Walk a `TRANSACTION` body and emit a `SyntaxError` for any body
/// line that contains flat catch-all tokens (e.g., an
/// unrecognized identifier where a posting was expected).
/// Matches the legacy parser, which fails its inner posting
/// parser on such lines and recovers by skipping to the next
/// NEWLINE while emitting a `SyntaxError`.
/// The `unexpected input` diagnostic for one catch-all transaction-body line.
///
/// Mirrors `green::unexpected_body_input`; shared by the newline- and
/// EOF-terminated sites so the span rule cannot drift between them.
fn unexpected_body_input(line_start: u32, end: u32, bom_offset: u32) -> crate::ParseError {
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
        Span::new(
            (line_start + bom_offset) as usize,
            (end + bom_offset) as usize,
        ),
    )
}

/// The error for a transaction body line of `#tag` / `^link` tokens that
/// comes after the transaction's first posting (#2575). `tags` is the line's
/// tag and link tokens as written, space-separated.
///
/// Beancount's grammar accepts such a line anywhere in the posting list, but
/// its builder refuses one after the first posting ("Tags or links not allowed
/// after first Posting") and keeps the transaction WITHOUT those tags. rledger
/// does the same: the line draws this error, and the conversion leaves its
/// tags out of the transaction's set (`body_tag_joins_transaction`). Before
/// #2575 rledger silently added them to the transaction, so a file beancount
/// refuses loaded clean, with a tag beancount would not report.
///
/// Shared by the red ([`transaction_body_check`]) and green
/// (`green::tl_transaction_body_check`) body checks, so the two report the
/// same words over the same span.
pub(super) fn tags_after_posting_error(
    tags: &str,
    line_start: usize,
    end: usize,
    bom_offset: u32,
) -> crate::ParseError {
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError(format!(
            "tags and links are not allowed after a transaction's first posting \
             (`{tags}`); write them on the header line or on a line before the first posting"
        )),
        Span::new(line_start + bom_offset as usize, end + bom_offset as usize),
    )
}

/// Whether a `#tag` / `^link` token on a transaction BODY line (outside any
/// posting or metadata node) joins the transaction's tag/link set: only before
/// the first posting (#2575). After it, the line is an error
/// ([`tags_after_posting_error`]) and its tags are dropped, as beancount drops
/// them.
///
/// THE rule, for both conversions (red `convert_transaction`, green
/// `convert_transaction_header`) and both body checks; each walk tracks
/// `posting_seen` and asks here.
pub(super) const fn body_tag_joins_transaction(posting_seen: bool) -> bool {
    !posting_seen
}

/// Tracks where a `TRANSACTION` node's header region ends, one direct-child
/// token at a time.
///
/// A transaction node can open with leading trivia: blank lines and comment
/// lines before it attach inside the node (the Directive-Terminator Rule,
/// `cst::trivia`), so its first token may be a NEWLINE. The header line
/// therefore ends at the first NEWLINE *after* the first non-trivia token, not
/// at the first NEWLINE. Breaking on the first one made the same transaction
/// convert differently depending on what preceded it (#2628): the header-line
/// comment landed in the first posting's `comments` and the deprecated `|`
/// warning was lost, but only after a blank line or a comment.
///
/// THE rule for every walk that splits a transaction into header and body:
/// red `collect_postings_with_comments` and `header_has_pipe`, green
/// `convert_transaction_header`. (The body checks keep their own
/// `saw_header_content` flag, which is the same rule.) "Trivia" is
/// [`is_trivia_kind`], the set `Transaction::header_tokens` skips.
#[derive(Default)]
pub(super) struct HeaderEnd {
    started: bool,
    ended: bool,
}

impl HeaderEnd {
    /// Feed the next direct-child token. Returns `true` while the token is in
    /// the header region (leading trivia, the header line and its terminating
    /// NEWLINE), `false` for every token after it.
    pub(super) fn in_header(&mut self, kind: crate::SyntaxKind) -> bool {
        if self.ended {
            return false;
        }
        if kind == crate::SyntaxKind::NEWLINE {
            self.ended = self.started;
        } else if !is_trivia_kind(kind) {
            self.started = true;
        }
        true
    }

    /// A child node (`POSTING` / `META_ENTRY`) ends the header whatever came
    /// before it.
    pub(super) const fn end(&mut self) {
        self.ended = true;
    }
}

/// Reject transaction headers beancount's grammar refuses (#2008 cases 3, 4,
/// 6, 7). The rule itself lives in [`super::txn_header`] so this and its green
/// mirror (`green::tl_transaction_header_check`) cannot drift; here we only
/// enumerate the header tokens.
///
/// Token enumeration goes through `Transaction::header_tokens`, the same
/// accessor `flag()` / `strings()` / `tags()` use, so "what counts as the
/// header" has one definition.
fn transaction_header_check(
    child: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    let Some(txn) = ast::Transaction::cast(child.clone()) else {
        return;
    };
    let tokens = txn
        .header_tokens()
        .map(|t| {
            let r = t.text_range();
            (t.kind(), usize::from(r.start())..usize::from(r.end()))
        })
        .collect();
    if let Some((defect, range)) = super::txn_header::first_header_defect_in(tokens, stripped) {
        out.push(header_defect_error(defect, &range, stripped, bom_offset));
    }
}

/// Whether `node`'s header line holds an invalid token (`ERROR_TOKEN`). The
/// line is read by `header_line_tokens`, the header walk the header check
/// uses: past the blank and comment lines stored at the start of the node,
/// up to the `NEWLINE` that ends the header. beancount's grammar never reduces
/// such a line to its directive, so a `pushtag`, `poptag`, `pushmeta` or
/// `popmeta` with one changes no state there (`pushtag" #t`, `pushtag #t $x`).
/// An `open` asks `holds_an_invalid_token` instead, as its metadata lines
/// belong to the same statement. Walks GREEN children only.
fn header_has_invalid_token(node: &crate::SyntaxNode) -> bool {
    let mut tokens = Vec::new();
    header_line_tokens(node, &mut tokens);
    tokens
        .iter()
        .any(|(kind, _)| *kind == crate::SyntaxKind::ERROR_TOKEN)
}

/// A directive's header-line tokens into `tokens` (cleared first): its direct
/// tokens from the first content token (past leading trivia) up to the
/// `NEWLINE` that ends the line. Returns where the line's content ends.
/// Walks GREEN children only.
fn header_line_tokens(
    node: &crate::SyntaxNode,
    tokens: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
) -> usize {
    tokens.clear();
    let mut at = usize::from(node.text_range().start());
    let mut end = usize::from(node.text_range().end());
    for child in node.green().children() {
        let rowan::NodeOrToken::Token(t) = child else {
            break;
        };
        let kind = <crate::BeancountLanguage as rowan::Language>::kind_from_raw(t.kind());
        let range = at..at + t.text().len();
        at = range.end;
        if tokens.is_empty() && (is_trivia_kind(kind) || kind == crate::SyntaxKind::BOM) {
            continue;
        }
        if kind == crate::SyntaxKind::NEWLINE {
            end = range.start;
            break;
        }
        tokens.push((kind, range));
    }
    end
}

/// Reject a non-transaction directive header line that beancount's grammar
/// refuses (#2802). The rule lives in [`super::directive_header`]; here we only
/// enumerate the header tokens: the node's direct tokens from its first
/// content token (past leading trivia) up to the `NEWLINE` that ends the line.
/// Metadata lines are `META_ENTRY` child nodes, so the first node ends the
/// header too.
///
/// `prior_error_starts` (sorted, BOM frame) are the errors the tree walks
/// already reported. A directive with one of them anywhere on its header line
/// (an `ERROR_TOKEN`, a mid-line BOM, an indented directive, a bare currency
/// in a custom value, ...) is not checked again, so a problem is reported
/// once, with one exception (`report_defects_before`): when that first error
/// is an invalid token's, a defect BEFORE it is still reported, as beancount
/// reports its grammar error there and the lexer's on top.
///
/// Walks the GREEN children (kind and length, no red-node allocation) into
/// `tokens`, a buffer the caller reuses across directives, so the check costs
/// no allocation per directive.
fn directive_header_check(
    node: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    prior_error_starts: &[usize],
    tokens: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
) -> Option<crate::ParseError> {
    let keyword = super::directive_header::directive_keyword(node.kind())?;
    let end = header_line_tokens(node, tokens);
    let off = bom_offset as usize;
    let from = usize::from(node.text_range().start()) + off;
    let first_after = prior_error_starts.partition_point(|&s| s < from);
    let first_prior = prior_error_starts
        .get(first_after)
        .copied()
        .filter(|&s| s <= end + off);
    let before = report_defects_before(first_prior, tokens, off)?;
    let Some(defect) =
        super::directive_header::first_header_defect(node.kind(), tokens, end, stripped)
            .filter(|d| d.range.start + off < before)
    else {
        // A value date that is not a real calendar date (`custom "x"
        // 2024-02-30`) is reported by `report_invalid_dates`, for every line.
        // A grammatical `pushmeta` value can still be an expression with no
        // value (`pushmeta kk: 1/0`): the same check, and the same error, as a
        // metadata line (#2812).
        if node.kind() != crate::SyntaxKind::PUSHMETA_DIRECTIVE || first_prior.is_some() {
            return None;
        }
        let range = unevaluable_meta_value(tokens, stripped)?;
        return Some(unevaluable_value_error(
            "pushmeta",
            Span::new(range.start + off, range.end + off),
        ));
    };
    let text = stripped.get(defect.range.clone()).unwrap_or_default();
    Some(crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError(super::directive_header::defect_message(
            &format!("the {keyword} directive"),
            &defect,
            text,
        )),
        Span::new(defect.range.start + off, defect.range.end + off),
    ))
}

/// How far a line check may still report the defect it finds, given
/// `first_prior`, the first error the tree walks already reported on the line
/// (BOM frame), and the line's `tokens` (CST frame, `off` the BOM offset).
///
/// No prior error: anywhere (`usize::MAX`). A prior error at one of the line's
/// `ERROR_TOKEN`s, the lexer's own `Invalid token` error: only before it.
/// beancount's lexer reports every invalid token whatever its grammar does, so
/// when its grammar fails at a readable token first (`pushtag #$t`, where it
/// expects a tag at the `#`), both are reported; when the invalid token comes
/// first, the grammar never reaches the rest of the line. Any other prior
/// error: `None`, the line is not checked again.
fn report_defects_before(
    first_prior: Option<usize>,
    tokens: &[(crate::SyntaxKind, std::ops::Range<usize>)],
    off: usize,
) -> Option<usize> {
    let Some(at) = first_prior else {
        return Some(usize::MAX);
    };
    tokens
        .iter()
        .any(|(k, r)| *k == crate::SyntaxKind::ERROR_TOKEN && r.start + off == at)
        .then_some(at)
}

/// Reject a metadata line that beancount's grammar refuses (#2802, stage 2):
/// the `META_ENTRY` children of `node`, and those of its `POSTING` children.
/// The rule lives in [`super::directive_header::first_meta_defect`]; here we
/// only enumerate each line's tokens.
///
/// The metadata converter (`meta_value_from_tokens`) takes the first value
/// token of each kind and ignores the rest, so `kk: "v" !` loaded as `"v"` and
/// `rledger format` deleted the `!`.
///
/// A line that already has an error on it (`prior_error_starts`, BOM frame, or
/// one pushed for this directive since `errors_before`) is not checked again,
/// so a problem is reported once. Like the header check, it reports and does
/// not drop: the directive still loads. Walks GREEN children only, from the
/// shared directive loop, so the green and red paths cannot disagree.
fn meta_entry_check(
    node: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    prior_error_starts: &[usize],
    errors_before: usize,
    errors: &mut Vec<crate::ParseError>,
    tokens: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
) {
    use crate::SyntaxKind as K;
    let kind_of = <crate::BeancountLanguage as rowan::Language>::kind_from_raw;
    let mut ctx = MetaCheck {
        stripped,
        off: bom_offset as usize,
        prior_error_starts,
        errors_before,
        errors,
        tokens,
    };
    let mut at = usize::from(node.text_range().start());
    for child in node.green().children() {
        let child_start = at;
        at += green_len(child);
        let rowan::NodeOrToken::Node(n) = child else {
            continue;
        };
        match kind_of(n.kind()) {
            K::META_ENTRY => ctx.line(n, child_start),
            // Posting-attached metadata is a child of its `POSTING`.
            K::POSTING => {
                let mut p = child_start;
                for part in n.children() {
                    let part_start = p;
                    p += green_len(part);
                    if let rowan::NodeOrToken::Node(m) = part
                        && kind_of(m.kind()) == K::META_ENTRY
                    {
                        ctx.line(m, part_start);
                    }
                }
            }
            _ => {}
        }
    }
}

/// A green child's length in bytes.
fn green_len(child: rowan::NodeOrToken<&rowan::GreenNodeData, &rowan::GreenTokenData>) -> usize {
    match child {
        rowan::NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
        rowan::NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
    }
}

/// [`meta_entry_check`]'s state, shared by every line of one directive.
struct MetaCheck<'a> {
    stripped: &'a str,
    off: usize,
    prior_error_starts: &'a [usize],
    errors_before: usize,
    errors: &'a mut Vec<crate::ParseError>,
    tokens: &'a mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
}

impl MetaCheck<'_> {
    /// Check one `META_ENTRY` starting at byte `start` (CST frame).
    fn line(&mut self, entry: &rowan::GreenNodeData, start: usize) {
        use crate::SyntaxKind as K;
        let kind_of = <crate::BeancountLanguage as rowan::Language>::kind_from_raw;
        self.tokens.clear();
        let mut p = start;
        let mut end = start + u32::from(entry.text_len()) as usize;
        for part in entry.children() {
            let rowan::NodeOrToken::Token(t) = part else {
                break;
            };
            let kind = kind_of(t.kind());
            let range = p..p + t.text().len();
            p = range.end;
            if self.tokens.is_empty() && (is_trivia_kind(kind) || kind == K::BOM) {
                continue;
            }
            if kind == K::NEWLINE {
                end = range.start;
                break;
            }
            self.tokens.push((kind, range));
        }
        let off = self.off;
        let (from, to) = (start + off, end + off);
        let first_after = self.prior_error_starts.partition_point(|&s| s < from);
        let first_prior = self
            .prior_error_starts
            .get(first_after)
            .copied()
            .filter(|&s| s <= to);
        if self.errors[self.errors_before..]
            .iter()
            .any(|e| (from..=to).contains(&e.span.start))
        {
            return;
        }
        let Some(before) = report_defects_before(first_prior, self.tokens, off) else {
            return;
        };
        let Some(defect) =
            super::directive_header::first_meta_defect(self.tokens, end, self.stripped)
                .filter(|d| d.range.start + off < before)
        else {
            // A date that is not a real calendar date (`kk: 2024-02-30`) is
            // reported by `report_invalid_dates`, for every line.
            // Grammatical, but an expression with no value (`kk: 1/0`) is
            // still an error, from the check `pushmeta` uses too.
            if first_prior.is_none()
                && let Some(range) = unevaluable_meta_value(self.tokens, self.stripped)
            {
                self.errors.push(unevaluable_value_error(
                    "metadata",
                    Span::new(range.start + off, range.end + off),
                ));
            }
            return;
        };
        let text = self.stripped.get(defect.range.clone()).unwrap_or_default();
        self.errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(super::directive_header::defect_message(
                "a metadata line",
                &defect,
                text,
            )),
            Span::new(defect.range.start + off, defect.range.end + off),
        ));
    }
}

/// Check each posting line against beancount's posting rule (#2802, stage 3;
/// the rule is [`super::directive_header::first_posting_defect`]).
///
/// The posting converter reads its flag, account and `AMOUNT`, `COST_SPEC`
/// and `PRICE_ANNOTATION` children and nothing else, so a token with no place
/// in a posting was dropped in silence: `Assets:A ! 1 USD`, `1 USD %`, or a
/// second cost spec loaded clean, and `rledger format` deleted the stray
/// text. The posting is still KEPT, as a directive with a stray character on
/// its header is (#2805): the error is reported, nothing cascades.
///
/// A posting that already has an error anywhere on it (`5 USD + 3 USD`'s
/// trailing amount, a cost-spec shape error, an `ERROR_TOKEN`) is not
/// reported twice.
///
/// Runs from the shared directive loop over GREEN children, so the green and
/// red parse paths cannot disagree on it.
fn posting_line_check(
    node: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    prior_error_starts: &[usize],
    errors_before: usize,
    errors: &mut Vec<crate::ParseError>,
    tokens: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
) {
    use crate::SyntaxKind as K;
    let kind_of = <crate::BeancountLanguage as rowan::Language>::kind_from_raw;
    let off = bom_offset as usize;
    let mut at = usize::from(node.text_range().start());
    for child in node.green().children() {
        let posting_start = at;
        at += match child {
            rowan::NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            rowan::NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        };
        let rowan::NodeOrToken::Node(posting) = child else {
            continue;
        };
        if kind_of(posting.kind()) != K::POSTING {
            continue;
        }
        tokens.clear();
        let mut end = at;
        let mut p = posting_start;
        // Flatten the line: its own tokens, and those of its amount, cost and
        // price nodes. Stop at the NEWLINE, or at a metadata child.
        let mut done = false;
        for part in posting.children() {
            if done {
                break;
            }
            match part {
                rowan::NodeOrToken::Token(t) => {
                    let kind = kind_of(t.kind());
                    let range = p..p + u32::from(t.text_len()) as usize;
                    p = range.end;
                    if kind == K::NEWLINE {
                        end = range.start;
                        done = true;
                    } else if !(tokens.is_empty() && kind == K::WHITESPACE) {
                        tokens.push((kind, range));
                    }
                }
                rowan::NodeOrToken::Node(n) => match kind_of(n.kind()) {
                    K::AMOUNT | K::COST_SPEC | K::PRICE_ANNOTATION => {
                        flatten_green(n, &mut p, tokens);
                    }
                    _ => {
                        end = p;
                        done = true;
                    }
                },
            }
        }
        let (from, to) = (posting_start + off, end + off);
        let first_after = prior_error_starts.partition_point(|&s| s < from);
        let first_prior = prior_error_starts
            .get(first_after)
            .copied()
            .filter(|&s| s < to);
        if errors[errors_before..]
            .iter()
            .any(|e| (from..to).contains(&e.span.start))
        {
            continue;
        }
        let Some(before) = report_defects_before(first_prior, tokens, off) else {
            continue;
        };
        let Some(defect) = super::directive_header::first_posting_defect(tokens, end, stripped)
            .filter(|d| d.range.start + off < before)
        else {
            // A cost date that is not a real calendar date (`{1 USD,
            // 2024-02-30}`) is reported by `report_invalid_dates`.
            // Grammatical; beancount's builder still rejects some postings.
            if first_prior.is_none()
                && let Some((range, message)) = posting_builder_error(tokens, stripped)
            {
                errors.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(message),
                    Span::new(range.start + off, range.end + off),
                ));
            }
            continue;
        };
        let text = stripped.get(defect.range.clone()).unwrap_or_default();
        // Glued to the currency that ended the amount, and a character a
        // currency may hold inside it: the lexer ended the currency before it
        // (`1 USD-`, where beancount reads one invalid token).
        let glued_to_currency = tokens
            .iter()
            .position(|(_, r)| r.start == defect.range.start)
            .and_then(|i| i.checked_sub(1))
            .is_some_and(|i| tokens[i].0 == K::CURRENCY && tokens[i].1.end == defect.range.start);
        let message = if glued_to_currency && matches!(text, "-" | "'" | "." | "_") {
            format!(
                "unexpected {text:?} after the posting amount: a currency cannot end in `{text}`"
            )
        } else {
            super::directive_header::defect_message("a posting", &defect, text)
        };
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(message),
            Span::new(defect.range.start + off, defect.range.end + off),
        ));
    }
}

/// What beancount's grammar BUILDER rejects in a grammatical posting line
/// (`grammar.py`'s `cost_spec` and `posting`), reported at parse time there
/// like a syntax error, so here too (#2802, stage 3). The first, in
/// beancount's order:
///
/// - a cost spec with two numbers-and-currencies, two dates or two labels
///   (`{2, USD}` is the number `2` and the currency `USD`, two costs);
/// - a `#` in a `{{ }}` total cost ("Per-unit cost may not be specified using
///   total cost syntax");
/// - a negative price (`@ -3 USD`), evaluated by the shared reader;
/// - `@@` on a posting without a number for its units;
/// - a cost and a price whose currencies are both written and differ
///   (`{100 USD} @ 120 EUR`): "Cost and price currencies must match", for a
///   buy and a sale alike. A cost spec written without a currency (`{}`,
///   `{100}`) or a price without one is not checked, as in beancount. A sale
///   with mismatched currencies is then not booked, deliberately, where
///   beancount books it, and booking says so
///   (`BookingError::CostPriceCurrencyMismatch`, #2571).
///
/// `tokens` is the posting line as [`posting_line_check`] flattens it, and
/// grammatical: [`super::directive_header::first_posting_defect`] found
/// nothing.
fn posting_builder_error(
    tokens: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
    src: &str,
) -> Option<(std::ops::Range<usize>, String)> {
    use crate::SyntaxKind as K;
    // Most postings have neither a cost spec nor a price: nothing to check.
    if !tokens.iter().any(|(k, _)| {
        matches!(
            k,
            K::L_BRACE | K::L_BRACE_HASH | K::L_DOUBLE_BRACE | K::AT | K::AT_AT
        )
    }) {
        return None;
    }
    // In place, so the caller's reused buffer is the only allocation: this
    // runs on every posting with a cost or a price.
    tokens.retain(|(k, _)| !is_trivia_kind(*k) && *k != K::BOM);
    let sig = tokens.as_slice();
    let account = sig.iter().position(|(k, _)| *k == K::ACCOUNT)?;
    let opener = |k: K| matches!(k, K::L_BRACE | K::L_BRACE_HASH | K::L_DOUBLE_BRACE);
    let units_end = sig[account + 1..]
        .iter()
        .position(|(k, _)| opener(*k) || matches!(k, K::AT | K::AT_AT))
        .map_or(sig.len(), |i| account + 1 + i);
    let units_have_number = sig[account + 1..units_end]
        .iter()
        .any(|(k, _)| *k == K::NUMBER);

    // The cost spec, component by component; a component is `sig[start..i]`.
    let mut i = units_end;
    if let Some((open, _)) = sig.get(i)
        && opener(*open)
    {
        let is_total = *open == K::L_DOUBLE_BRACE;
        let close = if is_total {
            K::R_DOUBLE_BRACE
        } else {
            K::R_BRACE
        };
        let (mut costs, mut dates, mut labels) = (0usize, 0usize, 0usize);
        // `{#` begins the first component with its `#`.
        let mut component_has_hash = *open == K::L_BRACE_HASH;
        i += 1;
        let mut start = i;
        loop {
            let token = sig.get(i);
            let ends = token.is_none_or(|(k, _)| *k == K::COMMA || *k == close);
            if !ends {
                component_has_hash |= token?.0 == K::HASH;
                i += 1;
                continue;
            }
            let component = &sig[start..i];
            if let Some(first) = component.first().or_else(|| {
                // `{# 2 USD}`: the hash was the opener.
                component_has_hash.then_some(&sig[units_end])
            }) {
                let duplicate = |n: &mut usize, what: &str| {
                    *n += 1;
                    (*n > 1).then(|| {
                        (
                            first.1.start..component.last().map_or(first.1.end, |t| t.1.end),
                            format!("duplicate {what} in the cost spec, as beancount reports"),
                        )
                    })
                };
                let found = match (component.len(), first.0) {
                    (1, K::DATE) => duplicate(&mut dates, "date"),
                    (1, K::STRING) => duplicate(&mut labels, "label"),
                    // Cost merging, `{*}`. Deliberately NOT reported, unlike
                    // beancount 3.2.3 ("Cost merging is not supported yet"):
                    // rledger implements it (average-cost merge booking, see
                    // `rustledger_core::inventory::booking`), a correct
                    // feature beancount lacks, which we keep. The matrix pins
                    // its rows (`known_cost_merge`).
                    (1, K::STAR) => None,
                    _ => duplicate(&mut costs, "cost"),
                };
                if found.is_some() {
                    return found;
                }
                if is_total && component_has_hash {
                    let hash = component.iter().find(|(k, _)| *k == K::HASH)?;
                    return Some((
                        hash.1.clone(),
                        "a per-unit cost (`#`) cannot be written with the total-cost `{{ }}` \
                         syntax, as beancount reports"
                            .to_string(),
                    ));
                }
            }
            component_has_hash = false;
            i += 1;
            start = i;
            if token.is_none_or(|(k, _)| *k == close) {
                break;
            }
        }
    }

    // The price.
    let (at, at_range) = sig.get(i)?;
    if !matches!(at, K::AT | K::AT_AT) {
        return None;
    }
    let price = &sig[i + 1..];
    let number_tokens = match price.last() {
        Some((K::CURRENCY, _)) => &price[..price.len() - 1],
        _ => price,
    };
    // Only an expression with a `-` can be negative; skip the evaluator (and
    // its token view) for every other price.
    if number_tokens.iter().any(|(k, _)| *k == K::MINUS) {
        let view: Vec<TextToken<'_>> = number_tokens
            .iter()
            .map(|(k, r)| TextToken {
                kind: *k,
                text: src.get(r.clone()).unwrap_or_default(),
            })
            .collect();
        let mut cursor = 0;
        if let Some(value) = parse_arith_expr(&view, &mut cursor)
            && value.is_sign_negative()
            && !value.is_zero()
        {
            let from = number_tokens[0].1.start;
            let to = price.last().map_or(from, |t| t.1.end);
            return Some((
                from..to,
                format!(
                    "negative prices are not allowed: {}, as in beancount",
                    src.get(from..to).unwrap_or_default()
                ),
            ));
        }
    }
    if *at == K::AT_AT && !units_have_number {
        return Some((
            at_range.clone(),
            "a total price (`@@`) on a posting without a number for its units, \
             as beancount reports"
                .to_string(),
        ));
    }
    // Both currencies written and different: beancount's builder rejects the
    // posting for a buy and a sale alike (`grammar.py` `posting`). A cost
    // spec's currency is its one `CURRENCY` token (dates and labels have
    // none); the price's is its last token.
    let cost_currency = sig[units_end..i].iter().find(|(k, _)| *k == K::CURRENCY);
    if let (Some((_, cost)), Some((K::CURRENCY, price_currency))) = (cost_currency, price.last()) {
        let (cost_text, price_text) = (
            src.get(cost.clone()).unwrap_or_default(),
            src.get(price_currency.clone()).unwrap_or_default(),
        );
        if cost_text != price_text {
            return Some((
                cost.start..price_currency.end,
                format!(
                    "{}: {cost_text} != {price_text}",
                    crate::COST_PRICE_CURRENCY_MISMATCH
                ),
            ));
        }
    }
    None
}

/// Append every token under `node` to `out`, with absolute ranges starting at
/// `*at`, which it advances.
fn flatten_green(
    node: &rowan::GreenNodeData,
    at: &mut usize,
    out: &mut Vec<(crate::SyntaxKind, std::ops::Range<usize>)>,
) {
    let kind_of = <crate::BeancountLanguage as rowan::Language>::kind_from_raw;
    for child in node.children() {
        match child {
            rowan::NodeOrToken::Token(t) => {
                let range = *at..*at + u32::from(t.text_len()) as usize;
                *at = range.end;
                out.push((kind_of(t.kind()), range));
            }
            rowan::NodeOrToken::Node(n) => flatten_green(n, at, out),
        }
    }
}

/// Shared by both walkers so one defect cannot be reported two ways.
pub(super) fn header_defect_error(
    defect: super::txn_header::HeaderDefect,
    range: &std::ops::Range<usize>,
    stripped: &str,
    bom_offset: u32,
) -> crate::ParseError {
    // `get` rather than indexing: a range that is not a char boundary would
    // panic, and a parser must not panic on malformed input. Token ranges are
    // always char boundaries, so this is unreachable today — but an empty
    // slice would render as `unexpected "" in transaction header`, which names
    // nothing. Fall back to the byte range instead, so even the unreachable
    // branch produces something a reader can act on.
    let message = match stripped.get(range.clone()) {
        Some(text) => super::txn_header::defect_message(defect, text),
        None => format!(
            "malformed transaction header at bytes {}..{} ({defect:?})",
            range.start, range.end
        ),
    };
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError(message),
        Span::new(
            range.start + bom_offset as usize,
            range.end + bom_offset as usize,
        ),
    )
}

fn transaction_body_check(
    child: &crate::SyntaxNode,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    // Caller dispatches: `child` is a TRANSACTION.
    {
        // Skip past the header NEWLINE, then look for catch-all
        // tokens (non-trivia, non-comment) appearing on lines
        // OUTSIDE POSTING / META_ENTRY child nodes.
        // Track whether we've SEEN at least one non-trivia
        // header token (DATE / flag / STRING / etc.); only AFTER
        // that does the next NEWLINE count as the header
        // terminator. Otherwise leading-trivia NEWLINEs from the
        // Directive-Terminator Rule would falsely trip
        // past_header on the very first iteration.
        let mut past_header = false;
        let mut saw_header_content = false;
        let mut line_start: Option<u32> = None;
        let mut line_has_content = false;
        // #2575: a tag/link line after the first posting is an error. The
        // line's tag and link tokens, as written, for the message.
        let mut posting_seen = false;
        let mut line_tags = String::new();
        for el in child.children_with_tokens() {
            match el {
                rowan::NodeOrToken::Token(t) => {
                    if !past_header {
                        if t.kind() == crate::SyntaxKind::NEWLINE {
                            if saw_header_content {
                                past_header = true;
                            }
                        } else if !is_trivia_kind(t.kind()) {
                            saw_header_content = true;
                        }
                        continue;
                    }
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    if line_start.is_none() {
                        line_start = Some(start);
                    }
                    if t.kind() == crate::SyntaxKind::NEWLINE {
                        if let Some(ls) = line_start {
                            if line_has_content {
                                out.push(unexpected_body_input(ls, end, bom_offset));
                            } else if !line_tags.is_empty() {
                                out.push(tags_after_posting_error(
                                    &line_tags,
                                    ls as usize,
                                    end as usize,
                                    bom_offset,
                                ));
                            }
                        }
                        line_start = None;
                        line_has_content = false;
                        line_tags.clear();
                    } else if matches!(t.kind(), crate::SyntaxKind::TAG | crate::SyntaxKind::LINK) {
                        // TAG / LINK on body lines is valid Beancount
                        // syntax BEFORE the first posting (they continue
                        // the transaction's tag/link list), so not
                        // unexpected input; after it, the line is the
                        // tags-after-posting error (#2575).
                        if !body_tag_joins_transaction(posting_seen) {
                            if !line_tags.is_empty() {
                                line_tags.push(' ');
                            }
                            line_tags.push_str(t.text());
                        }
                    } else if !is_trivia_kind(t.kind()) && !is_comment_kind(t.kind()) {
                        line_has_content = true;
                    }
                }
                rowan::NodeOrToken::Node(n) => {
                    // POSTING / META_ENTRY: not catch-all. Reset.
                    posting_seen |= n.kind() == crate::SyntaxKind::POSTING;
                    line_start = None;
                    line_has_content = false;
                    line_tags.clear();
                    if !past_header {
                        past_header = true;
                    }
                }
            }
        }
        // EOF terminates the final body line, same as a NEWLINE. Mirrors
        // `green::tl_transaction_body_check` (#1884).
        if past_header && let Some(ls) = line_start {
            let end: u32 = child.text_range().end().into();
            if line_has_content {
                out.push(unexpected_body_input(ls, end, bom_offset));
            } else if !line_tags.is_empty() {
                out.push(tags_after_posting_error(
                    &line_tags,
                    ls as usize,
                    end as usize,
                    bom_offset,
                ));
            }
        }
    }
}

/// Walk an `ERROR_NODE` and emit a
/// `ParseError` for each line that is NEITHER a section marker
/// (a column-0 `*`, per `is_section_marker`) NOR a column-0 comment. The variant emitted
/// mirrors the legacy parser's error-recovery classifier
/// (`parser.rs:2186-2249`): a stray BOM on the line (one in an invalid
/// token, see [`has_stray_bom`]) → `BomInDirectiveBody`
/// (with `BOM_REMOVAL_HINT`); Unicode-character account →
/// `InvalidAccount`; otherwise → `SyntaxError("unexpected
/// input")`. `stripped` is the post-BOM-strip source so token
/// `text_range` indices into it correctly.
/// Emit the recovery diagnostics for one `ERROR_NODE` line.
///
/// Mirrors `green::emit_error_node_line`, and exists for the same reason:
/// this runs from BOTH the newline-terminated and the EOF-terminated site, and
/// two inline copies is how the span rule or the secondary BOM diagnostic
/// drifts between them.
fn emit_error_node_line(
    first_non_trivia: Option<crate::SyntaxKind>,
    is_section: bool,
    line_start: Option<u32>,
    end: u32,
    invalid: &[std::ops::Range<usize>],
    bom_offset: u32,
    stripped: &str,
    out: &mut Vec<crate::ParseError>,
) {
    let is_comment = matches!(first_non_trivia, Some(k) if is_comment_kind(k));
    if is_section || is_comment || first_non_trivia.is_none() {
        return;
    }
    let Some(ls) = line_start else { return };
    // Legacy span INCLUDES the terminator NEWLINE (skip_to_newline consumes it
    // before span_from is called); at EOF the terminator is the node end.
    let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
    let stray_bom = has_stray_bom(invalid, stripped);
    let primary = classify_recovery_error(
        stripped,
        ls as usize..end as usize,
        invalid,
        stray_bom,
        span,
    );
    let primary_is_bom = matches!(primary.kind, crate::ParseErrorKind::BomInDirectiveBody);
    out.push(primary);
    // Additive secondary `BomInDirectiveBody` when a different primary
    // diagnostic already fired AND the line ALSO has a stray BOM byte. Matches
    // legacy `parser.rs:2258-2263`: without it, a Windows-exported line with
    // both problems surfaces only the actionable root cause and the user has no
    // clue the invisible BOM byte is also corrupting the line.
    if !primary_is_bom && stray_bom {
        out.push(
            crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
        );
    }
    report_invalid_tokens_of_error_line(
        ls as usize,
        invalid,
        stripped,
        bom_offset,
        !primary_is_bom && stray_bom,
        out,
    );
}

fn error_node_check(
    child: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    // Caller dispatches: `child` is an ERROR_NODE.
    {
        let mut line_start: Option<u32> = None;
        let mut first_non_trivia: Option<crate::SyntaxKind> = None;
        let mut section = false;
        let mut invalid: Vec<std::ops::Range<usize>> = Vec::new();
        for el in child.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            if line_start.is_none() {
                line_start = Some(start);
            }
            if t.kind() == crate::SyntaxKind::NEWLINE {
                emit_error_node_line(
                    first_non_trivia,
                    section,
                    line_start,
                    end,
                    &invalid,
                    bom_offset,
                    stripped,
                    out,
                );
                line_start = None;
                invalid.clear();
                first_non_trivia = None;
                section = false;
                continue;
            }
            if t.kind() == crate::SyntaxKind::ERROR_TOKEN {
                invalid.push(start as usize..end as usize);
            }
            if first_non_trivia.is_none() && !is_trivia_kind(t.kind()) {
                first_non_trivia = Some(t.kind());
                section = is_section_marker(t.kind(), stripped, start as usize);
            }
        }
        // EOF terminates the final line exactly as a NEWLINE would. Mirrors
        // `green::tl_error_node_check`; without it the two paths disagree on
        // any input lacking a trailing newline, and a malformed last line
        // produced no diagnostic at all (#1884).
        let end: u32 = child.text_range().end().into();
        emit_error_node_line(
            first_non_trivia,
            section,
            line_start,
            end,
            &invalid,
            bom_offset,
            stripped,
            out,
        );
    }
}

/// Whether one of a line's invalid tokens (`invalid`, ranges into
/// `stripped`) holds a U+FEFF: a stray mid-file BOM.
///
/// The line's raw text is not the thing to search. A BOM inside a string
/// literal, a comment or an account token is content, not a stray byte; see
/// [`token_has_stray_bom`], the same rule for a single token. Shared by the
/// red and green recovery walks (this file's and `green`'s
/// `emit_error_node_line`). Every range in `invalid` is an `ERROR_TOKEN`
/// (both walks collect only those), so each goes through
/// [`token_has_stray_bom`] as one.
pub(super) fn has_stray_bom(invalid: &[std::ops::Range<usize>], stripped: &str) -> bool {
    invalid.iter().any(|r| {
        stripped
            .get(r.clone())
            .is_some_and(|t| token_has_stray_bom(crate::SyntaxKind::ERROR_TOKEN, t))
    })
}

/// Whether a token of `kind` with `text` carries a stray mid-file BOM.
///
/// Only an invalid token can. A BOM the lexer placed inside a `STRING` is
/// string content, and beancount 3.2.3 keeps it byte-for-byte in the value
/// (#2910); one inside a comment is ignored with the comment, as there; and
/// one glued into an account is part of the `ACCOUNT` token, which beancount's
/// lexer reads the same way (`open Assets:Ca\u{FEFF}sh` loads there). The
/// single rule behind the inline `BomInDirectiveBody` check of both walks
/// (red `walk_descendants_once` and `green`'s fold); [`has_stray_bom`] applies
/// it to an `ERROR_NODE` line.
pub fn token_has_stray_bom(kind: crate::SyntaxKind, text: &str) -> bool {
    kind == crate::SyntaxKind::ERROR_TOKEN && text.contains(crate::bom::BOM_CHAR)
}

/// Whether the invalid token `text`, starting at byte `start` of `source`, is
/// a mid-file BOM the lexer kept as a token of its own: one that starts its
/// line, or follows another such BOM (#2928).
///
/// Only such a BOM is layout-transparent (the lexer's `Err` arm and
/// `apply_err_layout_transparency`), and stands for nothing but itself: its
/// line's `BomInDirectiveBody` reports it, and the rest of the line lexes
/// as if it were not there. Anywhere else, a BOM starts (or sits inside) an
/// invalid run that goes on to the next blank, as beancount's does, and is
/// an invalid token like any other. A token the lexer cut at a line-start
/// BOM starts with one, and what stands before it on its line is nothing
/// or more such BOMs; a BOM-led run in the middle of a line never follows a
/// BOM, as a token ending in one (an invalid run, an account) would have
/// taken it in. So one look back, at the character before `start`, tells
/// the two apart, at constant cost.
///
/// Such a token is only ever on an `ERROR_NODE` line: a line whose first
/// content token is a BOM starts no directive, and no directive takes it in
/// (see `holds_an_invalid_token`). So of the counts of invalid tokens, only
/// [`report_invalid_tokens_of_error_line`] asks this; for
/// `quiet_after_invalid_tokens` the BOM is its line's first invalid token,
/// as beancount's is (see there).
pub(super) fn is_line_start_bom_token(source: &str, start: usize, text: &str) -> bool {
    text.starts_with(crate::bom::BOM_CHAR)
        && source.get(..start).is_some_and(|before| {
            before.is_empty() || before.ends_with(['\n', crate::bom::BOM_CHAR])
        })
}

/// Whether the invalid token `text`, starting at byte `start` of `source`, is
/// BOMs beancount reads into an account (`logos_lexer::bom_led_account`):
/// either a run of BOMs with an account of its own right after it, which the
/// lexer keeps as a token of its own (`$x <BOM>Assets:A`, and the last BOM of
/// a run that starts the line), or the BOMs together with the rest of
/// beancount's account where no account of rledger's follows them
/// (`$x <BOM>assets:A`). Either way it is none of beancount's invalid tokens:
/// it is reported by the line's `BomInDirectiveBody` alone and counts as no
/// invalid token (#2928). The one predicate every count of invalid tokens
/// asks (`report_invalid_tokens_of_error_line`, `invalid_runs`,
/// `quiet_after_invalid_tokens`, `holds_an_invalid_token`).
///
/// Constant work past the token unless an account may follow: a token in a
/// long run of BOMs sees the next BOM and stops there.
fn is_bom_account_token(source: &str, start: usize, text: &str) -> bool {
    if !text.starts_with(crate::bom::BOM_CHAR) {
        return false;
    }
    let Some(from) = source.get(start..) else {
        return false;
    };
    if text.chars().all(|c| c == crate::bom::BOM_CHAR) {
        !from[text.len()..].starts_with(crate::bom::BOM_CHAR)
            && crate::logos_lexer::account_follows_bom_run(from)
    } else {
        crate::logos_lexer::bom_led_account(from).is_some_and(|(_, end)| end == text.len())
    }
}

/// Pick the most specific `ParseError` variant for an
/// error-recovery line, mirroring the legacy parser's classifier
/// at `parser.rs:2186-2249`:
/// 1. A Unicode-character account (`Assets:Café:…`) → primary
///    `InvalidAccount` - it's the actionable root cause.
/// 2. A stray mid-file BOM byte (`U+FEFF`; `stray_bom`, see
///    [`has_stray_bom`]) → `BomInDirectiveBody` with `BOM_REMOVAL_HINT`
///    so miette surfaces the remediation step.
/// 3. Anything else → `SyntaxError("unexpected input")`.
///
/// Order matters: a Windows-exported file with a Unicode account
/// AND an internal BOM gets the Unicode-account diagnostic
/// (the BOM is usually a side effect, not the root cause).
///
/// Only text outside the line's invalid tokens (`invalid`, ranges into
/// `stripped`) can be an account: inside one (`Heading,Ü:A`, read by
/// beancount as one invalid token) it is part of that token, whose own error
/// reports it, and taking it for an account too counted the token twice.
/// Its bytes are masked with `_`, not blanked: a blank would split the
/// word, so the account glued to the BOM in `<BOM>Fݾ:Ü` (one word led by the
/// BOM, never an account here) would start a word of its own and be counted
/// beside the BOM's diagnostic.
pub(super) fn classify_recovery_error(
    stripped: &str,
    line: std::ops::Range<usize>,
    invalid: &[std::ops::Range<usize>],
    stray_bom: bool,
    span: Span,
) -> crate::ParseError {
    let line_text = stripped.get(line.clone()).unwrap_or("");
    let outside_invalid: std::borrow::Cow<'_, str> =
        if invalid.is_empty() || !line_text.starts_with(crate::bom::BOM_CHAR) {
            line_text.into()
        } else {
            // `invalid` is in line order: one sweep, linear in the line. One `_`
            // per byte keeps every offset, so the account found is read back
            // from the line itself.
            let mut k = 0;
            let mut masked = String::with_capacity(line_text.len());
            for (i, c) in line_text.char_indices() {
                let at = line.start + i;
                while invalid.get(k).is_some_and(|r| r.end <= at) {
                    k += 1;
                }
                if invalid.get(k).is_some_and(|r| r.start <= at) {
                    masked.extend(std::iter::repeat_n('_', c.len_utf8()));
                } else {
                    masked.push(c);
                }
            }
            masked.into()
        };
    if let Some(account) = crate::diagnostics::find_unicode_account(&outside_invalid) {
        // A word partly masked is reported whole, as written.
        let at = account.as_ptr().addr() - outside_invalid.as_ptr().addr();
        let account = line_text.get(at..at + account.len()).unwrap_or(account);
        return crate::ParseError::new(
            crate::ParseErrorKind::InvalidAccount(account.to_string()),
            span,
        );
    }
    if stray_bom {
        return crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
            .with_hint(crate::diagnostics::BOM_REMOVAL_HINT);
    }
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
        span,
    )
}

/// Walk every descendant token and emit a `ParseError` for each
/// `ERROR_TOKEN` (a stray-BOM one included) that lands inside an
/// otherwise-valid directive node - i.e., NOT inside an
/// `ERROR_NODE` ancestor. Catches lexer-reject bytes the
/// outer recovery path misses:
/// - `.` in `.50 USD` (leading-decimal in posting amount) →
///   `SyntaxError`.
/// - Mid-file U+FEFF byte inside a recognized directive (e.g.,
///   `open Assets:Bank \u{FEFF}USD`) → `BomInDirectiveBody` with
///   `BOM_REMOVAL_HINT`.
///
/// The leading `SyntaxKind::BOM` token is skipped (the
/// legitimate strict-byte-0 BOM is already tracked by
/// `has_leading_bom`). `ERROR_NODE` descendants are skipped -
/// `extract_error_node_errors` / `classify_recovery_error`
/// already cover those.
/// Result of the fused descendants-walk visitor that powers
/// `walk_descendants_once`.
pub(super) struct DescendantsWalkResult {
    pub(super) inline_errors: Vec<crate::ParseError>,
    pub(super) top_level_comments: Vec<Spanned<String>>,
    pub(super) currency_occurrences: Vec<Spanned<Currency>>,
    pub(super) account_occurrences: Vec<Spanned<rustledger_core::Account>>,
    /// The three per-node shape rules, kept in SEPARATE vecs rather than
    /// merged into `inline_errors`.
    ///
    /// Two reasons. They are emitted at a different point in the error order
    /// than the inline errors (see `parse_via_cst_inner`), and each vec stays
    /// grouped the way its former standalone pass emitted it — document order
    /// within a rule, rules in a fixed sequence. Merging them would interleave
    /// the three by position, which no test pins today but which is
    /// observable in every diagnostic list rledger prints.
    ///
    /// Populated only by the GREEN walker. The red walker leaves them empty
    /// and `parse_via_cst_inner` calls the standalone `extract_*` functions
    /// for that path instead — see the call site for why the fold is
    /// green-only.
    pub(super) cost_brace_errors: Vec<crate::ParseError>,
    pub(super) link_meta_errors: Vec<crate::ParseError>,
    pub(super) custom_pushmeta_errors: Vec<crate::ParseError>,
}

/// Whether `token` is the flag of its transaction header or posting, as
/// [`ast::Transaction::flag`] / [`ast::Posting::flag`] read it.
///
/// Used to keep a one-letter flag (`T`, `P`, ...), which lexes as `CURRENCY`,
/// out of `currency_occurrences`. Asks the AST accessors themselves, so it
/// cannot disagree with how the directive's flag is read. The green walker
/// cannot build red nodes and mirrors this in `green::flag_child_index`; the
/// `parse_green_eq_red_corpus` test and the `fuzz_green_eq_red` target pin the
/// two to the same occurrences.
pub(super) fn is_flag_token(token: &crate::SyntaxToken) -> bool {
    let Some(parent) = token.parent() else {
        return false;
    };
    let flag = match parent.kind() {
        crate::SyntaxKind::TRANSACTION => ast::Transaction::cast(parent)
            .and_then(|t| t.flag())
            .map(|f| f.syntax().clone()),
        crate::SyntaxKind::POSTING => ast::Posting::cast(parent)
            .and_then(|p| p.flag())
            .map(|f| f.syntax().clone()),
        _ => None,
    };
    flag.as_ref() == Some(token)
}

/// Fused single-pass visitor over `source_file`'s descendants -
/// replaces three separate walks (`extract_inline_token_errors`,
/// `extract_top_level_comments`, `extract_currency_occurrences`)
/// with one traversal. Each walk had its own per-token cost; the
/// LSP runs them on every keystroke, so collapsing 3·O(N) → 1·O(N)
/// matters at editor-edge latencies. The state of each former
/// walk is maintained inline below.
fn walk_descendants_once(
    source_file: &SourceFile,
    bom_offset: u32,
    collect_occurrences: bool,
) -> DescendantsWalkResult {
    let mut inline_errors: Vec<crate::ParseError> = Vec::new();
    let mut top_level_comments: Vec<Spanned<String>> = Vec::new();
    let mut currency_occurrences: Vec<Spanned<Currency>> = Vec::new();
    let mut account_occurrences: Vec<Spanned<rustledger_core::Account>> = Vec::new();

    // `extract_top_level_comments` state: column-0 tracking.
    let mut preceded_by_ws = false;

    for el in source_file.syntax().descendants_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            // `extract_top_level_comments` used the Node arm to
            // reset preceded_by_ws when entering a recognized
            // directive. Keep that behavior - directive leading
            // trivia still gets column-0-classified correctly.
            if let rowan::NodeOrToken::Node(n) = el
                && ast::Directive::can_cast(n.kind())
            {
                preceded_by_ws = false;
            }
            continue;
        };

        // ---- `extract_top_level_comments` state machine -------
        match t.kind() {
            crate::SyntaxKind::NEWLINE => preceded_by_ws = false,
            crate::SyntaxKind::WHITESPACE => preceded_by_ws = true,
            k if is_comment_kind(k) => {
                if !preceded_by_ws {
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    let span =
                        Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                    top_level_comments.push(Spanned::new(t.text().to_string(), span));
                }
            }
            _ => {
                preceded_by_ws = false;
            }
        }

        // ---- `extract_inline_token_errors` + currency walks ---
        if t.kind() == crate::SyntaxKind::BOM {
            continue;
        }
        // ERROR_NODE-ancestor check is only consulted for tokens
        // whose downstream emission depends on it (CURRENCY, BOM-
        // text-containing, ERROR_TOKEN). For well-formed source
        // most tokens fall into none of those buckets - gating
        // the per-token `parent_ancestors` walk on relevance
        // saves an O(depth) probe per WHITESPACE/NEWLINE/comment
        // token, which dominates token counts in real ledgers.
        let kind = t.kind();
        let has_bom = token_has_stray_bom(kind, t.text());
        let is_error_token = kind == crate::SyntaxKind::ERROR_TOKEN;
        // CURRENCY/ACCOUNT need the in-ERROR_NODE probe only to decide whether
        // to record an occurrence; skip it entirely when not collecting.
        let needs_in_error_check = (collect_occurrences
            && matches!(
                kind,
                crate::SyntaxKind::CURRENCY | crate::SyntaxKind::ACCOUNT
            ))
            || has_bom
            || is_error_token;
        if !needs_in_error_check {
            continue;
        }
        let in_error_node = t
            .parent_ancestors()
            .any(|a| a.kind() == crate::SyntaxKind::ERROR_NODE);

        // CURRENCY occurrences: only outside ERROR_NODE, and only when the
        // caller wants them (LSP path). A one-letter flag (`T` in
        // `2024-01-16 T "x"`, `P` before a posting's account) lexes as
        // CURRENCY too, but it is a flag, not a currency, so it is left out:
        // otherwise references, highlight, rename and linked editing on a
        // currency `T` would also touch every `T` flag. The green walker
        // mirrors this with `flag_child_index`.
        if collect_occurrences
            && kind == crate::SyntaxKind::CURRENCY
            && !in_error_node
            && !is_flag_token(&t)
        {
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            currency_occurrences.push(Spanned::new(Currency::new(t.text()), span));
        }

        // ACCOUNT occurrences: only outside ERROR_NODE. The same
        // rationale as CURRENCY applies - the lexer classifies an
        // `ACCOUNT` token by its character shape independent of
        // whether the surrounding directive parses cleanly, and
        // source-position-aware tooling (LSP rename / references /
        // document-highlight) wants the token as the user typed it
        // even during a mid-edit broken state.
        if collect_occurrences && kind == crate::SyntaxKind::ACCOUNT && !in_error_node {
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            account_occurrences.push(Spanned::new(rustledger_core::Account::new(t.text()), span));
        }

        // Inline errors: stray BOM byte in a recognized directive
        // (-> BomInDirectiveBody + hint) or ERROR_TOKEN inside a
        // recognized directive (-> SyntaxError). Both skip when
        // already inside an ERROR_NODE (handled by the recovery
        // classifier).
        if (!has_bom && !is_error_token) || in_error_node {
            continue;
        }
        let range = t.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
        if has_bom {
            inline_errors.push(
                crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                    .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
            );
        } else {
            inline_errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                span,
            ));
        }
    }

    DescendantsWalkResult {
        inline_errors,
        top_level_comments,
        currency_occurrences,
        account_occurrences,
        // Red keeps the three shape rules as standalone `extract_*` passes;
        // `parse_via_cst_inner` calls them for this path. Folding them in here
        // too would need each token's IMMEDIATE parent kind, and this walk is
        // a flat `descendants_with_tokens()` — recovering the parent means
        // `t.parent()`, which allocates the very red `NodeData` the green fold
        // exists to avoid.
        cost_brace_errors: Vec::new(),
        link_meta_errors: Vec::new(),
        custom_pushmeta_errors: Vec::new(),
    }
}

/// Emit empty-string comments for org-mode section-marker
/// lines (`* Heading`, `** Subheading`) inside `ERROR_NODE`
/// children. The legacy parser's `parse_entry` matches
/// `Token::Star` and emits `Comment(String::new(), line_span)`;
/// the structured CST wraps these lines in `ERROR_NODE`s so we
/// have to walk them and synthesize the same shape.
fn section_marker_check(
    child: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    out: &mut Vec<Spanned<String>>,
) {
    // Caller dispatches: `child` is an ERROR_NODE.
    // Walk tokens line-by-line. A line starts at the start
    // of the first token after a NEWLINE (or at the node's
    // start) and ends at the next NEWLINE (inclusive).
    let mut line_start: Option<u32> = None;
    let mut first_non_trivia: Option<crate::SyntaxKind> = None;
    let mut section = false;
    for el in child.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        let range = t.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        if line_start.is_none() {
            line_start = Some(start);
        }
        if t.kind() == crate::SyntaxKind::NEWLINE {
            if section && let Some(ls) = line_start {
                let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
                out.push(Spanned::new(String::new(), span));
            }
            line_start = None;
            first_non_trivia = None;
            section = false;
            continue;
        }
        if first_non_trivia.is_none() && !is_trivia_kind(t.kind()) {
            first_non_trivia = Some(t.kind());
            section = is_section_marker(t.kind(), stripped, start as usize);
        }
    }
    // EOF terminates the final line. Mirrors `green::tl_section_marker_check`.
    if section && let Some(ls) = line_start {
        let end: u32 = child.text_range().end().into();
        let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
        out.push(Spanned::new(String::new(), span));
    }
}

// `extract_top_level_comments` and `extract_currency_occurrences`
// are folded into `walk_descendants_once` above - see the
// comments there for the column-0 / ERROR_NODE-exclusion rules.

// ---- Token parsing helpers -------------------------------------

/// Parse a date token the way beancount builds a date from its `DATE` token:
/// the three fields are integers ([`crate::diagnostics::date_fields`]), so
/// single-digit fields, `/` separators and extra leading zeros all read
/// (`02024-001-01` is 2024-01-01, #2808). Returns `None` when they do not form
/// a real calendar date (a month or day out of range, Feb 29 in a common year,
/// a year outside 1 to 9999).
///
/// Year 0 is refused as beancount refuses it (`year 0 is out of range`):
/// Python's `datetime.date` starts at year 1, while `jiff` would accept
/// it (#2811).
pub fn parse_date_token(text: &str) -> Option<NaiveDate> {
    // Fast path: canonical "YYYY-MM-DD".
    if text.len() == 10
        && text.as_bytes()[4] == b'-'
        && text.as_bytes()[7] == b'-'
        && let (Ok(y), Ok(m), Ok(d)) = (
            text[0..4].parse::<i32>(),
            text[5..7].parse::<u32>(),
            text[8..10].parse::<u32>(),
        )
    {
        return naive_date(y, m, d).filter(|date| date.year() >= 1);
    }
    // Slow path: any other shape the lexer accepts.
    let [year, month, day] = crate::diagnostics::date_fields(text)?;
    let year = year.parse::<i32>().ok()?;
    if !(1..=9999).contains(&year) {
        return None;
    }
    naive_date(year, month.parse().ok()?, day.parse().ok()?)
}

/// The first date in a value position on one line that is not a real
/// calendar date (`kk: 2024-02-30`, `custom "x" 2024-13-01`), with the
/// message the directive's own date gets (`InvalidDateValue`, from
/// [`crate::diagnostics::describe_invalid_date`]), or `None`.
///
/// `tokens` are the line's `(kind, range)` pairs over `src`, from its first
/// content token. `skip_leading_date` skips the first token when it is the
/// directive's own `DATE`, which [`parse_directive_date`] already reports.
///
/// One check for metadata lines, `custom` and `pushmeta` values: those dates
/// used to load as no value at all, with no error (#2811). beancount reports
/// each (`day is out of range for month`).
pub(super) fn invalid_value_date(
    tokens: &[(crate::SyntaxKind, std::ops::Range<usize>)],
    src: &str,
    skip_leading_date: bool,
) -> Option<(std::ops::Range<usize>, String)> {
    let skip = usize::from(
        skip_leading_date
            && tokens
                .first()
                .is_some_and(|(k, _)| *k == crate::SyntaxKind::DATE),
    );
    tokens[skip..].iter().find_map(|(kind, range)| {
        if *kind != crate::SyntaxKind::DATE {
            return None;
        }
        let text = src.get(range.clone())?;
        parse_date_token(text).is_none().then(|| {
            (
                range.clone(),
                crate::diagnostics::describe_invalid_date(text),
            )
        })
    })
}

/// Report every `DATE` token that is not a real calendar date, wherever it
/// stands, and let that error stand for its line's grammar errors, as
/// beancount does (#2856).
///
/// beancount builds the date while lexing, so a bad date is a lexer error: it
/// is named (`day is out of range for month`) in every position, a header, a
/// metadata or `custom` value, an `event` or `option` argument, a price, a
/// transaction header, an orphan indented line; two bad dates on one line are
/// two errors; and the rest of the line gets no grammar error on top, because
/// the parser never sees a date token there. A grammar error BEFORE the date
/// still stands: the parser fails at that earlier token before the lexer
/// reaches the date (`balance Assets:A USD 2024-02-30` is `unexpected
/// CURRENCY` and the date). Its OTHER lexer errors still stand: the
/// lexer goes on past the date, so a stray `` ` `` or a mid-file BOM on the
/// same line is reported too. Here the date is one token like any other until
/// it is read, so this pass, run once over the whole tree after every other
/// check, applies that rule in one place: each invalid date not already
/// reported at its position (a directive's own date, by
/// `parse_directive_date`) gets `InvalidDateValue`, and a parse error is
/// dropped when the parser failed at or after its line's first bad date
/// (`reaches_a_bad_date` says where it failed), unless it covers an
/// `ERROR_TOKEN` (the lexer's own error: a character no token takes, a
/// mid-file BOM). A directive with a bad date of
/// its own is still dropped, as in beancount, but the bad dates under it are
/// now reported too. A date inside one of beancount's invalid tokens (an
/// invalid character takes the rest of its run of non-blank characters) is
/// never read there, so it is not named here either.
///
/// Linear in the source and the error count: the line bounds are found in one
/// forward pass over the sorted dates, and each error is looked up by binary
/// search (#2868 review: a line of 40,000 bad dates took a minute).
///
/// Walks GREEN tokens (kind and length, no red-node allocation).
fn report_invalid_dates(
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    grammar_failures: &[(usize, usize, usize)],
    errors: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    let off = bom_offset as usize;
    let mut bad: Vec<std::ops::Range<usize>> = Vec::new();
    let mut lexer_errors: Vec<std::ops::Range<usize>> = Vec::new();
    // `STRING` tokens that run over a line end (stripped frame), so a line
    // that starts inside one is not taken for a gap line.
    let mut multiline_strings: Vec<std::ops::Range<usize>> = Vec::new();
    let mut stack = vec![(
        root.green().to_owned(),
        usize::from(root.text_range().start()),
    )];
    while let Some((node, start)) = stack.pop() {
        let mut at = start;
        for child in node.children() {
            match child {
                rowan::NodeOrToken::Node(n) => {
                    let len = usize::from(n.text_len());
                    stack.push((n.to_owned(), at));
                    at += len;
                }
                rowan::NodeOrToken::Token(t) => {
                    let len = t.text().len();
                    match <crate::BeancountLanguage as rowan::Language>::kind_from_raw(t.kind()) {
                        K::DATE if parse_date_token(t.text()).is_none() => {
                            bad.push(at..at + len);
                        }
                        K::ERROR_TOKEN => lexer_errors.push(at + off..at + len + off),
                        K::STRING if t.text().contains('\n') => {
                            multiline_strings.push(at..at + len);
                        }
                        _ => {}
                    }
                    at += len;
                }
            }
        }
    }
    if bad.is_empty() {
        return;
    }
    bad.sort_unstable_by_key(|r| r.start);
    lexer_errors.sort_unstable_by_key(|r| r.start);
    multiline_strings.sort_unstable_by_key(|r| r.start);
    let reported: std::collections::HashSet<usize> = errors
        .iter()
        .filter(|e| matches!(e.kind, crate::ParseErrorKind::InvalidDateValue(_)))
        .map(|e| e.span.start)
        .collect();
    // Whether a lexer error starts in `from..to` (BOM frame).
    let lexer_error_in = |from: usize, to: usize| {
        let i = lexer_errors.partition_point(|t| t.start < from);
        lexer_errors.get(i).is_some_and(|t| t.start < to)
    };
    // For each line holding a reported bad date, in order and once, its start
    // and the stretch from its first such date to its end, in the BOM frame.
    // `line` is the current date's line in the stripped frame, and `scanned`
    // is where it ended (its `\n`), so every byte is stepped over at most
    // once looking back for a line start and once looking ahead for a line
    // end.
    let mut lines: Vec<(usize, std::ops::Range<usize>)> = Vec::new();
    let mut line = 0..0;
    let mut scanned = 0;
    // Where the last date on this line ended, and whether it stood inside an
    // invalid token (below), so each stretch between dates is scanned once.
    let mut prev_end = 0;
    let mut prev_in_invalid = false;
    for range in bad {
        if range.start >= line.end {
            let back = &stripped[scanned..range.start];
            let ahead = &stripped[range.end..];
            let line_start = back.rfind('\n').map_or(scanned, |i| scanned + i + 1);
            let line_end = ahead.find('\n').map_or(stripped.len(), |i| range.end + i);
            #[cfg(test)]
            test_counters::DATE_LINE_SCANNED_BYTES
                .with(|c| c.set(c.get() + (range.start - scanned) + (line_end - range.end)));
            line = line_start..line_end;
            scanned = line_end;
            prev_end = line_start;
            prev_in_invalid = false;
        }
        // beancount's lexer takes everything from an invalid character up to
        // the next space, tab or line end as ONE invalid token, so a date
        // inside that run is never read, and never named. The lexer forms the
        // same run (#2872), except after a mid-file BOM, which keeps its own
        // extent there, so a date glued to one still lexes on its own.
        let between = &stripped[prev_end..range.start];
        #[cfg(test)]
        test_counters::DATE_LINE_SCANNED_BYTES.with(|c| c.set(c.get() + between.len()));
        let in_invalid = match between.rfind([' ', '\t', '\r']) {
            Some(i) => lexer_error_in(prev_end + i + 1 + off, range.start + off),
            None => prev_in_invalid || lexer_error_in(prev_end + off, range.start + off),
        };
        prev_end = range.end;
        prev_in_invalid = in_invalid;
        if in_invalid {
            continue;
        }
        if lines
            .last()
            .is_none_or(|(_, stretch)| stretch.end != line.end + off)
        {
            lines.push((line.start + off, range.start + off..line.end + off));
        }
        if !reported.contains(&(range.start + off)) {
            let text = &stripped[range.clone()];
            errors.push(invalid_value_date_error(
                range,
                crate::diagnostics::describe_invalid_date(text),
                off,
            ));
        }
    }
    // Whether a grammar error is the date's doing: the parser failed at or
    // after the first bad date on its line, which it reaches. An error from
    // an earlier failure is reported by beancount too (`balance Assets:A USD
    // 2024-02-30`: `unexpected CURRENCY`, then the date).
    //
    // Where the parser failed: for a dropped directive's whole-node error,
    // what the header grammar says (`grammar_failures`), placed on the line by
    // the header's start, since the node's span takes in leading blank and
    // comment lines. For any other error, its first non-blank character: a
    // precise error starts at its token, and a whole-line recovery error (an
    // orphan indented line, a transaction-body line no posting takes) fails at
    // the line's first token in beancount (`  "x" 2024-02-30`: `unexpected
    // STRING`, then the date; `  2024-02-30 5`: the date alone).
    // Where every error starts, sorted, stripped frame.
    // Only an error that swallows the next line keeps a directive that takes
    // no metadata from leaving a gap (`swallows_the_next_line`).
    let mut error_starts: Vec<usize> = errors
        .iter()
        .filter(|e| swallows_the_next_line(&e.kind))
        .map(|e| e.span.start.saturating_sub(off))
        .collect();
    error_starts.sort_unstable();
    let reaches_a_bad_date = |span: &Span| {
        let j = grammar_failures.partition_point(|&(start, _, _)| start < span.start);
        let (anchor, failed_at) = match grammar_failures.get(j) {
            Some(&(start, header_start, failed_at)) if start == span.start => {
                (header_start, failed_at)
            }
            _ => {
                let from = span.start.saturating_sub(off).min(stripped.len());
                let is_blank = |b: &u8| matches!(b, b' ' | b'\t');
                let ahead = stripped[from..].bytes().take_while(is_blank).count();
                let behind = stripped[..from].bytes().rev().take_while(is_blank).count();
                let line_begin = from - behind;
                // An indented line after a blank line, a comment, a directive
                // that takes no metadata or the top of the file
                // (`previous_line_is_a_gap`) is no directive's continuation, so
                // beancount fails at the indent itself (`unexpected INDENT`),
                // before any date on it.
                let after_a_gap = ahead + behind > 0
                    && (line_begin == 0 || stripped.as_bytes()[line_begin - 1] == b'\n')
                    && previous_line_is_a_gap(
                        stripped,
                        line_begin,
                        &multiline_strings,
                        &error_starts,
                    );
                let failed_at = if after_a_gap {
                    line_begin + off
                } else {
                    span.start + ahead
                };
                (span.start, failed_at)
            }
        };
        let i = lines.partition_point(|(_, stretch)| stretch.end <= anchor);
        let Some((line_start, stretch)) = lines.get(i) else {
            return false;
        };
        *line_start <= anchor
            && stretch.start < span.end.max(span.start + 1)
            && failed_at >= stretch.start
    };
    let covers_a_lexer_error = |span: &Span| {
        let end = span.end.max(span.start + 1);
        let i = lexer_errors.partition_point(|t| t.end <= span.start);
        lexer_errors.get(i).is_some_and(|t| t.start < end)
    };
    errors.retain(|e| {
        matches!(e.kind, crate::ParseErrorKind::InvalidDateValue(_))
            || !reaches_a_bad_date(&e.span)
            || covers_a_lexer_error(&e.span)
    });
}

/// The directives that take no metadata, with their keywords: beancount's
/// grammar has no indented continuation for them, so an indented line after
/// one is `unexpected INDENT`. The one list for `previous_line_is_a_gap` and
/// `report_no_metadata_continuations`.
const NO_METADATA_DIRECTIVES: [(crate::SyntaxKind, &str); 7] = [
    (crate::SyntaxKind::OPTION_DIRECTIVE, "option"),
    (crate::SyntaxKind::INCLUDE_DIRECTIVE, "include"),
    (crate::SyntaxKind::PLUGIN_DIRECTIVE, "plugin"),
    (crate::SyntaxKind::PUSHTAG_DIRECTIVE, "pushtag"),
    (crate::SyntaxKind::POPTAG_DIRECTIVE, "poptag"),
    (crate::SyntaxKind::PUSHMETA_DIRECTIVE, "pushmeta"),
    (crate::SyntaxKind::POPMETA_DIRECTIVE, "popmeta"),
];

/// Whether an error on a directive's header means beancount's recovery
/// swallows the indented line after it, so that line is not `unexpected
/// INDENT` there. A syntax error or a lexer error (an invalid date) does: bison
/// discards up to the next statement. A `poptag` / `popmeta` of nothing pushed,
/// or a push never popped, does not: beancount's builder reports it and the
/// parser carries on, so the indented line is still `unexpected INDENT`
/// (bean-check 3.2.3: `poptag #zz` then `  2024-02-30 open Assets:A` is three
/// errors). The one rule for `previous_line_is_a_gap` and
/// `report_no_metadata_continuations`.
const fn swallows_the_next_line(kind: &crate::ParseErrorKind) -> bool {
    !matches!(
        kind,
        crate::ParseErrorKind::InvalidPoptag(_)
            | crate::ParseErrorKind::InvalidPopmeta(_)
            | crate::ParseErrorKind::UnclosedPushtag(_)
            | crate::ParseErrorKind::UnclosedPushmeta(_)
    )
}

/// Whether the line before the one starting at `line_start` leaves an indented
/// line nothing to continue, so beancount reports `unexpected INDENT` there
/// (bean-check 3.2.3): it is blank, missing, a comment at column 0, or one of
/// the undated directives that take no metadata (`option`, `include`,
/// `plugin`, `pushtag`, `poptag`, `pushmeta`, `popmeta`) with no error of its
/// own (`error_starts`, sorted): beancount's recovery from a broken one
/// swallows the indented line. An indented comment continues the directive
/// above.
///
/// A column-0 comment is a line beancount ignores, per
/// [`crate::logos_lexer::beancount_ignores_line`]: `;` and anything, or `*`,
/// `:` or a flag character (`!`, `&`, `#`, `?`, `%`) followed by at least one
/// more character on the line, except `#` starting a tag (`#a1`, `#a b`). A
/// bare marker is a token, not a comment, and beancount reports it on its own
/// line.
///
/// A previous line that starts inside a multi-line string (`multiline_strings`,
/// sorted) is the string's text. Its directive is the one on the line where
/// the string starts, so step back to that line (again, while it too starts
/// inside a string) and apply only the no-metadata check there. Each step
/// goes back over one string, so the walk is bounded by the lines above.
fn previous_line_is_a_gap(
    src: &str,
    line_start: usize,
    multiline_strings: &[std::ops::Range<usize>],
    error_starts: &[usize],
) -> bool {
    let takes_no_metadata = |line: &str| {
        NO_METADATA_DIRECTIVES.iter().any(|(_, keyword)| {
            line.strip_prefix(keyword)
                .is_some_and(|rest| rest.starts_with([' ', '\t']))
        })
    };
    // The string a line starting at `at` starts inside, if any.
    let string_around = |at: usize| {
        let i = multiline_strings.partition_point(|s| s.end <= at);
        multiline_strings.get(i).filter(|s| s.start < at)
    };
    let line_start_of = |at: usize| src[..at].rfind('\n').map_or(0, |i| i + 1);
    // Whether an error starts in `from..to`: a directive that is already a
    // syntax error is no gap, because beancount's recovery from it swallows
    // the indented line after it (`option "a" "b" "c"`).
    let has_an_error = |from: usize, to: usize| {
        let i = error_starts.partition_point(|&s| s < from);
        error_starts.get(i).is_some_and(|&s| s < to)
    };
    let Some(before) = src[..line_start].strip_suffix('\n') else {
        return true;
    };
    let previous_start = line_start_of(before.len());
    if let Some(mut string) = string_around(previous_start) {
        let mut start = line_start_of(string.start);
        while let Some(outer) = string_around(start) {
            string = outer;
            start = line_start_of(string.start);
        }
        let end = src[start..].find('\n').map_or(src.len(), |i| start + i);
        return takes_no_metadata(&src[start..end]) && !has_an_error(start, line_start);
    }
    // Not trimmed of `\r`: a `#\r` line is a comment, as flex's `.` takes the
    // `\r` (bean-check 3.2.3).
    let previous = &before[previous_start..];
    crate::logos_lexer::beancount_ignores_line(previous)
        || previous.trim_start_matches([' ', '\t', '\r']).is_empty()
        || takes_no_metadata(previous) && !has_an_error(previous_start, line_start)
}

/// Counters the linear-cost tests read (test builds only).
#[cfg(test)]
pub mod test_counters {
    thread_local! {
        /// Bytes `report_invalid_dates` stepped over finding the lines that
        /// hold a bad date, and the stretches between dates, on this thread.
        pub static DATE_LINE_SCANNED_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
        /// Bytes `drop_errors_inside_a_line_error` stepped over: the source
        /// scan for line starts, and each line prefix it lexed (#2787).
        pub static ERROR_LINE_SCANNED_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
        /// Work `report_no_metadata_continuations` did: header tokens and
        /// line bytes stepped over, and errors visited (#2813).
        pub static NO_META_SCANNED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
        /// Keys `report_duplicate_metadata` compared pairwise (#2893).
        pub static DUP_META_COMPARED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }
}

/// The error for [`invalid_value_date`]'s finding, in the BOM frame.
const fn invalid_value_date_error(
    range: std::ops::Range<usize>,
    message: String,
    off: usize,
) -> crate::ParseError {
    crate::ParseError::new(
        crate::ParseErrorKind::InvalidDateValue(message),
        Span::new(range.start + off, range.end + off),
    )
}

/// Parse a directive's `DATE` token. On success returns the
/// `NaiveDate`; on a token whose calendar values don't form a
/// real date (`2024-13-01`, Feb 29 in a non-leap year) emits
/// `InvalidDateValue` with the legacy parser's human-readable
/// message and returns `None`. This mirrors
/// `parser.rs:181-182` so the CST and legacy parsers surface the
/// same diagnostics for malformed dates in directive position.
fn parse_directive_date(
    date_tok: &ast::Date,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> Option<NaiveDate> {
    let text = date_tok.text();
    if let Some(d) = parse_date_token(text) {
        return Some(d);
    }
    let range = date_tok.syntax().text_range();
    let start: u32 = range.start().into();
    let end: u32 = range.end().into();
    let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
    errors.push(crate::ParseError::new(
        crate::ParseErrorKind::InvalidDateValue(crate::diagnostics::describe_invalid_date(text)),
        span,
    ));
    None
}

/// Decode a `STRING` token's text (with surrounding quotes) into its semantic
/// value: quotes stripped, escapes decoded (`\"`→`"`, `\\`→`\`, `\n`/`\t`/`\r`,
/// `\b`/`\f`, unknown escape drops the backslash). `None` if not a well-formed quoted
/// string. Text-based so both the red ([`ast::StringLit::text_decoded`]) and
/// green conversion paths share one source of truth.
pub(super) fn decode_string_token(text: &str) -> Option<String> {
    let bytes = text.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len() - 1] != b'"' {
        return None;
    }
    let raw = &text[1..text.len() - 1];
    if !raw.contains('\\') {
        return Some(raw.to_string());
    }
    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            // Backspace and form feed, as beancount's lexer decodes them
            // (#2672). Every other escape (`\a`, `\v`, `\0`, `\x`, `\u`, ...)
            // drops the backslash there too, so the fallback below matches.
            Some('b') => out.push('\u{8}'),
            Some('f') => out.push('\u{c}'),
            Some(other) => out.push(other),
            None => {}
        }
    }
    Some(out)
}

/// Parse a numeric token. Tolerates leading sign and thousands-
/// separator commas (legacy parser drops them).
pub(super) fn parse_decimal_token(text: &str) -> Option<Decimal> {
    use std::str::FromStr;
    let cleaned: String;
    let s = if text.contains(',') {
        cleaned = text.replace(',', "");
        cleaned.as_str()
    } else {
        text
    };
    Decimal::from_str(s).ok()
}

/// Choose `Int` vs `Number` for a numeric metadata literal.
///
/// Beancount represents integer metadata (`key: 42`) as an int and decimal
/// metadata (`key: 42.0`) as a `Decimal`. `text` is the original (unsigned)
/// NUMBER token: a literal with no `.` or exponent that fits in `i64` becomes
/// `Int`; decimals, exponents, and out-of-range integers stay `Number`. `value`
/// is the parsed (and sign-applied) magnitude. (Thousands-separator commas are
/// irrelevant to integer-ness, so they aren't stripped before the check.)
pub(super) fn number_meta_value(text: &str, value: Decimal) -> MetaValue {
    use rust_decimal::prelude::ToPrimitive;
    if !text.contains('.')
        && !text.contains('e')
        && !text.contains('E')
        && let Some(i) = value.to_i64()
    {
        return MetaValue::Int(i);
    }
    MetaValue::Number(value)
}

// ---- Span helpers ----------------------------------------------

/// Convert a CST node's [`rowan::TextRange`] (relative to the
/// post-BOM source frame) into a [`Span`] in the original-source
/// frame.
fn node_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start: u32 = range.start().into();
    let end: u32 = range.end().into();
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

/// The tokens [`value_groups`] skips: whitespace, line ends and `;` comments.
/// Every caller of the walk (custom values, pushmeta values, and the
/// expression check in both trees) filters with this one predicate, so they
/// all see the same token stream.
pub(super) const fn is_value_walk_trivia(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::WHITESPACE | crate::SyntaxKind::NEWLINE | crate::SyntaxKind::COMMENT
    )
}

/// Trivia kinds that don't count toward a span's start/end when
/// matching the legacy parser's span convention.
///
/// Covers WHITESPACE / NEWLINE plus EVERY comment-trivia kind
/// (`COMMENT`, `PERCENT_COMMENT`, `SHEBANG`, `EMACS_DIRECTIVE`)
/// so files with ledger-style `%` comments or org-mode
/// `#!`/`#+` lines have the same span/header-tracking behavior
/// as files with only `;` comments. Mirrors
/// `SyntaxKind::is_trivia()` minus `BOM` - a mid-file BOM byte
/// is an error to surface (`extract_inline_token_errors` /
/// `classify_recovery_error`), not trivia to silently skip.
pub(super) const fn is_trivia_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::WHITESPACE
            | crate::SyntaxKind::NEWLINE
            | crate::SyntaxKind::COMMENT
            | crate::SyntaxKind::PERCENT_COMMENT
            | crate::SyntaxKind::SHEBANG
            | crate::SyntaxKind::EMACS_DIRECTIVE
    )
}

/// Span policy for `Posting`: the legacy parser ends the posting
/// span at the position just before the line's terminating
/// NEWLINE. The CST node's range INCLUDES the terminator
/// NEWLINE; trim it by using the NEWLINE token's start position.
/// We look at the FIRST direct-child NEWLINE token because
/// posting-attached metadata sub-lines (which have their own
/// inner NEWLINEs) come after the line terminator and shouldn't
/// extend the posting-line span.
fn posting_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start: u32 = range.start().into();
    let end_raw: u32 = range.end().into();
    // Postings have no inter-directive leading trivia: their
    // first direct-child NEWLINE IS the terminator.
    let end = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .find(|t| t.kind() == crate::SyntaxKind::NEWLINE)
        .map_or(end_raw, |t| u32::from(t.text_range().start()));
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

/// Span policy for non-Directive single-line constructs that
/// participate in inter-directive trivia attachment (Option,
/// Include, Plugin). Unlike Posting these may have leading
/// trivia (blank-line NEWLINEs, comments) inside the node from
/// the Directive-Terminator Rule. Start at the first non-trivia
/// content token; end at the first NEWLINE after that.
fn single_line_directive_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start_raw: u32 = range.start().into();
    let end_raw: u32 = range.end().into();
    let mut content_start: Option<u32> = None;
    let mut terminator: Option<u32> = None;
    for t in node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
    {
        if content_start.is_none() {
            if !is_trivia_kind(t.kind()) {
                content_start = Some(u32::from(t.text_range().start()));
            }
        } else if t.kind() == crate::SyntaxKind::NEWLINE {
            terminator = Some(u32::from(t.text_range().start()));
            break;
        }
    }
    let start = content_start.unwrap_or(start_raw);
    let end = terminator.unwrap_or(end_raw);
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

/// Count the root's Directive-castable children on the **green** tree: a
/// slice walk, zero allocation, unlike `source_file.directives().count()`,
/// whose red-tree walk materializes a rowan `NodeData` per child (~2M
/// allocations on a 2M-directive ledger). Used purely as a `Vec`
/// capacity hint; an over-count is fine.
fn directive_child_count(source_file: &SourceFile) -> usize {
    source_file
        .syntax()
        .green()
        .children()
        .filter(|child| match child {
            rowan::NodeOrToken::Node(n) => ast::Directive::can_cast(
                <crate::BeancountLanguage as rowan::Language>::kind_from_raw(n.kind()),
            ),
            rowan::NodeOrToken::Token(_) => false,
        })
        .count()
}

/// Span policy for top-level directives: legacy directives start
/// at the first content character (skipping leading trivia from
/// the Directive-Terminator Rule) and extend through any
/// inter-directive trivia up to where the NEXT directive begins.
/// Computed in a post-pass since each directive's end depends on
/// the next one's start.
fn fixup_directive_spans(
    source_file: &SourceFile,
    bom_offset: u32,
    converted_nodes: &[crate::SyntaxNode],
    directives: &mut [Spanned<Directive>],
) {
    debug_assert_eq!(
        converted_nodes.len(),
        directives.len(),
        "converted_nodes and directives must be parallel arrays"
    );

    // Walk EVERY top-level Directive-castable child (including
    // pushtag/poptag/pushmeta/popmeta that we filter out of the
    // ParseResult) so the "next directive's start" boundary used
    // for span end-fixup matches the legacy parser: there, each
    // visible directive's span ends at the next /input/
    // directive's start, regardless of whether that next
    // directive is preserved.
    // Same green count as the conversion loop's capacity hint: this walk
    // produces one entry per Directive-castable child, so it is exact here
    // rather than an upper bound.
    let mut all_starts: Vec<(usize, usize)> =
        Vec::with_capacity(directive_child_count(source_file));
    all_starts.extend(
        source_file
            .syntax()
            .children()
            .filter(|n| ast::Directive::can_cast(n.kind()))
            .map(|n| {
                let raw_start: u32 = n.text_range().start().into();
                let content_start = n
                    .descendants_with_tokens()
                    .filter_map(rowan::NodeOrToken::into_token)
                    .find(|t| !is_trivia_kind(t.kind()))
                    .map_or_else(
                        || (raw_start + bom_offset) as usize,
                        |t| (u32::from(t.text_range().start()) + bom_offset) as usize,
                    );
                ((raw_start + bom_offset) as usize, content_start)
            }),
    );

    // `all_starts` is built from `children()`, i.e. siblings in document
    // order, and sibling text ranges are disjoint and increasing — so it is
    // sorted ascending on `raw_start` and every key is unique. The lookup
    // below binary-searches on that.
    debug_assert!(
        all_starts.windows(2).all(|w| w[0].0 < w[1].0),
        "all_starts must be strictly ascending by raw_start for the binary \
         search below; sibling text ranges are disjoint and increasing, so a \
         failure here means the enumeration is no longer document-ordered",
    );

    let source_end: usize =
        (u32::from(source_file.syntax().text_range().end()) + bom_offset) as usize;

    // For each converted directive, find its position in the all
    // list by raw_start (which is unique per CST node), then use
    // the NEXT all_starts content_start as its span end.
    //
    // INVARIANT: every node in `converted_nodes` was yielded by
    // `source_file.directives()`, which is the same iteration
    // `all_starts` filters from. So `position` always succeeds in
    // well-formed input. Falling back to the node's own
    // `text_range` rather than panicking keeps the parser usable
    // when a future change to the typed-AST surface ever de-syncs
    // those two enumerations - a `panic!()` reachable from user
    // input is a `#![forbid(unsafe_code)]`-class regression for an
    // LSP/WASM consumer.
    for (i, spanned) in directives.iter_mut().enumerate() {
        let node = &converted_nodes[i];
        let raw_start: usize = (u32::from(node.text_range().start()) + bom_offset) as usize;
        let node_end: usize = (u32::from(node.text_range().end()) + bom_offset) as usize;
        // Binary search, NOT a linear `position()` scan. This loop runs once
        // per directive over an `all_starts` that has one entry per
        // directive, so a linear probe made span fixup O(N^2) in the
        // directive count. Measured on the `simple` profiling shape: 10x the
        // transactions cost 21.8x the instructions, and cachegrind put ~40%
        // of a 20k-transaction run inside this one scan and its slice-iterator
        // internals. It is invisible on small inputs, which is why it sat
        // here — at 2k transactions the same scan is under 2%.
        //
        // Semantics are unchanged: keys are unique (see the debug_assert
        // above), so where `position` found the sole match, `binary_search`
        // finds the same one, and a miss still falls through to the
        // defensive branch below rather than panicking.
        if let Ok(pos) = all_starts.binary_search_by_key(&raw_start, |(rs, _)| *rs) {
            let start = all_starts[pos].1;
            let end = all_starts
                .get(pos + 1)
                .map_or(source_end, |(_, content)| *content);
            spanned.span = Span::new(start, end);
        } else {
            // Defensive fallback: match the success-path
            // convention by also trimming leading trivia. Without
            // this trim the fallback span would underline blank
            // lines / column-0 comments above the directive when
            // LSP/miette renders the diagnostic, even though the
            // directive itself starts further down.
            let content_start = node
                .descendants_with_tokens()
                .filter_map(rowan::NodeOrToken::into_token)
                .find(|t| !is_trivia_kind(t.kind()))
                .map_or(raw_start, |t| {
                    (u32::from(t.text_range().start()) + bom_offset) as usize
                });
            spanned.span = Span::new(content_start, node_end);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `drop_errors_inside_a_line_error` (#2787) scans the source once for
    /// line starts and lexes each broken line's prefix once, so many broken
    /// lines, or many unreadable tokens on one long line, stay linear.
    /// `report_no_metadata_continuations` (#2813) visits each header token,
    /// each checked line and each error once, so many `option` / `pushtag`
    /// lines with an indented line after each, among many other errors,
    /// stay linear.
    #[test]
    fn test_report_no_metadata_continuations_is_linear_in_the_input() {
        const N: usize = 20_000;
        let src = "pushtag #t\n  ; c\npoptag #t\n  2024-01-01 open\n".repeat(N);
        test_counters::NO_META_SCANNED.with(|c| c.set(0));
        let result = crate::parse(&src);
        let scanned = test_counters::NO_META_SCANNED.with(std::cell::Cell::get);
        assert!(
            scanned <= 2 * src.len(),
            "visited {scanned} units of a {}-byte input",
            src.len()
        );
        let indented = result
            .errors
            .iter()
            .filter(|e| e.to_string().contains("takes no metadata"))
            .count();
        assert_eq!(indented, N);
    }

    /// `report_duplicate_metadata` (#2893) compares a key pairwise only while
    /// its owner has a handful, then through a set, so a transaction with
    /// many keys, repeated or not, stays linear.
    #[test]
    fn test_report_duplicate_metadata_is_linear_in_the_keys() {
        const N: usize = 20_000;
        let mut keys = String::new();
        for i in 0..N {
            keys.push_str(&format!("  k{i}: 1\n"));
        }
        let src = format!(
            "2024-01-01 *\n{keys}{keys}  Assets:A  1 USD\n{}  Assets:B  -1 USD\n",
            keys.replace("  k", "    k")
        );
        test_counters::DUP_META_COMPARED.with(|c| c.set(0));
        let result = crate::parse(&src);
        let compared = test_counters::DUP_META_COMPARED.with(std::cell::Cell::get);
        // At most 16 keys per owner are compared pairwise, whatever N is.
        assert!(compared <= 1_000, "compared {compared} keys pairwise");
        let repeats = result
            .errors
            .iter()
            .filter(|e| e.to_string().contains("duplicate metadata field on entry"))
            .count();
        assert_eq!(repeats, N);
    }

    #[test]
    fn test_drop_errors_inside_a_line_error_is_linear_in_the_input() {
        const N: usize = 20_000;
        let head = "2024-01-01 open Assets:A\n2024-01-02 *\n  Assets:A  1 USD\n";
        let many_lines = format!("{head}{}", "  * h\n".repeat(N));
        let one_line = format!("{head}  *{}\n", " h".repeat(N));
        for (label, src, errors) in [("many lines", many_lines, N), ("one line", one_line, N)] {
            test_counters::ERROR_LINE_SCANNED_BYTES.with(|c| c.set(0));
            let result = crate::parse(&src);
            let scanned = test_counters::ERROR_LINE_SCANNED_BYTES.with(std::cell::Cell::get);
            assert!(
                scanned <= 3 * src.len(),
                "{label}: stepped over {scanned} bytes of a {}-byte input",
                src.len()
            );
            assert_eq!(result.errors.len(), errors, "{label}");
        }
    }

    /// Reporting bad dates must stay linear in the input (#2868 review): one
    /// `custom` line of 40,000 bad dates took 63 s when each date looked back
    /// and ahead for its own line's bounds. The bytes stepped over finding
    /// the lines, and the stretches between dates, must stay within three
    /// passes over the source, whether the dates share one line or each has
    /// its own.
    #[test]
    fn test_report_invalid_dates_is_linear_in_the_input() {
        const N: usize = 20_000;
        let one_line = "2024-01-02 custom \"x\"".to_string() + &" 2024-02-30".repeat(N) + "\n";
        let many_lines =
            "2024-01-02 custom \"x\" 2024-02-30\n2024-01-02 custom \"y\" `\n".repeat(N);
        for (label, src) in [("one line", one_line), ("many lines", many_lines)] {
            test_counters::DATE_LINE_SCANNED_BYTES.with(|c| c.set(0));
            let result = crate::parse(&src);
            let scanned = test_counters::DATE_LINE_SCANNED_BYTES.with(std::cell::Cell::get);
            assert!(
                scanned <= 3 * src.len(),
                "{label}: stepped over {scanned} bytes of a {}-byte input",
                src.len()
            );
            let named = result
                .errors
                .iter()
                .filter(|e| matches!(e.kind, crate::ParseErrorKind::InvalidDateValue(_)))
                .count();
            assert_eq!(named, N, "{label}");
        }
    }

    /// A directive's span ends at the next *input* directive's content start,
    /// INCLUDING directives filtered out of the `ParseResult`
    /// (`pushtag`/`poptag`/`pushmeta`/`popmeta`).
    ///
    /// This is the case that makes `all_starts` longer than `directives`, so
    /// it is the one that breaks if the lookup ever stops keying on the CST
    /// node's own start — e.g. "optimizing" the binary search into an index
    /// into `directives`, which would end the `open` span at the transaction
    /// instead of at the `pushtag` between them.
    #[test]
    fn spans_end_at_the_next_input_directive_even_when_it_is_filtered_out() {
        let src = "2024-01-01 open Assets:Bank USD\n\
                   pushtag #trip\n\
                   2024-01-02 * \"a\"\n  Assets:Bank 1 USD\n  Assets:Other\n\
                   poptag #trip\n\
                   2024-01-03 close Assets:Bank\n";
        let parsed = crate::parse(src);

        let at = |needle: &str| src.find(needle).expect("fixture contains it");
        let spans: Vec<(usize, usize)> = parsed
            .directives
            .iter()
            .map(|d| (d.span.start, d.span.end))
            .collect();

        assert_eq!(
            spans,
            vec![
                // `open` stops at `pushtag`, NOT at the transaction.
                (0, at("pushtag")),
                // the transaction stops at `poptag`, NOT at `close`.
                (at("2024-01-02"), at("poptag")),
                // the last directive runs to end of source.
                (at("2024-01-03"), src.len()),
            ],
            "pushtag/poptag are filtered from `directives` but still bound the \
             preceding directive's span",
        );
    }

    /// Match a `SyntaxError` by message prefix rather than by `Debug` output.
    /// The `Debug` rendering of `ParseErrorKind` can change without any
    /// semantic change, and an assertion that reads it would fail for no
    /// reason; the variant plus the message prefix is the real contract.
    fn has_syntax_error(result: &ParseResult, prefix: &str) -> bool {
        result.errors.iter().any(
            |e| matches!(&e.kind, crate::ParseErrorKind::SyntaxError(m) if m.starts_with(prefix)),
        )
    }

    fn assert_directive_count(result: &ParseResult, expected: usize) {
        assert_eq!(
            result.directives.len(),
            expected,
            "directive count mismatch: {:#?}",
            result.directives
        );
    }

    #[test]
    fn open_directive_basic() {
        let src = "2024-01-15 open Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open, got {:?}", result.directives[0].value);
        };
        assert_eq!(open.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(open.account.as_str(), "Assets:Cash");
        assert!(open.currencies.is_empty());
        assert!(open.booking.is_none());
        assert!(open.meta.is_empty());
    }

    #[test]
    fn open_directive_with_currencies_and_booking() {
        let src = "2024-01-15 open Assets:Brokerage USD,EUR \"STRICT\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        let currencies: Vec<&str> = open.currencies.iter().map(Currency::as_str).collect();
        assert_eq!(currencies, vec!["USD", "EUR"]);
        assert_eq!(open.booking.as_deref(), Some("STRICT"));
    }

    #[test]
    fn open_directive_with_metadata() {
        let src = "2024-01-15 open Assets:Cash\n  note: \"main checking\"\n  number: 42\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(
            open.meta.get("note"),
            Some(&MetaValue::String("main checking".to_string()))
        );
        assert_eq!(
            open.meta.get("number"),
            // Unquoted integer metadata is now `Int`, not `Number`.
            Some(&MetaValue::Int(42))
        );
    }

    #[test]
    fn close_directive_basic() {
        let src = "2024-12-31 close Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Close(close) = &result.directives[0].value else {
            panic!("expected Close, got {:?}", result.directives[0].value);
        };
        assert_eq!(close.date, naive_date(2024, 12, 31).unwrap());
        assert_eq!(close.account.as_str(), "Assets:Cash");
    }

    #[test]
    fn commodity_directive_basic() {
        let src = "2024-01-01 commodity HOOL\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Commodity(c) = &result.directives[0].value else {
            panic!("expected Commodity");
        };
        assert_eq!(c.currency.as_str(), "HOOL");
    }

    #[test]
    fn bom_offset_is_included_in_spans() {
        let src = "\u{FEFF}2024-01-15 open Assets:Cash\n";
        let result = parse_via_cst(src);
        assert!(result.has_leading_bom);
        let span = result.directives[0].span;
        assert_eq!(span.start, 3, "span should include BOM offset");
    }

    #[test]
    fn note_directive_basic() {
        let src = "2024-01-15 note Assets:Cash \"deposit received\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Note(note) = &result.directives[0].value else {
            panic!("expected Note");
        };
        assert_eq!(note.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(note.account.as_str(), "Assets:Cash");
        assert_eq!(note.comment, "deposit received");
    }

    #[test]
    fn document_directive_basic() {
        let src = "2024-01-15 document Assets:Cash \"/path/to/file.pdf\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Document(d) = &result.directives[0].value else {
            panic!("expected Document");
        };
        assert_eq!(d.account.as_str(), "Assets:Cash");
        assert_eq!(d.path, "/path/to/file.pdf");
        // tags/links currently unimplemented - pin as empty.
        assert!(d.tags.is_empty());
        assert!(d.links.is_empty());
    }

    #[test]
    fn event_directive_basic() {
        let src = "2024-01-15 event \"location\" \"Berlin\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Event(e) = &result.directives[0].value else {
            panic!("expected Event");
        };
        assert_eq!(e.event_type, "location");
        assert_eq!(e.value, "Berlin");
    }

    #[test]
    fn query_directive_basic() {
        let src = "2024-01-15 query \"income\" \"SELECT account, sum(position)\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Query(q) = &result.directives[0].value else {
            panic!("expected Query");
        };
        assert_eq!(q.name, "income");
        assert_eq!(q.query, "SELECT account, sum(position)");
    }

    #[test]
    fn price_directive_basic() {
        let src = "2024-01-15 price USD 1.10 EUR\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Price(p) = &result.directives[0].value else {
            panic!("expected Price");
        };
        assert_eq!(p.currency.as_str(), "USD");
        assert_eq!(p.amount.number, Decimal::new(110, 2));
        assert_eq!(p.amount.currency.as_str(), "EUR");
    }

    #[test]
    fn balance_directive_basic() {
        let src = "2024-06-30 balance Assets:Cash 100.00 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Balance(b) = &result.directives[0].value else {
            panic!("expected Balance");
        };
        assert_eq!(b.account.as_str(), "Assets:Cash");
        assert_eq!(b.amount.number, Decimal::new(10000, 2));
        assert_eq!(b.amount.currency.as_str(), "USD");
        assert!(b.tolerance.is_none());
    }

    #[test]
    fn balance_directive_with_explicit_tolerance() {
        let src = "2024-06-30 balance Assets:Cash 100.00 ~ 0.05 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Balance(b) = &result.directives[0].value else {
            panic!("expected Balance");
        };
        assert_eq!(b.amount.number, Decimal::new(10000, 2));
        assert_eq!(b.tolerance, Some(Decimal::new(5, 2)));
    }

    #[test]
    fn pad_directive_basic() {
        let src = "2024-01-01 pad Assets:Cash Equity:Opening-Balances\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Pad(p) = &result.directives[0].value else {
            panic!("expected Pad");
        };
        assert_eq!(p.account.as_str(), "Assets:Cash");
        assert_eq!(p.source_account.as_str(), "Equity:Opening-Balances");
    }

    #[test]
    fn custom_directive_basic() {
        let src = "2024-01-01 custom \"budget\" \"food\" 500 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Custom(c) = &result.directives[0].value else {
            panic!("expected Custom");
        };
        assert_eq!(c.custom_type, "budget");
        assert_eq!(c.values.len(), 2);
        assert_eq!(c.values[0], MetaValue::String("food".to_string()));
        // 500 USD becomes an Amount (NUMBER + CURRENCY adjacent).
        let MetaValue::Amount(amt) = &c.values[1] else {
            panic!("expected Amount, got {:?}", c.values[1]);
        };
        assert_eq!(amt.number, Decimal::from(500));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn custom_directive_heterogeneous_values() {
        let src = "2024-01-01 custom \"test\" Assets:Cash TRUE 42 2024-06-15\n";
        let result = parse_via_cst(src);
        let Directive::Custom(c) = &result.directives[0].value else {
            panic!("expected Custom");
        };
        assert_eq!(c.values.len(), 4);
        assert!(matches!(c.values[0], MetaValue::Account(_)));
        assert_eq!(c.values[1], MetaValue::Bool(true));
        assert_eq!(c.values[2], MetaValue::Int(42));
        assert!(matches!(c.values[3], MetaValue::Date(_)));
    }

    #[test]
    fn number_meta_value_int_vs_decimal_discriminator() {
        use rust_decimal_macros::dec;
        // Integer literals -> Int (the token text is unsigned; `value` carries
        // the sign, e.g. `precision: -1` parses the token "1" with value -1).
        assert_eq!(number_meta_value("42", dec!(42)), MetaValue::Int(42));
        assert_eq!(number_meta_value("0", dec!(0)), MetaValue::Int(0));
        assert_eq!(number_meta_value("1", dec!(-1)), MetaValue::Int(-1));
        // Decimal point -> Number.
        assert_eq!(
            number_meta_value("42.0", dec!(42.0)),
            MetaValue::Number(dec!(42.0))
        );
        // Exponent -> Number. The lexer doesn't currently emit exponent NUMBER
        // tokens, so this isn't reachable from real input today; it pins the
        // helper's `e`/`E` guard against a future lexer that does.
        assert_eq!(
            number_meta_value("1e3", dec!(1000)),
            MetaValue::Number(dec!(1000))
        );
        // i64 overflow stays Number (within Decimal's range).
        let huge = "99999999999999999999999999";
        let huge_dec = Decimal::from_str_exact(huge).unwrap();
        assert_eq!(
            number_meta_value(huge, huge_dec),
            MetaValue::Number(huge_dec)
        );
    }

    #[test]
    fn option_directive_populates_options_field() {
        let src = "option \"title\" \"My Ledger\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].0, "title");
        assert_eq!(result.options[0].1, "My Ledger");
    }

    #[test]
    fn include_directive_populates_includes_field() {
        let src = "include \"shared.beancount\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.includes.len(), 1);
        assert_eq!(result.includes[0].0, "shared.beancount");
    }

    #[test]
    fn plugin_directive_with_config() {
        let src = "plugin \"my.plugin\" \"cfg\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.plugins.len(), 1);
        assert_eq!(result.plugins[0].0, "my.plugin");
        assert_eq!(result.plugins[0].1.as_deref(), Some("cfg"));
    }

    #[test]
    fn plugin_directive_without_config() {
        let src = "plugin \"my.plugin\"\n";
        let result = parse_via_cst(src);
        assert_eq!(result.plugins.len(), 1);
        assert_eq!(result.plugins[0].0, "my.plugin");
        assert!(result.plugins[0].1.is_none());
    }

    // ---- Transaction converter tests ------------------------------

    #[test]
    fn transaction_basic_two_postings() {
        let src = "2024-01-15 * \"Coffee Shop\" \"Morning coffee\"\n  \
                   Expenses:Food:Coffee  5.00 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(t.flag, '*');
        assert_eq!(
            t.payee.as_ref().map(InternedStr::as_str),
            Some("Coffee Shop")
        );
        assert_eq!(t.narration.as_str(), "Morning coffee");
        assert_eq!(t.postings.len(), 2);

        let p0 = &t.postings[0].value;
        assert_eq!(p0.account.as_str(), "Expenses:Food:Coffee");
        let Some(IncompleteAmount::Complete(amt)) = &p0.units else {
            panic!("expected complete units, got {:?}", p0.units);
        };
        assert_eq!(amt.number, Decimal::new(500, 2));
        assert_eq!(amt.currency.as_str(), "USD");

        let p1 = &t.postings[1].value;
        assert_eq!(p1.account.as_str(), "Assets:Cash");
        assert!(p1.units.is_none(), "auto-posting has no units");
    }

    #[test]
    fn transaction_narration_only_no_payee() {
        let src = "2024-01-15 ! \"Pending\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.flag, '!');
        assert!(t.payee.is_none());
        assert_eq!(t.narration.as_str(), "Pending");
    }

    #[test]
    fn transaction_three_plus_header_strings_surface_last_as_narration() {
        // A header with 3+ strings is ambiguous (the grammar caps payee+narration
        // at two); the lossless CST still keeps all of them, so the typed surface
        // drops the payee and surfaces only the LAST string as narration. Locks
        // the `(Some, Some, Some(c)) => it.last().unwrap_or(c)` arm.
        let src = "2024-01-15 * \"a\" \"b\" \"c\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert!(t.payee.is_none(), "3+ strings drop the payee");
        assert_eq!(t.narration.as_str(), "c", "last string becomes narration");
    }

    #[test]
    fn transaction_with_no_flag_is_reported_and_kept() {
        // beancount: `syntax error, unexpected STRING` (#2905). Reported at
        // the string; the transaction is kept, as for every header defect.
        let src = "2024-01-15 \"Implied\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
        assert_eq!(
            (result.errors[0].span.start, result.errors[0].span.end),
            (11, 20)
        );
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.flag, '*');
    }

    #[test]
    fn transaction_with_tags_and_links() {
        let src = "2024-01-15 * \"Coffee\" #daily ^trip1\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.tags.len(), 1);
        assert_eq!(t.tags[0].as_str(), "daily");
        assert_eq!(t.links.len(), 1);
        assert_eq!(t.links[0].as_str(), "trip1");
    }

    #[test]
    fn transaction_with_signed_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash  -5.00 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete units");
        };
        assert_eq!(amt.number, Decimal::new(-500, 2));
    }

    #[test]
    fn transaction_with_posting_flag() {
        let src = "2024-01-15 * \"x\"\n  ! Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.postings[0].value.flag, Some('!'));
    }

    #[test]
    fn transaction_with_cost_spec_per_unit() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL {500.00 USD}\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let cost = t.postings[0].value.cost.as_ref().expect("cost spec");
        assert!(!cost.merge);
        let Some(CostNumber::PerUnit { value }) = &cost.number else {
            panic!("expected PerUnit");
        };
        assert_eq!(*value, Decimal::new(50000, 2));
        assert_eq!(cost.currency.as_ref().unwrap().as_str(), "USD");
    }

    #[test]
    fn transaction_with_cost_spec_total() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL {{5000 USD}}\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let cost = t.postings[0].value.cost.as_ref().expect("cost spec");
        let Some(CostNumber::Total { value }) = &cost.number else {
            panic!("expected Total");
        };
        assert_eq!(*value, Decimal::from(5000));
    }

    #[test]
    fn transaction_with_price_annotation_unit() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL @ 510 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let price = t.postings[0]
            .value
            .price
            .as_ref()
            .expect("price annotation");
        assert!(price.is_unit());
        let Some(IncompleteAmount::Complete(amt)) = &price.amount else {
            panic!("expected complete price amount");
        };
        assert_eq!(amt.number, Decimal::from(510));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn transaction_with_price_annotation_total() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL @@ 5100 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let price = t.postings[0]
            .value
            .price
            .as_ref()
            .expect("price annotation");
        assert!(!price.is_unit(), "@@ is total form");
    }

    // ---- regression tests for review findings (#1281) ----------

    #[test]
    fn document_directive_preserves_tags_and_links() {
        // Finding 1: convert_document was filling tags/links empty
        // unconditionally. Legacy parse_document_directive collects
        // trailing `#tag` / `^link` tokens after the path STRING.
        let src = "2024-06-01 document Assets:Bank \"stmt.pdf\" #quarter1 ^scan42 #urgent\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Document(doc) = &result.directives[0].value else {
            panic!("expected Document");
        };
        let tags: Vec<&str> = doc.tags.iter().map(Tag::as_str).collect();
        let links: Vec<&str> = doc.links.iter().map(Link::as_str).collect();
        assert_eq!(tags, vec!["quarter1", "urgent"]);
        assert_eq!(links, vec!["scan42"]);
    }

    #[test]
    fn open_directive_rejects_invalid_booking_method() {
        // Finding 2: convert_open accepted any booking string; legacy
        // validates against [FIFO, STRICT, STRICT_WITH_SIZE, LIFO,
        // HIFO, NONE, AVERAGE] and on mismatch drops the directive
        // AND emits InvalidBookingMethod.
        let src = "2024-01-01 open Assets:Bank USD \"GARBAGE\"\n";
        let result = parse_via_cst(src);
        assert_eq!(result.directives.len(), 0, "directive should be dropped");
        assert_eq!(result.errors.len(), 1);
        let err = &result.errors[0];
        assert!(
            matches!(
                &err.kind,
                crate::ParseErrorKind::InvalidBookingMethod(s) if s == "GARBAGE"
            ),
            "expected InvalidBookingMethod, got {:?}",
            err.kind,
        );
    }

    #[test]
    fn open_directive_accepts_all_valid_booking_methods() {
        for method in VALID_BOOKING_METHODS {
            let src = format!("2024-01-01 open Assets:Bank USD \"{method}\"\n");
            let result = parse_via_cst(&src);
            assert!(
                result.errors.is_empty(),
                "{method} rejected: {:?}",
                result.errors
            );
            let Directive::Open(open) = &result.directives[0].value else {
                panic!("{method}: expected Open");
            };
            assert_eq!(open.booking.as_deref(), Some(*method));
        }
    }

    #[test]
    fn unclosed_pushtag_at_eof_emits_diagnostic() {
        // Finding 3: legacy emits one UnclosedPushtag per leftover
        // tag at EOF, pointing at the originating push directive.
        let src = "pushtag #active\n2024-01-01 open Assets:Bank USD\n";
        let result = parse_via_cst(src);
        let unclosed: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::UnclosedPushtag(t) => Some(t.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unclosed, vec!["active".to_string()]);
    }

    #[test]
    fn unclosed_pushmeta_at_eof_emits_diagnostic() {
        // Finding 4: same as pushtag, for pushmeta.
        let src = "pushmeta location: \"NYC\"\n2024-01-01 open Assets:Bank USD\n";
        let result = parse_via_cst(src);
        let unclosed: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::UnclosedPushmeta(k) => Some(k.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unclosed, vec!["location".to_string()]);
    }

    #[test]
    fn invalid_poptag_on_mismatch_emits_diagnostic() {
        // Finding 5: poptag for a tag never pushed should error,
        // not silently no-op.
        let src = "pushtag #foo\npoptag #bar\npoptag #foo\n";
        let result = parse_via_cst(src);
        let mismatches: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidPoptag(t) => Some(t.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(mismatches, vec!["bar".to_string()]);
        // and the matching #foo poptag should leave NO unclosed
        // diagnostic - i.e. the stack is empty after the matched pop.
        let leftover: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::UnclosedPushtag(_)))
            .collect();
        assert!(leftover.is_empty(), "unexpected leftover: {leftover:?}");
    }

    #[test]
    fn invalid_popmeta_on_mismatch_emits_diagnostic() {
        // Finding 6: popmeta for a key never pushed should error,
        // not silently no-op. Also checks Vec-stack shadow semantics:
        // pushmeta x: 1; pushmeta x: 2; popmeta x leaves x=1 active.
        let src = "pushmeta location: \"NYC\"\npopmeta nope:\npopmeta location:\n";
        let result = parse_via_cst(src);
        let mismatches: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidPopmeta(k) => Some(k.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(mismatches, vec!["nope".to_string()]);
        let leftover: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::UnclosedPushmeta(_)))
            .collect();
        assert!(leftover.is_empty(), "unexpected leftover: {leftover:?}");
    }

    #[test]
    fn pushmeta_shadow_pop_restores_prior_value() {
        // Vec-stack semantics (the reason meta_stack isn't a HashMap):
        // shadow-pop must restore the prior value, not delete the key.
        let src = "pushmeta loc: \"NYC\"\n\
                   pushmeta loc: \"LDN\"\n\
                   popmeta loc:\n\
                   2024-01-01 * \"t\"\n  Assets:A  1 USD\n  Assets:B\n\
                   popmeta loc:\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(
            txn.meta.get("loc"),
            Some(&MetaValue::String("NYC".to_string())),
            "shadow pop should restore NYC, got {:?}",
            txn.meta.get("loc"),
        );
    }

    #[test]
    fn error_recovery_classifies_bom_in_directive_body() {
        // Finding 7: error-recovery path should distinguish BOM-in-
        // line from a generic SyntaxError so users see the
        // BOM-removal hint instead of "unexpected input".
        let src = "garbage\u{FEFF}content\n";
        let result = parse_via_cst(src);
        let bom_errors: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .collect();
        assert_eq!(bom_errors.len(), 1, "errors: {:?}", result.errors);
        assert!(
            bom_errors[0].hint.is_some(),
            "BomInDirectiveBody should carry BOM_REMOVAL_HINT",
        );
    }

    #[test]
    fn error_recovery_emits_both_invalid_account_and_bom_for_dual_line() {
        // Round-2 finding: legacy `parser.rs:2258-2263` emits a
        // SECONDARY `BomInDirectiveBody` whenever the line ALSO
        // contains a BOM byte and the primary diagnostic isn't
        // BOM itself. Without this, a Windows-exported file with
        // a Unicode account AND an internal BOM loses the BOM
        // hint entirely. The BOM stands alone after a space: glued to the
        // account it would be part of the account token, as in beancount
        // (#2910), and no stray BOM.
        let src = "garbage Assets:Café \u{FEFF}content\n";
        let result = parse_via_cst(src);
        let invalid_account_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::InvalidAccount(_)))
            .count();
        let bom_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .count();
        assert_eq!(
            invalid_account_count, 1,
            "expected one InvalidAccount: {:?}",
            result.errors
        );
        assert_eq!(
            bom_count, 1,
            "expected secondary BomInDirectiveBody: {:?}",
            result.errors
        );
        // The secondary BOM diagnostic must carry the hint so
        // miette renders the remediation step.
        let bom_err = result
            .errors
            .iter()
            .find(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .unwrap();
        assert!(bom_err.hint.is_some());
    }

    #[test]
    fn error_recovery_classifies_unicode_account() {
        // Finding 7: a Unicode-character account name (Assets:Café)
        // should surface as InvalidAccount, not generic SyntaxError.
        // We embed it in a malformed line so the parser routes to
        // the error-recovery path.
        let src = "garbage Assets:Café content\n";
        let result = parse_via_cst(src);
        let unicode_errors: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidAccount(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unicode_errors, vec!["Assets:Café".to_string()]);
    }

    #[test]
    fn transaction_with_pipe_emits_deprecated_pipe_symbol() {
        // Finding 7 (transaction path): legacy emits
        // DeprecatedPipeSymbol when a `|` separates payee/narration.
        let src = "2024-01-15 * \"Acme\" | \"invoice\"\n  Assets:Cash  -5 USD\n  Expenses:X\n";
        let result = parse_via_cst(src);
        let pipe_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::DeprecatedPipeSymbol))
            .count();
        assert_eq!(pipe_count, 1, "errors: {:?}", result.errors);
        // and the transaction itself is kept (legacy behavior).
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn transaction_trailing_comments_after_final_posting() {
        // Finding 8: comments that appear AFTER the last posting
        // but inside the transaction body belong to
        // Transaction::trailing_comments, not lost.
        let src = "2024-01-15 * \"x\"\n  \
                   Assets:Cash  -5 USD\n  \
                   Expenses:X\n  \
                   ; trailing one\n  \
                   ; trailing two\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(
            t.trailing_comments.len(),
            2,
            "got: {:?}",
            t.trailing_comments
        );
        assert!(t.trailing_comments[0].contains("trailing one"));
        assert!(t.trailing_comments[1].contains("trailing two"));
    }

    // ---- arithmetic AMOUNT evaluation (phase 3.7 flip blocker) -

    #[test]
    fn posting_amount_evaluates_division() {
        // Regression for `test_arithmetic_expressions_consistency`:
        // `120 / 3 USD` must evaluate to 40 USD so the transaction
        // balances. Without this the CST flip breaks every ledger
        // using arithmetic split syntax.
        let src = "2024-01-15 * \"split\"\n  \
                   Expenses:Food   120 / 3 USD\n  \
                   Assets:Bank    -40 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount on posting 0");
        };
        assert_eq!(amt.number, Decimal::from(40));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn posting_amount_evaluates_addition_and_multiplication_precedence() {
        // `2 + 3 * 4 USD` = 14 USD (standard precedence).
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   2 + 3 * 4 USD\n  \
                   Assets:Y   -14 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(14));
    }

    #[test]
    fn posting_amount_evaluates_parens_override_precedence() {
        // `(2 + 3) * 4 USD` = 20 USD.
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   (2 + 3) * 4 USD\n  \
                   Assets:Y   -20 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(20));
    }

    #[test]
    fn posting_amount_evaluates_subtraction_left_associative() {
        // `10 - 3 - 2 USD` = 5 USD (left-associative, not 9).
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   10 - 3 - 2 USD\n  \
                   Assets:Y   -5 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(5));
    }

    #[test]
    fn posting_amount_division_by_zero_drops_number() {
        // `5 / 0 USD` - legacy returns parse error; we return None
        // from the evaluator, which degrades to CurrencyOnly here.
        // The transaction won't balance and downstream validation
        // surfaces that as the user-facing error.
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   5 / 0 USD\n  \
                   Assets:Y\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        // Either the units degrade to CurrencyOnly (number lost)
        // or to None - both are acceptable since the input is
        // semantically invalid. The strict assertion is that we
        // DON'T silently return 5 (the first NUMBER) as the value.
        match &t.postings[0].value.units {
            None | Some(IncompleteAmount::CurrencyOnly(_)) => {}
            other => panic!("div-by-zero leaked: {other:?}"),
        }
    }

    // ---- round-8 final compat regressions (#1282 flip) ---------

    #[test]
    fn indented_top_level_directive_emits_error() {
        // A top-level directive that starts at column N>0 is a
        // syntax error per the Beancount spec; the CST grammar
        // accepts it silently, so the converter has to surface
        // the diagnostic at directive-content-start position.
        let src = "2020-07-28 open Assets:Foo\n  2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        let indent_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("column 0"),
                _ => false,
            })
            .count();
        assert_eq!(
            indent_errs, 1,
            "expected one column-0 diagnostic, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn indented_directive_after_blank_line_still_emits_error() {
        // Same as above but with a blank line between the
        // first directive and the indented one - the blank line
        // shouldn't mask the indentation error.
        let src = "2020-07-28 open Assets:Foo\n\n  2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        let indent_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("column 0"),
                _ => false,
            })
            .count();
        assert_eq!(indent_errs, 1, "errors: {:?}", result.errors);
    }

    #[test]
    fn top_level_directive_at_column_0_no_diagnostic() {
        // Sanity: well-formed top-level directives must NOT
        // trigger the indent diagnostic.
        let src = "2020-07-28 open Assets:Foo\n2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn custom_directive_with_bare_currency_emits_error() {
        // `bean-check` rejects bare currency literals in custom
        // value position; the CST converter mirrors that.
        let src = "2025-01-01 custom \"x\" 10 USD \"y\" NZD\n";
        let result = parse_via_cst(src);
        let bare_curr_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("bare currency"),
                _ => false,
            })
            .count();
        assert_eq!(
            bare_curr_errs, 1,
            "expected one bare-currency diagnostic, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn custom_directive_with_amount_no_error() {
        // Sanity: `10 USD` (NUMBER + CURRENCY paired as Amount)
        // is a valid custom value and must NOT trigger the
        // bare-currency diagnostic.
        let src = "2025-01-01 custom \"x\" 10 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    // ---- round-7 compat regressions (#1282 flip) ---------------

    #[test]
    fn balance_assertion_evaluates_arithmetic_value() {
        // PR #1282 compat regression: rledger emitted a balance
        // failure for `Assets:X  0.25+ 0.75 GBP` because only
        // the first NUMBER (0.25) was used as the assertion
        // target. CST converters for BALANCE/PRICE now evaluate
        // arithmetic the same way posting AMOUNTs do.
        let src = "2024-01-01 open Assets:X GBP\n\
                   2024-01-01 open Equity:Open GBP\n\
                   2024-01-02 * \"deposit\"\n  \
                   Assets:X         1.00 GBP\n  \
                   Equity:Open     -1.00 GBP\n\
                   2024-01-03 balance Assets:X  0.25 + 0.75 GBP\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let bal = result
            .directives
            .iter()
            .find_map(|d| match &d.value {
                Directive::Balance(b) => Some(b),
                _ => None,
            })
            .expect("expected a Balance directive");
        assert_eq!(bal.amount.number, Decimal::from(1));
        assert_eq!(bal.amount.currency.as_str(), "GBP");
    }

    #[test]
    fn price_directive_evaluates_arithmetic_value() {
        let src = "2024-01-01 price USD  1/2 EUR\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Price(p) = &result.directives[0].value else {
            panic!("expected Price");
        };
        assert_eq!(p.amount.number, Decimal::new(5, 1));
        assert_eq!(p.amount.currency.as_str(), "EUR");
    }

    // ---- round-5 architecture review (#1281) -------------------

    #[test]
    fn body_line_tag_does_not_drop_following_postings_comment() {
        // F2-bis: a TAG / LINK line in a transaction body must not
        // make the comment before it vanish. Before the exemption
        // was added, the `pending.clear()` over-fired on the TAG and
        // silently dropped the preceding comment that semantically
        // belonged to the next posting.
        //
        // This test also asserted that the late tag joined the
        // transaction's tag set. Beancount refuses a tag line after
        // the first posting and drops its tags (#2575), so it is now
        // an error and the tag is not kept; the comment still must
        // survive.
        let src = "2024-01-01 * \"x\"\n  \
                   Assets:A   100 USD\n  \
                   ; comment-for-B\n  \
                   #late-tag\n  \
                   Assets:B   -100 USD\n";
        let result = parse_via_cst(src);
        assert_eq!(result.errors.len(), 1, "errors: {:?}", result.errors);
        assert!(
            result.errors[0]
                .message()
                .contains("not allowed after a transaction's first posting"),
            "errors: {:?}",
            result.errors
        );
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert!(
            !t.tags.iter().any(|tag| tag.as_str() == "late-tag"),
            "a tag after the first posting is dropped: {:?}",
            t.tags,
        );
        // And the comment survives - attached to the next posting.
        let b = t.postings.last().expect("at least one posting");
        assert_eq!(b.value.account.as_str(), "Assets:B");
        assert!(
            b.value.comments.iter().any(|c| c.contains("comment-for-B")),
            "expected comment-for-B to survive on Assets:B: {:?}",
            b.value.comments,
        );
    }

    #[test]
    fn oversized_number_in_amount_emits_diagnostic() {
        // F5-bis: the non-arithmetic NUMBER path is now symmetric
        // with the arithmetic-evaluation path. A NUMBER whose
        // text the lexer accepts but `Decimal::from_str` rejects
        // (e.g., 30+ digits, exceeding the 28-digit precision
        // ceiling) used to silently degrade to `CurrencyOnly`.
        let huge = "1".to_string() + &"2345678901234567890".repeat(2); // 39 digits
        let src = format!("2024-01-15 * \"big\"\n  Expenses:X   {huge} USD\n  Assets:Y\n");
        let result = parse_via_cst(&src);
        let invalid_num = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("invalid number"),
                _ => false,
            })
            .count();
        assert_eq!(
            invalid_num, 1,
            "expected one invalid-number diagnostic, got: {:?}",
            result.errors
        );
    }

    // ---- round-4 architecture review (#1281) -------------------

    #[test]
    fn posting_with_two_amount_siblings_emits_error_and_keeps_first() {
        // F1: a posting like `Expenses:Food  5 USD + 3 USD` builds
        // two sibling AMOUNT nodes in the CST. `Posting::amount()`
        // only returns the first. Without an explicit guard the
        // second AMOUNT plus the joining `+` would be silently
        // dropped - the user's transaction would balance against
        // 5 USD instead of the intended 8 USD with no diagnostic.
        let src = "2024-01-15 * \"ambig\"\n  \
                   Expenses:Food   5 USD + 3 USD\n  \
                   Assets:Bank\n";
        let result = parse_via_cst(src);
        let trailing_count = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("trailing tokens"),
                _ => false,
            })
            .count();
        assert_eq!(
            trailing_count, 1,
            "expected one trailing-tokens diagnostic, got: {:?}",
            result.errors
        );
        // The first AMOUNT is still surfaced so partial recovery
        // works for downstream tooling.
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete units from the first AMOUNT");
        };
        assert_eq!(amt.number, Decimal::from(5));
    }

    #[test]
    fn comments_dont_leak_across_failed_posting() {
        // F2: when convert_posting returns None, the queue of
        // pending pre-posting comments must be CLEARED so they
        // don't migrate forward and attach to the next valid
        // posting. Without the clear, comments labelled for the
        // failed posting would silently re-attach to the wrong
        // account, visibly misleading the user.
        let src = "2024-01-15 * \"test\"\n  \
                   Assets:A   100 USD\n  \
                   ; comment-for-bad\n  \
                   ; another-comment\n  \
                   bogus_token_line_no_account\n  \
                   ; comment-for-good\n  \
                   Assets:B   -100 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        // Assets:B is the LAST successful posting; the only
        // comment that should attach to it is the one that
        // immediately precedes it (`; comment-for-good`). The
        // pre-failed-posting comments belong to the failed
        // posting and should be DROPPED with it.
        let b = t.postings.last().expect("at least one posting");
        assert_eq!(b.value.account.as_str(), "Assets:B");
        assert!(
            !b.value
                .comments
                .iter()
                .any(|c| c.contains("comment-for-bad")),
            "comment-for-bad leaked across failed posting onto Assets:B: {:?}",
            b.value.comments
        );
        assert!(
            !b.value
                .comments
                .iter()
                .any(|c| c.contains("another-comment")),
            "another-comment leaked: {:?}",
            b.value.comments
        );
    }

    #[test]
    fn arithmetic_overflow_in_amount_emits_diagnostic() {
        // F5: when `is_arithmetic` is true but the evaluator
        // gives up (overflow, div-by-zero), the converter used
        // to silently produce CurrencyOnly. Now an explicit
        // SyntaxError fires so the user sees the actual root
        // cause instead of just a downstream "doesn't balance".
        // Decimal max is 28 digits - `9999999999999999999999999999 *
        // 9999999999999999999999999999` overflows.
        let huge = "9999999999999999999999999999 * 9999999999999999999999999999";
        let src = format!("2024-01-15 * \"big\"\n  Expenses:X   {huge} USD\n  Assets:Y\n");
        let result = parse_via_cst(&src);
        let arith_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("arithmetic"),
                _ => false,
            })
            .count();
        assert_eq!(
            arith_errs, 1,
            "expected one arithmetic-error diagnostic, got: {:?}",
            result.errors
        );
    }

    // ---- 14 emission-gap regressions (#1281 round-3 review) ----

    #[test]
    fn date_with_single_digit_month_parses() {
        let result = parse_via_cst("2024-1-15 open Assets:Checking\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 15).unwrap());
    }

    #[test]
    fn date_with_single_digit_day_parses() {
        let result = parse_via_cst("2024-01-5 open Assets:Cash USD\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 5).unwrap());
    }

    #[test]
    fn date_with_single_digit_month_and_day_parses() {
        let result = parse_via_cst("2024-1-1 open Assets:Cash USD\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 1).unwrap());
    }

    #[test]
    fn date_with_month_out_of_range_emits_invalid_date_value() {
        let result = parse_via_cst("2024-13-01 open Assets:Cash USD\n");
        let invalid_date: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidDateValue(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(invalid_date.len(), 1, "errors: {:?}", result.errors);
        let msg = &invalid_date[0];
        assert!(
            msg.contains("month") && msg.contains("out of range"),
            "msg: {msg}"
        );
    }

    #[test]
    fn date_with_invalid_leap_year_emits_invalid_date_value() {
        let result = parse_via_cst("2023-02-29 open Assets:Cash USD\n");
        let invalid_date: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidDateValue(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(invalid_date.len(), 1, "errors: {:?}", result.errors);
        let msg = &invalid_date[0];
        assert!(
            msg.contains("day") && msg.contains("out of range") && msg.contains("2023-02"),
            "msg: {msg}"
        );
    }

    #[test]
    fn date_with_completely_invalid_value_still_emits_error() {
        // `2024-13-45` has BOTH month and day out of range; any
        // error variant satisfies the original integration test's
        // `!result.errors.is_empty()` assertion.
        let result = parse_via_cst("2024-13-45 open Assets:Bank\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn open_directive_without_account_emits_error() {
        // `2024-01-01 open` with no account is rejected by legacy
        // via the top-level error-recovery path. CST emits the
        // catch-all `SyntaxError` from `parse_via_cst`'s
        // is_directive_producing/errors_before tracker.
        let result = parse_via_cst("2024-01-01 open\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn open_directive_with_lowercase_account_emits_error() {
        // `lowercase:invalid` doesn't match the ACCOUNT regex
        // (uppercase first letter required), so the open directive
        // has no ACCOUNT child. Same catch-all path as the no-
        // account case.
        let result = parse_via_cst("2024-01-01 open lowercase:invalid\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn incomplete_open_at_eof_emits_error() {
        // Regression for the PR #740 "incomplete-at-EOF" finding:
        // `2024-01-01 open` at EOF with no trailing newline must
        // not be silently dropped.
        let result = parse_via_cst("2024-01-01 open");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn balance_directive_without_amount_emits_error() {
        let result = parse_via_cst("2024-01-15 balance Assets:Checking\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn pad_directive_without_source_account_emits_error() {
        let result = parse_via_cst("2024-01-15 pad Assets:Checking\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn cost_spec_n_hash_t_parses_as_compound() {
        use rust_decimal_macros::dec;
        // This test previously pinned `{N # T}` -> Total{T} — the #1700
        // misparse (beancount's compound_amount weighs N*per + total,
        // so dropping the per-unit silently misweighed every compound
        // spec). It now pins the corrected as-written form.
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock  10 STK {50 # 1500 USD}\n  \
                   Assets:Cash  -1500.00 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[2].value else {
            panic!("expected Transaction at index 2");
        };
        let cost = txn.postings[0]
            .value
            .cost
            .as_ref()
            .expect("cost spec present");
        assert_eq!(
            cost.number,
            Some(CostNumber::Compound {
                per_unit: dec!(50),
                total: dec!(1500)
            }),
            "the `{{N # T CCY}}` form must carry both components as written"
        );
    }

    #[test]
    fn unclosed_cost_brace_emits_error() {
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock 10 AAPL {150 USD\n  \
                   Assets:Cash -1500 USD\n";
        let result = parse_via_cst(src);
        let has_unclosed: bool = result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost"));
        assert!(
            has_unclosed,
            "expected 'unclosed cost' error, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn unclosed_cost_brace_at_eof_emits_error() {
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock 10 AAPL {150 USD";
        let result = parse_via_cst(src);
        let has_unclosed: bool = result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost"));
        assert!(
            has_unclosed,
            "expected 'unclosed cost' error at EOF, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn leading_decimal_in_posting_amount_emits_error() {
        // `.50 USD` (no integer part before the decimal) must be
        // rejected by both parsers; valid `0.50 USD` still works
        // (covered by other tests).
        let src = "2024-01-15 * \"Test\"\n  \
                   Expenses:Food  .50 USD\n  \
                   Assets:Checking\n";
        let result = parse_via_cst(src);
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn transaction_with_metadata_on_directive_and_posting() {
        let src = "2024-01-15 * \"x\"\n  \
                   tag1: \"hello\"\n  \
                   Assets:Cash  -5 USD\n    \
                       receipt: \"abc123\"\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(
            t.meta.get("tag1"),
            Some(&MetaValue::String("hello".to_string()))
        );
        let p_meta = &t.postings[0].value.meta;
        assert_eq!(
            p_meta.get("receipt"),
            Some(&MetaValue::String("abc123".to_string()))
        );
    }

    /// Pins the `ERROR_NODE` exclusion contract on
    /// `account_occurrences`. The rustdoc on `ParseResult::
    /// account_occurrences` distinguishes two failure modes:
    ///
    /// - **Typed-conversion failure** (e.g. `InvalidBookingMethod`
    ///   on an `open` whose booking string is garbage): the CST is
    ///   intact, the `ACCOUNT` node is NOT inside `ERROR_NODE`, so
    ///   the token IS tracked. The LSP rename can still hit it
    ///   during mid-edit.
    /// - **CST-recovery wrap**: a directive so garbled that the
    ///   CST wraps the region in `ERROR_NODE`. The `ACCOUNT` token
    ///   is inside `ERROR_NODE`, NOT tracked.
    ///
    /// The two policies are deliberate. This test pins both.
    #[test]
    fn account_occurrences_policy_for_failing_directives() {
        // Case A: typed-conversion failure. `open Assets:Bank
        // "GARBAGE"` parses syntactically but fails the booking-
        // method whitelist. The ACCOUNT token IS tracked.
        let src = "2024-01-01 open Assets:Bank \"GARBAGE\"\n";
        let r = parse_via_cst(src);
        assert!(
            r.account_occurrences
                .iter()
                .any(|o| o.value == "Assets:Bank"),
            "typed-conversion failure should keep the ACCOUNT token in \
             account_occurrences (got {:?}); rename mid-edit relies on this",
            r.account_occurrences,
        );

        // Case B: CST-recovery wrap. `opn Assets:Bank USD` (typo
        // `opn`) is unrecognized at the directive position and the
        // recovery walker wraps it in ERROR_NODE. The ACCOUNT
        // token is excluded.
        let src = "2024-01-01 opn Assets:Bank USD\n";
        let r = parse_via_cst(src);
        assert!(
            !r.account_occurrences
                .iter()
                .any(|o| o.value == "Assets:Bank"),
            "ERROR_NODE-wrapped ACCOUNT should be EXCLUDED from \
             account_occurrences (got {:?}); rename should not hit garbled \
             mid-edit syntax",
            r.account_occurrences,
        );
    }

    // ---- cost-spec token latches and the `{*}` merge machine ----
    //
    // Added after the 2026-08-01 mutation run: every mutant in these two
    // machines survived. The merge rule was tested only through the `ast.rs`
    // copy (now deleted, it delegates here), and nothing at all exercised the
    // first-token latches, so a cost spec carrying a duplicate date, label or
    // currency was untested in either tree walker.

    /// Parse one posting's cost spec, or panic with the source for context.
    fn cost_of(src: &str) -> CostSpec {
        let result = parse_via_cst(src);
        let Some(Directive::Transaction(txn)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected a transaction from {src:?}");
        };
        txn.postings
            .first()
            .and_then(|p| p.cost.as_deref().cloned())
            .unwrap_or_else(|| panic!("expected a cost spec from {src:?}"))
    }

    fn posting_with_cost(spec: &str) -> String {
        format!("2020-01-01 * \"t\"\n  Assets:A 1 HOOL {spec}\n  Assets:B\n")
    }

    /// A repeated DATE, STRING or CURRENCY keeps the FIRST occurrence. Malformed
    /// input is the only way to get here, and "first wins" is what keeps the
    /// green and red walkers agreeing on it.
    #[test]
    fn cost_spec_latches_the_first_date_label_and_currency() {
        let cost = cost_of(&posting_with_cost(
            "{2 USD, 2020-06-01, 2021-02-02, \"first\", \"second\"}",
        ));
        assert_eq!(cost.date, naive_date(2020, 6, 1), "the FIRST date wins");
        assert_eq!(cost.label.as_deref(), Some("first"), "the FIRST label wins");
        assert_eq!(
            cost.currency
                .as_ref()
                .map(rustledger_core::Currency::as_str),
            Some("USD"),
            "the FIRST currency wins"
        );

        // Currency specifically, with nothing else competing.
        let cost = cost_of(&posting_with_cost("{2 USD, EUR}"));
        assert_eq!(
            cost.currency
                .as_ref()
                .map(rustledger_core::Currency::as_str),
            Some("USD")
        );
    }

    /// The latch is on the first token of a KIND, not the first that parses.
    ///
    /// `9999-99-99` lexes as a DATE and fails to parse. The latch must still
    /// close, leaving the date empty — falling through to a later, valid DATE
    /// would make the two walkers disagree on malformed input, which is the
    /// divergence class this design exists to prevent.
    #[test]
    fn cost_spec_latch_closes_on_an_unparsable_first_token() {
        let cost = cost_of(&posting_with_cost("{2 USD, 9999-99-99, 2021-02-02}"));
        assert_eq!(
            cost.date, None,
            "an unparsable first DATE must not let a later one through"
        );
    }

    /// A `*` is the merge marker when it begins a component: the previous
    /// non-whitespace token is the opener or a comma. Each row pins one arm of
    /// that machine.
    #[test]
    fn cost_spec_merge_flag_is_set_by_a_star_that_begins_a_component() {
        for (spec, expected, why) in [
            ("{*}", true, "bare star directly after the opener"),
            (
                "{ * }",
                true,
                "whitespace never decides, so the star still does",
            ),
            ("{{*}}", true, "`{{` is an opener too"),
            (
                "{2 USD, *}",
                true,
                "a star after a comma begins a component: a merge, as in beancount (#2329)",
            ),
            ("{2020-01-01, *}", true, "after a date component"),
            ("{*, 2 USD}", true, "leading, before other components"),
            ("{{2 USD, *}}", true, "inside `{{`"),
            (
                "{500 * 2 USD, *}",
                true,
                "multiplication, then a merge component",
            ),
            (
                "{2 USD * 3, 4}",
                false,
                "a star after a number is multiplication",
            ),
            (
                "{500 * 2 USD}",
                false,
                "a star past the first token is multiplication",
            ),
        ] {
            assert_eq!(
                cost_of(&posting_with_cost(spec)).merge,
                expected,
                "{spec}: {why}"
            );
        }
    }

    /// The red-tree accessor and the token-level canonical must agree, since
    /// they are now one machine fed by two walkers. Asserts on the exact pair
    /// rather than on either alone, so deleting the delegation is caught.
    #[test]
    fn ast_is_merge_agrees_with_the_converted_cost_spec() {
        for spec in [
            "{*}",
            "{ * }",
            "{{*}}",
            "{2 USD, *}",
            "{500 * 2 USD}",
            "{2 USD}",
        ] {
            let src = posting_with_cost(spec);
            let converted = cost_of(&src).merge;

            let parsed = crate::parse(&src);
            let root = ast::SourceFile::cast(parsed.syntax_node()).expect("source file");
            let from_ast = root
                .syntax()
                .descendants()
                .find_map(ast::CostSpec::cast)
                .map_or_else(|| panic!("no CostSpec node in {src:?}"), |cs| cs.is_merge());

            assert_eq!(
                from_ast, converted,
                "{spec}: ast::CostSpec::is_merge disagrees with the converted CostSpec"
            );
        }
    }

    /// `MergeFlag` guards `past_opener` because a token stream may begin before
    /// the opener. Both tree walkers happen to start AT the opener, so this is
    /// unreachable through them and only a direct feed can pin it -- but the
    /// guard is what stops a leading `*` (or any leading token) from deciding
    /// the flag, and it costs nothing to keep it honest.
    #[test]
    fn merge_flag_ignores_tokens_before_the_opener() {
        use crate::SyntaxKind as K;

        // A star BEFORE any opener is not a merge marker: nothing has opened
        // yet, so it cannot be the first token after an opener.
        let mut flag = MergeFlag::default();
        for kind in [K::STAR, K::L_BRACE, K::R_BRACE] {
            flag.feed(kind);
        }
        assert!(
            !flag.is_merge(),
            "a star before the opener must not decide the flag"
        );

        // And a non-star before the opener must not close the machine early,
        // or the real `{*}` that follows would be missed.
        let mut flag = MergeFlag::default();
        for kind in [K::NUMBER, K::L_BRACE, K::STAR, K::R_BRACE] {
            flag.feed(kind);
        }
        assert!(
            flag.is_merge(),
            "a token before the opener must not consume the decision"
        );

        // A comma before the opener must not arm a component start either, or
        // the star that follows it would read as a merge component.
        let mut flag = MergeFlag::default();
        for kind in [K::COMMA, K::STAR, K::L_BRACE, K::NUMBER, K::R_BRACE] {
            flag.feed(kind);
        }
        assert!(
            !flag.is_merge(),
            "a comma before the opener must not make the next star a merge"
        );
    }

    /// Only the FIRST opener starts the component list. A later brace on
    /// malformed input is not an opener, so a star after it is not a merge
    /// component (#2329 moved the rule from "first token" to "starts a
    /// component", and this keeps it from re-arming mid-spec).
    #[test]
    fn merge_flag_ignores_a_later_opener() {
        use crate::SyntaxKind as K;
        let mut flag = MergeFlag::default();
        for kind in [
            K::L_BRACE,
            K::NUMBER,
            K::WHITESPACE,
            K::CURRENCY,
            K::L_BRACE,
            K::STAR,
        ] {
            flag.feed(kind);
        }
        assert!(!flag.is_merge(), "`{{2 USD {{*` is not a merge");
    }

    /// Every diagnostic span in this module is built as `offset + bom_offset`,
    /// and a wrong offset puts the editor's squiggle on the wrong text.
    ///
    /// The error paths were already exercised, but only for the PRESENCE of an
    /// error, so the 2026-08-01 mutation run could flip `+` to `-` or `*` in
    /// five different span computations without a single failure. Each row
    /// below drives one of them and asserts the exact range, once with no BOM
    /// and once with one, so the addition itself is pinned rather than merely
    /// the arithmetic happening to agree at zero.
    #[test]
    fn diagnostic_spans_point_at_the_offending_text_with_and_without_a_bom() {
        // (label, source, the substring the span must cover)
        let cases = [
            (
                "price with two numbers",
                "2024-01-15 price HOOL 1 2 USD\n",
                "1 2",
            ),
            (
                "balance with two numbers",
                "2024-01-15 balance Assets:Cash 1 2 USD\n",
                "1 2",
            ),
            (
                "posting with a second amount",
                "2024-01-15 *\n  Assets:A 5 USD + 3 USD\n  Assets:B\n",
                // Underlined from the END of the first amount on purpose, so
                // the reader sees `5 USD + 3 USD` and not just the tail.
                " + 3 USD",
            ),
            (
                // A `+`/`-` binds to the amount as its sign, so the orphan that
                // actually reaches this path is a stray comma - someone writing
                // `1,234` with the separator outside the number.
                "orphaned comma before a posting amount",
                "2024-01-15 *\n  Assets:A , 1,234.00 USD\n  Assets:B\n",
                ",",
            ),
        ];

        for (label, src, needle) in cases {
            for bom in [false, true] {
                let full = if bom {
                    format!("\u{FEFF}{src}")
                } else {
                    src.to_string()
                };
                let result = parse_via_cst(&full);
                let bom_len = if bom { "\u{FEFF}".len() } else { 0 };

                let expected_start = src
                    .find(needle)
                    .unwrap_or_else(|| panic!("{label}: {needle:?} not in the fixture"))
                    + bom_len;
                let expected_end = expected_start + needle.len();

                let hit = result
                    .errors
                    .iter()
                    .find(|e| e.span.start == expected_start && e.span.end == expected_end);
                assert!(
                    hit.is_some(),
                    "{label} (bom={bom}): expected an error spanning {expected_start}..{expected_end} \
                     (the {needle:?}), got {:?}",
                    result
                        .errors
                        .iter()
                        .map(|e| (e.span.start, e.span.end))
                        .collect::<Vec<_>>()
                );
            }
        }
    }

    /// A leading `-` on a `price`/`balance` number is a separate MINUS token,
    /// so the converter has to re-apply the sign the AST accessor drops. Both
    /// the negation and the scanner that finds it were untested.
    #[test]
    fn negative_numbers_in_price_and_balance_keep_their_sign() {
        // SPACED, so the sign is its own MINUS token and the AST accessor
        // hands back an unsigned number. `-1.50` written closed up lexes as a
        // single signed NUMBER and never reaches the scanner at all.
        let result = parse_via_cst("2024-01-15 price HOOL - 1.50 USD\n");
        let Some(Directive::Price(p)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected a Price, got {:?}", result.directives);
        };
        assert_eq!(p.amount.number, rust_decimal_macros::dec!(-1.50));

        let result = parse_via_cst("2024-01-15 balance Assets:Cash - 1.50 USD\n");
        let Some(Directive::Balance(b)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected a Balance, got {:?}", result.directives);
        };
        assert_eq!(b.amount.number, rust_decimal_macros::dec!(-1.50));

        // And the positive case must stay positive: a scanner that reports
        // "minus" for everything would pass the assertions above alone.
        let result = parse_via_cst("2024-01-15 price HOOL 1.50 USD\n");
        let Some(Directive::Price(p)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected a Price");
        };
        assert_eq!(p.amount.number, rust_decimal_macros::dec!(1.50));
    }

    /// `price` puts the BASE currency BEFORE the number, so the scan that
    /// rejects a two-number value may only stop at a currency once a number has
    /// been seen. Getting that guard wrong makes every `price` directive look
    /// malformed, or stops rejecting the thing it exists to reject.
    #[test]
    fn price_base_currency_before_the_number_is_not_a_malformed_value() {
        let result = parse_via_cst("2024-01-15 price HOOL 1.50 USD\n");
        assert!(
            result.errors.is_empty(),
            "a well-formed price must not be reported as malformed: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);

        // Two numbers still must be rejected.
        let result = parse_via_cst("2024-01-15 price HOOL 1 2 USD\n");
        assert!(
            has_syntax_error(&result, "malformed amount"),
            "two numbers must still be refused: {:?}",
            result.errors
        );
    }

    /// Only `+`, `-` and `,` are orphanable. A posting FLAG sits between the
    /// account and the amount too, and treating it as an orphan would reject
    /// perfectly ordinary input.
    #[test]
    fn a_posting_flag_is_not_an_orphaned_amount_prefix() {
        let result = parse_via_cst("2024-01-15 *\n  ! Assets:A 5 USD\n  Assets:B\n");
        assert!(
            !has_syntax_error(&result, "unexpected token before posting amount"),
            "a posting flag is not an orphan: {:?}",
            result.errors
        );
    }

    /// Both diagnostics inside posting-amount conversion carry spans built with
    /// the BOM offset, and neither was pinned. An arithmetic expression that
    /// cannot be evaluated and a number past the Decimal ceiling are the two
    /// ways in.
    #[test]
    fn posting_amount_diagnostics_point_at_the_offending_amount() {
        // 30 digits: past `rust_decimal`'s ~28-digit ceiling.
        let huge = "1".repeat(30);
        let cases = [
            (
                // The span covers the whole AMOUNT node, currency included:
                // the expression is what is wrong, but the amount is what the
                // reader has to replace.
                "unevaluatable arithmetic",
                "2024-01-15 *\n  Assets:A (1/0) USD\n  Assets:B\n".to_string(),
                "(1/0) USD".to_string(),
            ),
            (
                "number past the Decimal ceiling",
                format!("2024-01-15 *\n  Assets:A {huge} USD\n  Assets:B\n"),
                huge,
            ),
        ];

        for (label, src, needle) in cases {
            for bom in [false, true] {
                let full = if bom {
                    format!("\u{FEFF}{src}")
                } else {
                    src.clone()
                };
                let bom_len = if bom { "\u{FEFF}".len() } else { 0 };
                let result = parse_via_cst(&full);

                let start = src.find(&needle).expect("needle present") + bom_len;
                let end = start + needle.len();
                assert!(
                    result
                        .errors
                        .iter()
                        .any(|e| e.span.start == start && e.span.end == end),
                    "{label} (bom={bom}): expected a span {start}..{end}, got {:?}",
                    result
                        .errors
                        .iter()
                        .map(|e| (e.span.start, e.span.end))
                        .collect::<Vec<_>>()
                );
            }
        }
    }

    /// The trailing currency closes a directive value, and it must only do so
    /// once a number has been seen (a `price` names its base currency first).
    /// Without the break, a stray number after the currency would be counted
    /// and a well-formed directive rejected.
    #[test]
    fn a_trailing_currency_closes_the_value_scan() {
        let result = parse_via_cst("2024-01-15 price HOOL 1.50 USD 2\n");
        assert!(
            !has_syntax_error(&result, "malformed amount"),
            "the scan must stop at the closing currency, so the stray `2` is not \
             a second number of the VALUE: {:?}",
            result.errors
        );
    }

    /// Only tokens AFTER the account can be orphans, and only `+`, `-` and `,`
    /// qualify. Both halves of that were untested, so each row here would be
    /// reported as an orphan by a slightly wrong predicate.
    #[test]
    fn orphan_detection_ignores_pre_account_and_non_sign_tokens() {
        let orphan_reported = |src: &str| {
            has_syntax_error(
                &parse_via_cst(src),
                "unexpected token before posting amount",
            )
        };

        assert!(
            !orphan_reported("2024-01-15 *\n  , Assets:A 1 USD\n  Assets:B\n"),
            "a comma BEFORE the account is not an orphaned amount prefix"
        );
        assert!(
            !orphan_reported("2024-01-15 *\n  Assets:A \"note\" 1 USD\n  Assets:B\n"),
            "a non-sign token between account and amount is not an orphan"
        );
        // The genuine orphan still is one, so the assertions above cannot pass
        // by the detector simply never firing.
        assert!(
            orphan_reported("2024-01-15 *\n  Assets:A , 1 USD\n  Assets:B\n"),
            "a comma after the account IS an orphan"
        );
    }

    /// A posting's trailing comment is collected up to the newline. Stopping on
    /// the wrong condition silently drops every one of them.
    #[test]
    fn posting_trailing_comment_is_captured() {
        let result = parse_via_cst("2024-01-15 *\n  Assets:A 1 USD ; why\n  Assets:B\n");
        let Some(Directive::Transaction(txn)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected a transaction");
        };
        let first = &txn.postings[0];
        assert!(
            first.trailing_comments.iter().any(|c| c.contains("why")),
            "expected the trailing comment on the posting, got {:?}",
            first.trailing_comments
        );
    }

    /// The sign scanner behind `price`/`balance` fallback conversion.
    ///
    /// Reaching it takes work: `directive_arithmetic_value` runs first and
    /// handles ordinary unary minus, so `- 1.50` never gets here. The fallback
    /// only runs when the arithmetic parse declines, and `- 1.50 - USD` is one
    /// such shape -- error recovery tolerates the trailing operator, the
    /// arithmetic parse gives up, and the AST accessor then hands back an
    /// UNSIGNED number that this scanner has to re-sign.
    ///
    /// Probed for rather than assumed: the whole test suite and all 995 corpus
    /// files leave this branch cold, so it looked like dead code until an
    /// adversarial sweep found the inputs. Worth stating, because deleting it
    /// on that first impression would have been wrong.
    #[test]
    fn price_and_balance_fallback_re_signs_a_leading_minus() {
        let number_of = |src: &str| -> Decimal {
            let r = parse_via_cst(src);
            match r.directives.first().map(|d| &d.value) {
                Some(Directive::Price(p)) => p.amount.number,
                Some(Directive::Balance(b)) => b.amount.number,
                other => panic!("expected price/balance from {src:?}, got {other:?}"),
            }
        };

        // MINUS before the number: re-signed.
        assert_eq!(
            number_of("2024-01-15 price HOOL - 1.50 - USD\n"),
            rust_decimal_macros::dec!(-1.50)
        );
        assert_eq!(
            number_of("2024-01-15 balance Assets:C - 1.50 - USD\n"),
            rust_decimal_macros::dec!(-1.50)
        );

        // NUMBER first: the scan stops there, so a LATER minus must not flip
        // the sign. Without this the "stop at the number" arm is free to vanish.
        assert_eq!(
            number_of("2024-01-15 price HOOL 1.50 - USD\n"),
            rust_decimal_macros::dec!(1.50)
        );
        assert_eq!(
            number_of("2024-01-15 balance Assets:C 1.50 - USD\n"),
            rust_decimal_macros::dec!(1.50)
        );
    }

    /// The red conversion path is a mirror of the green one, kept for the
    /// `green_eq_red` differential fuzz target. Production parses via green, so
    /// a test written against `parse_via_cst` exercises the mirror only where
    /// the two SHARE a helper -- which is why the 2026-08-01 mutation run
    /// showed red-only code uncovered even though its green twin was tested.
    ///
    /// These drive `parse_red_only` directly, and assert the two paths agree,
    /// so the mirror cannot rot silently.
    #[test]
    fn red_path_matches_green_on_posting_comments_and_orphan_detection() {
        let orphan_msg = "unexpected token before posting amount";

        // Trailing comment on a posting line, collected by the red converter's
        // own scan up to the terminating NEWLINE.
        let src = "2024-01-15 *\n  Assets:A 1 USD ; why\n  Assets:B\n";
        for (label, result) in [("green", parse_via_cst(src)), ("red", parse_red_only(src))] {
            let Some(Directive::Transaction(txn)) = result.directives.first().map(|d| &d.value)
            else {
                panic!("{label}: expected a transaction");
            };
            assert!(
                txn.postings[0]
                    .trailing_comments
                    .iter()
                    .any(|c| c.contains("why")),
                "{label}: trailing comment lost, got {:?}",
                txn.postings[0].trailing_comments
            );
        }

        // Orphan detection, through the red converter: a comma after the
        // account is one, a comma before it and a non-sign token are not.
        let orphan_reported = |src: &str| has_syntax_error(&parse_red_only(src), orphan_msg);
        assert!(
            orphan_reported("2024-01-15 *\n  Assets:A , 1 USD\n  Assets:B\n"),
            "red: a comma after the account IS an orphan"
        );
        assert!(
            !orphan_reported("2024-01-15 *\n  , Assets:A 1 USD\n  Assets:B\n"),
            "red: a comma BEFORE the account is not"
        );
        assert!(
            !orphan_reported("2024-01-15 *\n  Assets:A \"note\" 1 USD\n  Assets:B\n"),
            "red: a non-sign token between account and amount is not"
        );
    }

    // ---- metadata and custom values: the other token-level canonical ----
    //
    // `meta_value_from_tokens` is the twin of `cost_spec_from_tokens` and had
    // the same shape of gap: first-of-kind latches and a sign machine that no
    // test touched. `value_tokens_to_meta` is the sibling used by custom
    // directives and the red path.

    fn meta_of(entries: &str) -> rustledger_core::Metadata {
        let src = format!("2024-01-15 open Assets:A\n{entries}");
        let result = parse_via_cst(&src);
        let Some(Directive::Open(open)) = result.directives.first().map(|d| &d.value) else {
            panic!("expected an Open from {src:?}, errors {:?}", result.errors);
        };
        open.meta.clone().into_inner()
    }

    fn custom_values(line: &str) -> Vec<MetaValue> {
        let result = parse_via_cst(line);
        let Some(Directive::Custom(c)) = result.directives.first().map(|d| &d.value) else {
            panic!(
                "expected a Custom from {line:?}, errors {:?}",
                result.errors
            );
        };
        c.values.clone()
    }

    /// Every value kind a metadata entry can carry. Deleting any one arm made
    /// that kind silently fall through to the next candidate in the priority
    /// order, which is invisible unless the kind is asserted directly.
    #[test]
    fn metadata_values_cover_every_kind() {
        let meta = meta_of(
            "  str: \"hello\"\n  num: 42\n  amt: 42 USD\n  dt: 2024-06-01\n  \
             acct: Assets:B\n  cur: USD\n  yes: TRUE\n  no: FALSE\n  \
             tg: #mytag\n  lk: ^mylink\n",
        );
        let got = |k: &str| meta.get(k).cloned().unwrap_or(MetaValue::None);

        assert_eq!(got("str"), MetaValue::String("hello".into()));
        assert_eq!(got("num"), MetaValue::Int(42));
        assert_eq!(
            got("amt"),
            MetaValue::Amount(Amount::new(rust_decimal_macros::dec!(42), "USD"))
        );
        assert_eq!(got("dt"), MetaValue::Date(naive_date(2024, 6, 1).unwrap()));
        assert_eq!(got("acct"), MetaValue::Account(Account::new("Assets:B")));
        assert_eq!(got("cur"), MetaValue::Currency(Currency::new("USD")));
        assert_eq!(got("yes"), MetaValue::Bool(true));
        assert_eq!(got("no"), MetaValue::Bool(false));
        assert_eq!(got("tg"), MetaValue::Tag(Tag::new("mytag")));
        assert_eq!(got("lk"), MetaValue::Link(Link::new("mylink")));
    }

    /// First-of-kind latching, the same rule `cost_spec_from_tokens` uses. A
    /// repeated token of any kind keeps the FIRST, and nothing exercised that
    /// for metadata, so every latch guard could be flipped freely.
    #[test]
    fn metadata_latches_the_first_token_of_each_kind() {
        // Two-character keys because beancount requires them, and so do we
        // since #1955. These are fixture names only; the test is about
        // first-of-kind LATCHING and nothing here depends on key length.
        let meta = meta_of(
            "  ss: \"one\" \"two\"\n  nn: 1 2\n  cc: USD EUR\n  dd: 2024-06-01 2025-07-02\n  \
             aa: Assets:First Assets:Second\n  bb: TRUE FALSE\n  tt: #first #second\n",
        );
        let got = |k: &str| meta.get(k).cloned().unwrap_or(MetaValue::None);

        assert_eq!(got("ss"), MetaValue::String("one".into()));
        assert_eq!(got("nn"), MetaValue::Int(1));
        assert_eq!(got("dd"), MetaValue::Date(naive_date(2024, 6, 1).unwrap()));
        assert_eq!(got("aa"), MetaValue::Account(Account::new("Assets:First")));
        assert_eq!(got("bb"), MetaValue::Bool(true), "TRUE came first");
        assert_eq!(got("tt"), MetaValue::Tag(Tag::new("first")));
        // `c` pairs a number-less currency run: the FIRST currency wins.
        assert_eq!(got("cc"), MetaValue::Currency(Currency::new("USD")));
    }

    /// The sign machine: a MINUS after the key negates the number.
    ///
    /// The third case CHANGED with #1944. It used to assert that `42 - 1` is
    /// `Int(42)` — "a minus past the number is not a sign; the first NUMBER
    /// closes it". That described the truncation faithfully but was never the
    /// right answer: beancount evaluates it and reports **41**, verified
    /// directly against the oracle before this expectation was touched. The
    /// old assertion was pinning a bug as intended behavior, which is why it
    /// took a differential comparison rather than a reading to notice.
    ///
    /// The sign machine itself is unchanged and still pinned by the first two
    /// cases: a leading MINUS is now consumed by the expression evaluator
    /// instead of a separate flag, and reaches the same values.
    #[test]
    fn metadata_minus_applies_only_before_the_number() {
        let meta = meta_of("  neg: -42\n  negamt: -42 USD\n  after: 42 - 1\n");
        let got = |k: &str| meta.get(k).cloned().unwrap_or(MetaValue::None);

        assert_eq!(got("neg"), MetaValue::Int(-42));
        assert_eq!(
            got("negamt"),
            MetaValue::Amount(Amount::new(rust_decimal_macros::dec!(-42), "USD")),
            "the sign applies to the amount too"
        );
        assert_eq!(
            got("after"),
            MetaValue::Int(41),
            "an expression in a metadata value is evaluated, matching beancount"
        );
    }

    /// `value_tokens_to_meta` walks a token run and returns the NEXT index, so
    /// a wrong advance either drops values or repeats them. Custom directives
    /// are the surface that reads several values in a row, which makes the
    /// advance observable.
    #[test]
    fn custom_directive_values_advance_one_value_at_a_time() {
        assert_eq!(
            custom_values("2024-01-15 custom \"b\" FALSE TRUE FALSE\n"),
            vec![
                MetaValue::Bool(false),
                MetaValue::Bool(true),
                MetaValue::Bool(false)
            ],
            "each bool consumes exactly one token"
        );

        assert_eq!(
            custom_values("2024-01-15 custom \"b\" 42 USD TRUE\n"),
            vec![
                MetaValue::Amount(Amount::new(rust_decimal_macros::dec!(42), "USD")),
                MetaValue::Bool(true)
            ],
            "NUMBER + CURRENCY consumes TWO tokens and the next value still lands"
        );

        // A lone CURRENCY is its own token, not an amount fragment -- it
        // consumes exactly one, so `TRUE` still lands. It is no longer
        // EMITTED, because a bare currency is rejected as a custom value by
        // both tools and a rejected value must not reach `values` (#2190).
        // The advance is what this test is about, and the surviving `TRUE`
        // is what proves it.
        assert_eq!(
            custom_values("2024-01-15 custom \"b\" USD TRUE\n"),
            vec![MetaValue::Bool(true)],
            "a lone CURRENCY consumes one token, so the next value still lands"
        );

        // The tag and link are rejected here and so are not emitted, but they
        // still consume one token each -- which is exactly what the date and
        // account landing afterwards proves.
        assert_eq!(
            custom_values("2024-01-15 custom \"b\" -42 #tag ^link 2024-06-01 Assets:B\n"),
            vec![
                MetaValue::Int(-42),
                MetaValue::Date(naive_date(2024, 6, 1).unwrap()),
                MetaValue::Account(Account::new("Assets:B")),
            ],
            "MINUS + NUMBER consumes two tokens; the rest follow in order"
        );
    }

    /// The bool and tag/link latches, in the order that actually exercises the
    /// SECOND arm of each pair. `TRUE FALSE` only proves the first arm latches;
    /// reversing it is what pins the guard on the other one.
    #[test]
    fn metadata_latches_bool_and_taglink_in_either_order() {
        // Two-character keys, per #1955; `tl` / `lt` already were.
        let meta = meta_of("  bb: FALSE TRUE\n  tl: #tag ^link\n  lt: ^link #tag\n");
        let got = |k: &str| meta.get(k).cloned().unwrap_or(MetaValue::None);

        assert_eq!(
            got("bb"),
            MetaValue::Bool(false),
            "FALSE came first, so the later TRUE must not overwrite it"
        );
        assert_eq!(
            got("tl"),
            MetaValue::Tag(Tag::new("tag")),
            "tag and link share one slot; the tag came first"
        );
        assert_eq!(
            got("lt"),
            MetaValue::Link(Link::new("link")),
            "and the link wins when it comes first"
        );
    }

    /// `extract_custom_values` advances by the index the discriminator returns.
    /// A helper that failed to advance would spin the loop forever, so the
    /// caller clamps. This pins that a long run of values terminates and is
    /// read in order -- a hang here would let malformed input stall the parser.
    #[test]
    fn custom_values_terminate_on_a_long_run() {
        let values = custom_values(
            "2024-01-15 custom \"b\" 1 USD 2 EUR TRUE FALSE #a ^b 2024-06-01 Assets:X \"s\"\n",
        );
        // Nine values are READ; the tag and the link are rejected and dropped,
        // leaving seven. `1 USD` and `2 EUR` each PAIR into an Amount, so
        // neither currency is bare and neither is dropped. The point of the
        // test is that the run terminates and stays in order, which the
        // surviving sequence still shows.
        assert_eq!(
            values.len(),
            7,
            "every value consumed exactly once, got {values:?}"
        );
        assert_eq!(
            values.first(),
            Some(&MetaValue::Amount(Amount::new(
                rust_decimal_macros::dec!(1),
                "USD"
            )))
        );
        assert_eq!(values.last(), Some(&MetaValue::String("s".into())));
    }

    /// The scan skips the directive header (date, keyword, and the type-name
    /// string) before reading values, steps past tokens that are not values,
    /// and terminates when there are none. Each of those is a separate step in
    /// the loop and none had a test.
    #[test]
    fn custom_directive_scan_skips_the_header_and_non_values() {
        assert_eq!(
            custom_values("2024-01-15 custom \"b\"\n"),
            vec![],
            "the type name is the header, not a value, and no values is valid"
        );

        assert_eq!(
            custom_values("2024-01-15 custom \"b\" \"x\" 42\n"),
            vec![MetaValue::String("x".into()), MetaValue::Int(42)],
            "the FIRST string is the type name; a later one IS a value"
        );

        // A `*` is not a value, so the scan must step over it rather than
        // stall. Both positions matter: before any value, and between two.
        assert_eq!(
            custom_values("2024-01-15 custom \"b\" * 42\n"),
            vec![MetaValue::Int(42)],
            "a non-value token before the first value is stepped over"
        );
        // Not `42 * 7`: that is one expression, evaluated to 294 (#2806).
        assert_eq!(
            custom_values("2024-01-15 custom \"b\" 42 ~ 7\n"),
            vec![MetaValue::Int(42), MetaValue::Int(7)],
            "and between two values"
        );
    }

    /// An arithmetic expression in a custom value is evaluated whole, as in
    /// beancount, instead of being split into separate values (#2806). The
    /// expected values are beancount 3.2.3's for the same lines.
    #[test]
    fn test_custom_values_evaluate_arithmetic() {
        use rust_decimal_macros::dec;
        let amount = |n: Decimal, c: &str| MetaValue::Amount(Amount::new(n, c));
        for (src, want) in [
            (
                "2024-01-01 custom \"c\" 10/4 USD\n",
                vec![amount(dec!(2.5), "USD")],
            ),
            (
                "2024-01-01 custom \"b\" 10/4\n",
                vec![MetaValue::Number(dec!(2.5))],
            ),
            (
                "2024-01-01 custom \"e\" 1+2 USD\n",
                vec![amount(dec!(3), "USD")],
            ),
            (
                "2024-01-01 custom \"m\" 10 - 5 USD\n",
                vec![amount(dec!(5), "USD")],
            ),
            ("2024-01-01 custom \"f\" 10 -5\n", vec![MetaValue::Int(5)]),
            ("2024-01-01 custom \"j\" 2 * 3\n", vec![MetaValue::Int(6)]),
            ("2024-01-01 custom \"n\" 3 * -2\n", vec![MetaValue::Int(-6)]),
            ("2024-01-01 custom \"p\" -(2+3)\n", vec![MetaValue::Int(-5)]),
            (
                "2024-01-01 custom \"h\" (1+2) USD\n",
                vec![amount(dec!(3), "USD")],
            ),
            (
                "2024-01-01 custom \"g\" -10/4 USD \"x\" 2*3\n",
                vec![
                    amount(dec!(-2.5), "USD"),
                    MetaValue::String("x".into()),
                    MetaValue::Int(6),
                ],
            ),
            (
                "2024-01-01 custom \"k\" \"s\" 1.50 + 1 USD TRUE\n",
                vec![
                    MetaValue::String("s".into()),
                    amount(dec!(2.50), "USD"),
                    MetaValue::Bool(true),
                ],
            ),
            (
                "2024-01-01 custom \"s\" 1 + 2 + 3 EUR 4\n",
                vec![amount(dec!(6), "EUR"), MetaValue::Int(4)],
            ),
            // Unchanged: separate numbers stay separate values.
            (
                "2024-01-01 custom \"i\" 10 5\n",
                vec![MetaValue::Int(10), MetaValue::Int(5)],
            ),
        ] {
            // Both trees, which must agree (asserted by the helper).
            let (errors, values) = custom_errors_and_values(src);
            assert!(errors.is_empty(), "{src:?}: {errors:?}");
            // Equal as numbers; the scale of a quotient is pinned by
            // `test_arithmetic_division_has_pythons_scale`.
            assert_eq!(values, want, "{src:?}");
        }
    }

    /// The value `pushmeta key: <value>` pushes onto the transaction after
    /// it (pushed metadata reaches transactions only, #2812), from the
    /// green-wired parse, after checking both trees agree.
    fn pushed_value(value: &str) -> (Vec<String>, Option<MetaValue>) {
        let src = format!(
            "pushmeta kk: {value}\n2024-01-01 * \"t\"\n  Assets:A  1 USD\n  Assets:B\npopmeta kk:\n"
        );
        let green = parse_via_cst(&src);
        let red = parse_red_only(&src);
        assert_eq!(
            format!("{:?}", green.errors),
            format!("{:?}", red.errors),
            "trees disagree on errors for {src:?}"
        );
        assert_eq!(
            format!("{:?}", green.directives),
            format!("{:?}", red.directives),
            "trees disagree on directives for {src:?}"
        );
        let Directive::Transaction(txn) = &green.directives[0].value else {
            panic!("expected Transaction from {src:?}");
        };
        let errors = green
            .errors
            .iter()
            .map(crate::ParseError::message)
            .collect();
        (errors, txn.meta.get("kk").cloned())
    }

    /// The value a metadata line `kk: <value>` gives, from the green-wired
    /// parse, after checking both trees agree.
    fn metadata_value(value: &str) -> (Vec<String>, Option<MetaValue>) {
        let src = format!("2024-01-01 open Assets:Bank USD\n  kk: {value}\n");
        let green = parse_via_cst(&src);
        let red = parse_red_only(&src);
        assert_eq!(
            format!("{:?}", green.errors),
            format!("{:?}", red.errors),
            "trees disagree on errors for {src:?}"
        );
        assert_eq!(
            format!("{:?}", green.directives),
            format!("{:?}", red.directives),
            "trees disagree on directives for {src:?}"
        );
        let Directive::Open(open) = &green.directives[0].value else {
            panic!("expected Open from {src:?}");
        };
        let errors = green
            .errors
            .iter()
            .map(crate::ParseError::message)
            .collect();
        (errors, open.meta.get("kk").cloned())
    }

    /// `pushmeta` values are metadata values, read by the metadata converter,
    /// so an expression is evaluated as in beancount 3.2.3, whose values these
    /// are. They used to be read by the custom-value walk, and before #2806
    /// every one of them pushed its first number (#2812).
    #[test]
    fn test_pushmeta_value_evaluates_arithmetic() {
        use rust_decimal_macros::dec;
        for (value, want) in [
            ("1+2", MetaValue::Int(3)),
            ("(1+2)", MetaValue::Int(3)),
            ("2*3", MetaValue::Int(6)),
            ("10/4", MetaValue::Number(dec!(2.5))),
            ("1-2", MetaValue::Int(-1)),
            ("--1", MetaValue::Int(1)),
            ("(1+2) USD", MetaValue::Amount(Amount::new(dec!(3), "USD"))),
            ("10/4 USD", MetaValue::Amount(Amount::new(dec!(2.5), "USD"))),
            ("\"a\\\"b\"", MetaValue::String("a\"b".into())),
        ] {
            let (errors, pushed) = pushed_value(value);
            assert!(errors.is_empty(), "{value:?}: {errors:?}");
            // Equal as numbers; the scale of a quotient is pinned by
            // `test_arithmetic_division_has_pythons_scale`.
            assert_eq!(pushed, Some(want), "{value:?}");
        }
    }

    /// A division in a value is Python's, as beancount's grammar computes it
    /// (#2813): `10/4` is `2.5` (it was `2.50`, `checked_div`'s scale),
    /// `10.00/4` keeps the ideal `2.50`, and an inexact quotient has 28
    /// significant digits. Checked against beancount 3.2.3's metadata values.
    #[test]
    fn test_arithmetic_division_has_pythons_scale() {
        for (value, want) in [
            ("10/4", "2.5"),
            ("10.00/4", "2.50"),
            ("7.5/3", "2.5"),
            ("1/3", "0.3333333333333333333333333333"),
            ("10/3", "3.333333333333333333333333333"),
            ("10/4 USD", "2.5 USD"),
        ] {
            let (errors, meta) = metadata_value(value);
            assert!(errors.is_empty(), "{value:?}: {errors:?}");
            let text = match meta {
                Some(MetaValue::Number(n)) => n.to_string(),
                Some(MetaValue::Amount(a)) => format!("{} {}", a.number, a.currency),
                other => panic!("{value:?}: {other:?}"),
            };
            assert_eq!(text, want, "{value:?}");
        }
    }

    /// A metadata line and a `pushmeta` follow one grammar rule and must read
    /// one value the same way: the same `MetaValue`, and the same error, with
    /// only the place named in the message differing. They drifted apart while
    /// `pushmeta` had its own reader: `1/0` was an error in one and `Int(1)` in
    /// the other, and `"a\"b"` kept its escape in one (#2812).
    #[test]
    fn test_pushmeta_value_agrees_with_a_metadata_line() {
        for value in [
            "(1+2)",
            "2*3",
            "10/4",
            "1-2",
            "--1",
            "(1+2) USD",
            "1/0",
            "1/0 USD",
            "79228162514264337593543950335 * 10",
            "\"a\\\"b\"",
            "42",
            "-1",
            "10 USD",
            "2024-02-02",
            "Assets:Bank",
            "TRUE",
        ] {
            let (meta_errors, meta) = metadata_value(value);
            let (push_errors, pushed) = pushed_value(value);
            assert_eq!(pushed, meta, "{value:?}");
            let push_errors: Vec<String> = push_errors
                .iter()
                .map(|e| e.replace("pushmeta value", "metadata value"))
                .collect();
            assert_eq!(push_errors, meta_errors, "{value:?}");
        }
    }

    /// An expression whose result overflows `rust_decimal` is an error, not a
    /// silently different number. Stricter than Python on purpose: beancount
    /// 3.2.3 evaluates `79228162514264337593543950335 * 10` to
    /// `7.922816251426433759354395034E+29`, a value we cannot hold (see
    /// `unevaluable_value_error`). The metadata line used to load the first
    /// operand.
    #[test]
    fn test_meta_value_reports_an_overflowing_expression() {
        let overflow = "79228162514264337593543950335 * 10";
        let message = "parse error: invalid arithmetic expression in metadata value \
                       (overflow, division by zero, or an inexact quotient below 1e-28)";
        let (errors, value) = metadata_value(overflow);
        assert_eq!(errors, vec![message.to_string()]);
        assert_eq!(value, Some(MetaValue::None));
        let (errors, value) = metadata_value("1/0");
        assert_eq!(errors, vec![message.to_string()]);
        assert_eq!(value, Some(MetaValue::None));

        // The span covers the expression and its currency.
        let src = "2024-01-01 open Assets:Bank USD\n  kk: 1/0 USD ; note\n";
        let result = parse_via_cst(src);
        let spans: Vec<&str> = result
            .errors
            .iter()
            .map(|e| &src[e.span.start..e.span.end])
            .collect();
        assert_eq!(spans, vec!["1/0 USD"]);
    }

    /// The errors and the custom values of `src`, from the green-wired parse
    /// and the red-only parse, after checking that the two agree.
    fn custom_errors_and_values(src: &str) -> (Vec<(String, String)>, Vec<MetaValue>) {
        let green = parse_via_cst(src);
        let red = parse_red_only(src);
        assert_eq!(
            format!("{:?}", green.errors),
            format!("{:?}", red.errors),
            "trees disagree on errors for {src:?}"
        );
        assert_eq!(
            format!("{:?}", green.directives),
            format!("{:?}", red.directives),
            "trees disagree on directives for {src:?}"
        );
        let errors = green
            .errors
            .iter()
            .map(|e| (e.message(), src[e.span.start..e.span.end].to_string()))
            .collect();
        let values = match green.directives.first().map(|d| &d.value) {
            Some(Directive::Custom(c)) => c.values.clone(),
            _ => panic!("expected a Custom from {src:?}"),
        };
        (errors, values)
    }

    const UNEVALUABLE_CUSTOM: &str = "parse error: invalid arithmetic expression in custom \
                                      value (overflow, division by zero, or an inexact \
                                      quotient below 1e-28)";

    /// An expression in a custom value that is well formed but has no value
    /// is a parse error over the expression and its currency, in both trees,
    /// and emits no value. It used to split silently: `10/0 USD` became `10`
    /// and `0 USD` (#2806). beancount 3.2.3 crashes on `1/0` here.
    #[test]
    fn test_custom_values_report_an_unevaluable_expression() {
        for (src, span) in [
            ("2024-01-01 custom \"x\" 10/0 USD\n", "10/0 USD"),
            ("2024-01-01 custom \"x\" 10/0\n", "10/0"),
            (
                "2024-01-01 custom \"x\" 1 / (2 - 2) USD\n",
                "1 / (2 - 2) USD",
            ),
            (
                "2024-01-01 custom \"x\" 79228162514264337593543950335 * 10 USD\n",
                "79228162514264337593543950335 * 10 USD",
            ),
        ] {
            let (errors, values) = custom_errors_and_values(src);
            assert!(
                errors.contains(&(UNEVALUABLE_CUSTOM.to_string(), span.to_string())),
                "{src:?}: {errors:?}"
            );
            assert!(
                !values.iter().any(|v| matches!(
                    v,
                    MetaValue::Int(_) | MetaValue::Number(_) | MetaValue::Amount(_)
                )),
                "{src:?} must not emit a number from the failed expression: {values:?}"
            );
        }

        // The values around it are kept, and only the failed one is reported.
        let (errors, values) =
            custom_errors_and_values("2024-01-01 custom \"x\" \"a\" 10/0 USD 2*3 TRUE\n");
        assert_eq!(
            errors,
            vec![(UNEVALUABLE_CUSTOM.to_string(), "10/0 USD".to_string())]
        );
        assert_eq!(
            values,
            vec![
                MetaValue::String("a".into()),
                MetaValue::Int(6),
                MetaValue::Bool(true)
            ]
        );
    }

    /// A malformed expression is already a header-line syntax error, as in
    /// beancount (which rejects the directive). It is not reported a second
    /// time, and its numbers are not emitted as values.
    #[test]
    fn test_custom_values_drop_a_malformed_expression() {
        for src in [
            "2024-01-01 custom \"x\" 10 + USD\n",
            "2024-01-01 custom \"x\" 10 *\n",
            "2024-01-01 custom \"x\" (1+2 USD\n",
            // The operand where the read broke off is part of the rejected
            // expression, whatever value it would otherwise be; beancount
            // 3.2.3 rejects each of these.
            "2024-01-01 custom \"x\" 10 + TRUE\n",
            "2024-01-01 custom \"x\" 10 + \"s\"\n",
            "2024-01-01 custom \"x\" 10 + 2024-02-01\n",
            "2024-01-01 custom \"x\" 10 + Assets:A\n",
        ] {
            let (errors, values) = custom_errors_and_values(src);
            assert!(!errors.is_empty(), "{src:?} must be an error");
            assert!(
                !errors.iter().any(|(m, _)| m == UNEVALUABLE_CUSTOM),
                "{src:?} is reported once, by the header check: {errors:?}"
            );
            assert_eq!(values, vec![], "{src:?}");
        }
    }

    /// `10 + TRUE` used to emit `Bool(true)`: the malformed group ended
    /// before the operand, and the walk then read it as a value of its own.
    /// It is rejected whole, with the one header-line error.
    #[test]
    fn test_custom_values_malformed_expression_takes_its_operand() {
        let (errors, values) = custom_errors_and_values("2024-01-01 custom \"x\" 10 + TRUE\n");
        assert_eq!(values, vec![]);
        assert_eq!(errors.len(), 1, "{errors:?}");

        // A value after the rejected expression is still read.
        let (_, values) = custom_errors_and_values("2024-01-01 custom \"x\" 10 + TRUE \"after\"\n");
        assert_eq!(values, vec![MetaValue::String("after".into())]);

        // A malformed pushmeta value pushes nothing, in both trees, and its
        // popmeta then reports the absent key. beancount 3.2.3 gives the same
        // two errors: "syntax error, unexpected BOOL" and "Attempting to pop
        // absent metadata key: 'kk'".
        for src in [
            "pushmeta kk: 1 + TRUE\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 10 *\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            // Anything else left on the line is a syntax error too, and also
            // pushes nothing (beancount: "unexpected ..." then the absent key).
            "pushmeta kk: \"v\" !\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 10 USD @\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: USD,EUR\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 1 2\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 10 USD EUR\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 1 + 2 USD 3\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: ^link\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            // A split date (#2808) with anything else on the line, before or
            // after it or run on from it, is still a syntax error in beancount.
            "pushmeta kk: 2024-02-002 !\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 2024-02-002 5\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 2024-02-002 USD\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 2024-02-002.\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: 2024-002-02,000\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
            "pushmeta kk: \"v\" 2024-02-002\n2024-01-01 open Assets:Bank USD\npopmeta kk:\n",
        ] {
            let green = parse_via_cst(src);
            let red = parse_red_only(src);
            assert_eq!(format!("{:?}", green.errors), format!("{:?}", red.errors));
            assert_eq!(
                format!("{:?}", green.directives),
                format!("{:?}", red.directives)
            );
            assert_eq!(green.errors.len(), 2, "{src:?}: {:?}", green.errors);
            assert!(
                matches!(
                    green.errors[1].kind,
                    crate::ParseErrorKind::InvalidPopmeta(ref key) if key == "kk"
                ),
                "{src:?}: {:?}",
                green.errors
            );
            let Directive::Open(open) = &green.directives[0].value else {
                panic!("expected Open");
            };
            assert_eq!(open.meta.get("kk"), None, "{src:?}");
        }
    }

    /// A division that does not terminate gives beancount 3.2.3's digits for
    /// these inputs. (`10/3` does not: `rust_decimal` keeps 28 decimal places,
    /// `3.3333333333333333333333333333`, where beancount keeps 28 significant
    /// digits, `3.333333333333333333333333333`. That is the shared evaluator,
    /// and balance, price and metadata amounts give the same, so it is not
    /// pinned here.)
    #[test]
    fn test_custom_values_non_terminating_division() {
        use rust_decimal_macros::dec;
        for (src, want) in [
            (
                "2024-01-01 custom \"x\" 1/3 USD\n",
                MetaValue::Amount(Amount::new(dec!(0.3333333333333333333333333333), "USD")),
            ),
            (
                "2024-01-01 custom \"x\" 2/7\n",
                MetaValue::Number(dec!(0.2857142857142857142857142857)),
            ),
            (
                "2024-01-01 custom \"x\" -1/3 USD\n",
                MetaValue::Amount(Amount::new(dec!(-0.3333333333333333333333333333), "USD")),
            ),
        ] {
            let (errors, values) = custom_errors_and_values(src);
            assert_eq!(errors, vec![], "{src:?}");
            assert_eq!(values, vec![want], "{src:?}");
        }
    }

    /// Valid values are unchanged by the check.
    #[test]
    fn test_custom_values_valid_expressions_have_no_error() {
        for (src, want) in [
            ("2024-01-01 custom \"x\" 10 -5\n", vec![MetaValue::Int(5)]),
            (
                "2024-01-01 custom \"x\" 10 5\n",
                vec![MetaValue::Int(10), MetaValue::Int(5)],
            ),
            ("2024-01-01 custom \"x\" -42\n", vec![MetaValue::Int(-42)]),
        ] {
            let (errors, values) = custom_errors_and_values(src);
            assert_eq!(errors, vec![], "{src:?}");
            assert_eq!(values, want, "{src:?}");
        }
    }

    /// A failed expression in a `pushmeta` value is reported too, in both
    /// trees, by the check metadata lines use. The key is pushed with no
    /// value rather than the expression's first number, as a metadata line
    /// gets no value, and its `popmeta` raises no second error.
    #[test]
    fn test_pushmeta_value_reports_an_unevaluable_expression() {
        let src = "pushmeta kk: 1/0\n\
                   2024-01-01 * \"t\"\n  Assets:A  1 USD\n  Assets:B\n\
                   popmeta kk:\n";
        let green = parse_via_cst(src);
        let red = parse_red_only(src);
        assert_eq!(format!("{:?}", green.errors), format!("{:?}", red.errors));
        let errors: Vec<(String, &str)> = green
            .errors
            .iter()
            .map(|e| (e.message(), &src[e.span.start..e.span.end]))
            .collect();
        assert_eq!(
            errors,
            vec![(
                "parse error: invalid arithmetic expression in pushmeta value \
                 (overflow, division by zero, or an inexact quotient below 1e-28)"
                    .to_string(),
                "1/0"
            )]
        );
        let Directive::Transaction(txn) = &green.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(txn.meta.get("kk"), Some(&MetaValue::None));
    }

    /// `header_grammar_reaches(src, at)` for the byte offset of the first
    /// occurrence of `at` in `src` (`quiet_after_invalid_tokens`).
    fn header_reaches_at(src: &str, at: &str) -> bool {
        let first = src.find(at).expect("`at` occurs in `src`");
        let source_file = SourceFile::parse(src);
        header_grammar_reaches(source_file.syntax(), src, first)
    }

    /// `header_grammar_reaches` is true for a token among a non-transaction
    /// directive's header tokens when the header's rule reads up to it: no
    /// defect at all (`Assets:A`), or the first defect at the token itself
    /// (`$~`, where the balance expects its currency).
    #[test]
    fn test_header_grammar_reaches_a_header_token_the_rule_reads_up_to() {
        assert!(header_reaches_at("2024-01-01 open Assets:A\n", "Assets:A"));
        assert!(header_reaches_at(
            "2024-01-01 balance Assets:A 1.00 $~ 0.01 USD\n",
            "$~"
        ));
        // The token right at the start of a directive is that directive's
        // (the right-biased token at the offset), not the end of the line
        // before it.
        assert!(header_reaches_at(
            "2024-01-01 open Assets:B\n2024-01-01 close Assets:A\n",
            "2024-01-01 close"
        ));
    }

    /// `header_grammar_reaches` is false when the header's rule fails before
    /// the token (`open` expects an account at the `5`), and for a token that
    /// is not one of a non-transaction directive's header tokens: a metadata
    /// line's (whose `META_ENTRY` is no directive, though it is the token's
    /// nearest ancestor), a posting's (a transaction has no header rule
    /// here), the end of an empty source, and an offset past what a tree can
    /// hold.
    #[test]
    fn test_header_grammar_reaches_is_false_off_the_header_rule() {
        assert!(!header_reaches_at("2024-01-01 open 5 $x\n", "$x"));
        assert!(!header_reaches_at(
            "2024-01-01 open Assets:A\n  kk: $x\n",
            "kk"
        ));
        assert!(!header_reaches_at(
            "2024-01-01 *\n  Assets:A  1 USD\n  Assets:B\n",
            "Assets:A"
        ));
        let empty = SourceFile::parse("");
        assert!(!header_grammar_reaches(empty.syntax(), "", 0));
        let src = "2024-01-01 open Assets:A\n";
        let source_file = SourceFile::parse(src);
        if let Ok(first) = usize::try_from(u64::from(u32::MAX) + 1) {
            assert!(!header_grammar_reaches(source_file.syntax(), src, first));
        }
    }

    /// A comment line between two directives is leading trivia of the
    /// second one's node, before any of its header tokens: no header token
    /// at all starts at or before it, which `header_grammar_reaches` answers
    /// `false` for rather than running the rule on nothing.
    #[test]
    fn test_header_grammar_reaches_is_false_before_the_first_header_token() {
        assert!(!header_reaches_at(
            "2024-01-01 open Assets:B ; c\n  ; x\n2024-01-01 open Assets:A\n",
            "; x"
        ));
    }
}

#[cfg(test)]
mod custom_rejected_values {
    use super::*;

    /// A `custom` directive must not report a value it has just rejected.
    ///
    /// `Custom.values` used to carry the tag, link or bare currency that the
    /// same parse had raised an error for, so a consumer reading `values`
    /// without also reading `errors` saw data the parser had declared invalid
    /// (#2190).
    ///
    /// All three types are rejected by beancount too, measured across its
    /// eight custom value types -- so this is not a stricter grammar, only an
    /// honest one.
    #[test]
    fn a_rejected_custom_value_is_not_emitted() {
        for (src, what) in [
            ("2024-01-05 custom \"b\" #atag\n", "tag"),
            ("2024-01-05 custom \"b\" ^alink\n", "link"),
            ("2024-01-05 custom \"b\" USD\n", "bare currency"),
        ] {
            let res = crate::parse(src);
            assert_eq!(res.errors.len(), 1, "{what} must be rejected: {src:?}");
            let values = res
                .directives
                .iter()
                .find_map(|d| match &d.value {
                    Directive::Custom(c) => Some(c.values.clone()),
                    _ => None,
                })
                .expect("the directive still parses, minus the bad value");
            assert!(
                values.is_empty(),
                "the rejected {what} must not survive into values; got {values:?}",
            );
        }
    }

    /// Only the rejected value is dropped. A directive mixing good and bad
    /// values keeps the good ones, so this is not "discard the whole line".
    #[test]
    fn valid_custom_values_survive_alongside_a_rejected_one() {
        let res = crate::parse("2024-01-05 custom \"b\" \"ok\" #atag 42\n");
        assert_eq!(res.errors.len(), 1, "the tag is rejected");
        let values = res
            .directives
            .iter()
            .find_map(|d| match &d.value {
                Directive::Custom(c) => Some(c.values.clone()),
                _ => None,
            })
            .expect("custom directive");
        assert_eq!(
            values,
            vec![MetaValue::String("ok".to_string()), MetaValue::Int(42)],
            "the string and the integer survive; only the tag is dropped",
        );
    }

    /// A `#tag` is still a legal METADATA value -- beancount accepts one there
    /// and stores it, so the shared `value_tokens_to_meta` must keep producing
    /// `MetaValue::Tag`. Only the custom-directive path filters it.
    ///
    /// Pinned because the fix above filters a value the two paths share, and
    /// filtering it one level lower would silently break metadata.
    #[test]
    fn a_tag_is_still_a_valid_metadata_value() {
        let res = crate::parse("2024-01-20 note Assets:A \"n\"\n  mytag: #kept\n");
        assert!(
            res.errors.is_empty(),
            "tag metadata parses: {:?}",
            res.errors
        );
        let meta = res
            .directives
            .iter()
            .find_map(|d| match &d.value {
                Directive::Note(n) => Some(n.meta.clone()),
                _ => None,
            })
            .expect("note directive");
        assert_eq!(
            meta.get("mytag"),
            Some(&MetaValue::Tag(Tag::new("kept"))),
            "the tag survives as a Tag in metadata; got {meta:?}",
        );
    }
}

/// Make the count of generic errors on a line beancount cannot read match
/// beancount's (#2787).
///
/// Two of our rules can fire for one line: the line (or directive) error,
/// and an inline error for each `ERROR_TOKEN` on it. `  * h` after a
/// transaction's postings gave two overlapping errors. Beancount reports an
/// `Invalid token` error for each token its lexer cannot read, and a syntax
/// error only when its grammar fails at a readable token first: once the
/// lexer has reported an error, bison's recovery reports nothing more for
/// that statement. So `  * h` is one error there (the `*` is a posting
/// flag, then `h` is unreadable), while `  ** h` and `  @ x` are two (the
/// grammar fails at the second `*`, at the `@`).
///
/// Here the line error stands for beancount's first error on the line. When
/// the tokens before the first `ERROR_TOKEN` on it are a readable start of
/// an indented line (nothing, a posting flag, or an optional flag, an
/// account and a prefix of a plain amount), the grammar has not failed
/// before it, so that `ERROR_TOKEN`'s own error is the one beancount reports
/// and the line error already stands for it: it is dropped, and a generic
/// line error takes over its name (`unexpected input: invalid token 'h'`,
/// as bean-check's `Invalid token: 'h'`), so the editor still names it.
/// The same holds on a header line the converter dropped with a whole-node
/// error, when the header grammar (`grammar_failures`) first fails at that
/// very token (`2024-01-01 open Ass'ets:A`, #2872).
/// Every later `ERROR_TOKEN` keeps its error, as each is one more `Invalid
/// token` there. The line error is the one kept, not the inline one,
/// because the formatter's verbatim-copy ranges are read from the outer
/// errors. The outer error may be any syntax error (a
/// posting's `unexpected trailing tokens` holds the `oops` in
/// `Assets:A  -1 oops USD`); only a generic inner one is dropped. Errors of
/// any other kind are left alone, and so is a generic error on a later line
/// of a multi-line one.
///
/// `errors` is sorted by start and stays so. Linear in the number of errors
/// plus, only when there are two or more syntax errors, the source length
/// (for the line starts) and one lexing of each covered line's prefix.
fn drop_errors_inside_a_line_error(
    errors: &mut Vec<crate::ParseError>,
    stripped: &str,
    bom_offset: u32,
    grammar_failures: &[(usize, usize, usize)],
) {
    use crate::logos_lexer::Token;
    let is_generic = |e: &crate::ParseError| match &e.kind {
        crate::ParseErrorKind::SyntaxError(m) => m == "unexpected input",
        _ => false,
    };
    let is_bom =
        |e: &crate::ParseError| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody);
    // A BOM error takes part only as an inner error: the inline one of a
    // BOM-led invalid token (#2928), never a line error that holds others.
    let mut syntax: Vec<usize> = (0..errors.len())
        .filter(|&i| {
            matches!(errors[i].kind, crate::ParseErrorKind::SyntaxError(_)) || is_bom(&errors[i])
        })
        .collect();
    if syntax.len() < 2 || !syntax.iter().any(|&i| is_generic(&errors[i])) {
        return;
    }
    // Longest first among equal starts, so a container precedes what it holds.
    syntax.sort_by_key(|&i| (errors[i].span.start, std::cmp::Reverse(errors[i].span.end)));
    let bom = bom_offset as usize;
    #[cfg(test)]
    test_counters::ERROR_LINE_SCANNED_BYTES.with(|c| c.set(c.get() + stripped.len()));
    let newlines: Vec<usize> = stripped
        .bytes()
        .enumerate()
        .filter_map(|(i, b)| (b == b'\n').then_some(i + bom))
        .collect();
    // The line `at` is on: its start and the position of its `\n`.
    let line_of = |at: usize| {
        let k = newlines.partition_point(|&n| n < at);
        let start = k.checked_sub(1).map_or(bom, |k| newlines[k] + 1);
        (start, newlines.get(k).copied().unwrap_or(usize::MAX))
    };
    // Whether `prefix`, the text of an indented line before its first
    // unreadable token, is a readable start of one.
    let readable_start = |prefix: &str| {
        #[cfg(test)]
        test_counters::ERROR_LINE_SCANNED_BYTES.with(|c| c.set(c.get() + prefix.len()));
        let tokens: Vec<Token<'_>> = crate::logos_lexer::tokenize(prefix)
            .into_iter()
            .map(|(t, _)| t)
            .filter(|t| {
                !matches!(
                    t,
                    Token::Indent(_) | Token::DeepIndent(_) | Token::Whitespace(_)
                )
            })
            .collect();
        let is_flag = |t: &Token<'_>| {
            matches!(
                t,
                Token::Star | Token::Pending | Token::Flag(_) | Token::Hash
            )
        };
        // A posting's start: an account, then a prefix of a plain amount
        // (`[-+]? NUMBER CURRENCY`). Anything longer is left to the grammar
        // (`Assets:A****` fails at the `*`), so both errors are kept.
        let posting_start = |rest: &[Token<'_>]| match rest {
            [Token::Account(_), amount @ ..] => {
                let amount = match amount {
                    [Token::Minus | Token::Plus, tail @ ..] => tail,
                    other => other,
                };
                matches!(
                    amount,
                    [] | [Token::Number(_)] | [Token::Number(_), Token::Currency(_)]
                )
            }
            _ => false,
        };
        match tokens.as_slice() {
            [] => true,
            [first] if is_flag(first) => true,
            [first, rest @ ..] if is_flag(first) => posting_start(rest),
            rest => posting_start(rest),
        }
    };
    let mut dropped = vec![false; errors.len()];
    // The outermost syntax error seen so far: its span, the end of its
    // first line, and whether an error inside it was already considered.
    let mut cover: Option<(usize, usize, usize, bool, usize)> = None;
    // The line errors that take over a dropped error's name.
    let mut renamed: Vec<(usize, usize)> = Vec::new();
    for &i in &syntax {
        let span = errors[i].span;
        match cover.as_mut() {
            Some((start, end, line_end, seen, outer))
                if span.start >= *start && span.end <= *end =>
            {
                if *seen || span.start >= *line_end {
                    continue;
                }
                // Whether the line's grammar first fails at this token, so
                // its own error is beancount's first one on the line and the
                // line error stands for it: a directive the converter
                // dropped, whose header grammar first fails here
                // (`2024-01-01 open Ass'ets:A`), or an indented line whose
                // start before it is one beancount reads.
                let fails_here = || {
                    let (line_start, _) = line_of(span.start);
                    let prefix = stripped
                        .get(line_start - bom..span.start - bom)
                        .unwrap_or_default();
                    grammar_failures
                        .binary_search_by_key(&errors[*outer].span.start, |&(s, _, _)| s)
                        .is_ok_and(|j| grammar_failures[j].2 == span.start)
                        || (prefix.starts_with([' ', '\t']) && readable_start(prefix))
                };
                // A mid-line BOM-led invalid token where the line's grammar
                // first fails (`price USD 1 <BOM>EUR`, `  <BOM>a`):
                // beancount's one `Invalid token` there. The token's own
                // `BomInDirectiveBody` is that error, and the generic line
                // error is dropped for it, so the line is one error, reported
                // at the token, as it was before #2928 merged the BOM into the
                // token. (Unlike the generic merge below, the inner error is
                // the one kept here: it already has the right kind and the
                // token's span. The formatter still copies the directive
                // verbatim, as the token lies inside its node.) Any other BOM
                // error is left alone and does not count as the first error
                // inside the line error.
                if is_bom(&errors[i]) {
                    if is_generic(&errors[*outer]) && fails_here() {
                        *seen = true;
                        dropped[*outer] = true;
                    }
                    continue;
                }
                *seen = true;
                // Another rule's error there first stands for a grammar
                // failure before any unreadable token: keep everything.
                if !is_generic(&errors[i]) {
                    continue;
                }
                if fails_here() {
                    dropped[i] = true;
                    renamed.push((*outer, i));
                }
            }
            _ if is_bom(&errors[i]) => {}
            _ => {
                let (_, line_end) = line_of(span.start);
                cover = Some((span.start, span.end, line_end, false, i));
            }
        }
    }
    for (outer, inner) in renamed {
        if !is_generic(&errors[outer]) {
            continue;
        }
        let span = errors[inner].span;
        let text = stripped
            .get(span.start.saturating_sub(bom)..span.end.saturating_sub(bom))
            .unwrap_or_default();
        errors[outer].kind = crate::ParseErrorKind::SyntaxError(format!(
            "unexpected input: invalid token '{}'",
            invalid_token_name(text)
        ));
    }
    let mut index = 0;
    errors.retain(|_| {
        let keep = !dropped[index];
        index += 1;
        keep
    });
}

/// The `Invalid token` errors of one `ERROR_NODE` line, after its line error
/// (`emit_error_node_line`, which both parse paths run this from).
///
/// beancount's lexer reports every token it cannot read, whatever its
/// grammar does with the line: `foo bar$ baz` is three `Invalid token`
/// errors there, `"plugin "p" "c"` a syntax error at the first string and
/// `Invalid token: 'p"'`. The line error stands for the first of them when
/// what comes before it is a start beancount's grammar reads
/// (`readable_start_of_an_error_line`: `foo`, `2024-01-01 commodi*ty`), and
/// is the grammar error otherwise; each other invalid token on the line gets
/// its own error.
///
/// A mid-file BOM is reported by the line's `BomInDirectiveBody`, which also
/// stands for some of beancount's `Invalid token` errors (#2928):
///
/// - A BOM that starts its line keeps its own extent here
///   ([`is_line_start_bom_token`]), where beancount's invalid token runs on
///   through whatever is glued to it. So it is the line's first invalid
///   token, the one the line error stands for, and an invalid run in its
///   blank-free run (`<BOM>foo`, `<BOM>12$`) is part of that same token, not
///   one more. After a `<BOM>*` heading start, each invalid run after the
///   first blank is one more ([`invalid_runs`]).
/// - When the line's error is not the BOM diagnostic (an invalid account),
///   the BOM one comes after it as a second error (`secondary_bom`), and
///   stands for the line's first invalid token with a stray BOM in it,
///   BOM-led or not.
/// - A token with a BOM inside it, not at its start (nor right after a lone
///   capital, `A<BOM>b`, which counts as BOM-led), is left to the line's BOM
///   diagnostic only while that diagnostic stands for nothing else: not once
///   it stood for a BOM that starts the line or a BOM-led first token, nor
///   when it is the second error.
///
/// Every other token gets its own error, a BOM-led one included: in the
/// middle of a line it runs to the next blank, as beancount's does. Pinned,
/// combination by combination, by `tests/bom_combination_matrix.rs`.
///
/// `invalid` holds the line's `ERROR_TOKEN` ranges (stripped frame) and
/// `line_start` where its first token starts.
pub(super) fn report_invalid_tokens_of_error_line(
    line_start: usize,
    invalid: &[std::ops::Range<usize>],
    stripped: &str,
    bom_offset: u32,
    secondary_bom: bool,
    out: &mut Vec<crate::ParseError>,
) {
    let off = bom_offset as usize;
    let mut secondary_bom = secondary_bom;
    // Whether the line's BOM diagnostic already stands for a token, so a
    // token with a BOM inside it is one more invalid token.
    let mut bom_diagnostic_spent = secondary_bom;
    // Whether the token being looked at is the line's first invalid one. A
    // line-start BOM never leaves this set for the token after it to read:
    // the prefix then holds the BOM, which is no readable start.
    let mut first = true;
    // Where the run of BOMs that starts the line ends, once there is one.
    let mut line_start_boms_end: Option<usize> = None;
    let report = |at: std::ops::Range<usize>, text: &str, out: &mut Vec<crate::ParseError>| {
        out.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(format!(
                "unexpected input: invalid token '{}'",
                invalid_token_name(text)
            )),
            Span::new(at.start + off, at.end + off),
        ));
    };
    // Where the account beancount reads a line-start BOM run into ends, when
    // no account of rledger's follows the BOMs (`<BOM>assets:A`): tokens
    // before it are part of that account, and the rest of the blank-free run
    // after it is beancount's next token.
    let mut account_glue_end: Option<usize> = None;
    for range in invalid {
        let text = stripped.get(range.clone()).unwrap_or_default();
        let bom_account = is_bom_account_token(stripped, range.start, text);
        if is_line_start_bom_token(stripped, range.start, text) {
            bom_diagnostic_spent = true;
            let from = &stripped[range.start..];
            let last_of_run = !from[text.len()..].starts_with(crate::bom::BOM_CHAR);
            line_start_boms_end = None;
            account_glue_end = None;
            if bom_account {
                // An account of its own after the BOMs ends beancount's
                // token there (`<BOM><BOM>Assets:A$x` is the account, then
                // `$x`), so nothing after it is glued to them.
            } else if let Some((_, end)) = last_of_run
                .then(|| crate::logos_lexer::bom_led_account(from))
                .flatten()
            {
                account_glue_end = Some(range.start + end);
            } else {
                line_start_boms_end = Some(range.end);
            }
            continue;
        }
        // BOMs beancount reads into an account: none of its invalid tokens.
        if bom_account {
            continue;
        }
        // The account a line-start BOM run starts, in beancount
        // (`<BOM>assets:A$x`): a token inside it is part of it, and the part
        // of a token past its end is beancount's next token, an invalid one
        // when it lexes so (`$x`, but not `"x"`, `#t` or `;c`).
        if let Some(end) = account_glue_end {
            if range.end <= end {
                continue;
            }
            account_glue_end = None;
            if range.start < end {
                let tail = &stripped[end..range.end];
                // `runs` index ` {tail}`: one byte before `end`.
                let (runs, comment) = invalid_runs(&format!(" {tail}"));
                for run in runs {
                    let at = end + run.start - 1..end + run.end - 1;
                    report(at.clone(), &stripped[at], out);
                }
                // A `;` where beancount's tokens leave off starts its
                // comment, which takes the rest of the line: right after the
                // account (`<BOM><BOM>kk:<BOM>;c <BOM>1.5`) or after a later
                // token of the tail (`<BOM>assets:A~<BOM>1:A;c $x`).
                if comment {
                    break;
                }
                continue;
            }
        }
        // In the same blank-free run as the BOMs that start the line, glued
        // to them directly (`<BOM>foo`) or through tokens that lex here
        // (`<BOM>12$`): part of the same beancount token. The unread rest of
        // a `<BOM>*` heading line holds a blank: its part up to the blank is
        // that token too, and each invalid token after the blank is one more,
        // as beancount lexes the rest of such a line.
        if let Some(end) = line_start_boms_end {
            if stripped
                .get(end..range.start)
                .is_some_and(|between| !between.contains([' ', '\t']))
            {
                if let Some(blank) = text.find([' ', '\t']) {
                    let rest_start = range.start + blank;
                    // The rest runs to the end of the line: a comment in it
                    // leaves nothing after it to stop.
                    let (runs, _) = invalid_runs(&text[blank..]);
                    for run in runs {
                        let at = rest_start + run.start..rest_start + run.end;
                        report(at.clone(), &stripped[at], out);
                    }
                }
                continue;
            }
            line_start_boms_end = None;
        }
        let holds_bom = text.contains(crate::bom::BOM_CHAR);
        // BOM-led for counting: a BOM starts it, or a lone capital glued to
        // a BOM does (`A<BOM>b`), which the lexer folds into the run after it
        // and beancount reads as one invalid token from the capital on.
        let bom_led = text.starts_with(crate::bom::BOM_CHAR)
            || text
                .strip_prefix(|c: char| c.is_ascii_uppercase())
                .is_some_and(|rest| rest.starts_with(crate::bom::BOM_CHAR));
        let starts_the_line = std::mem::take(&mut first)
            && stripped
                .get(line_start..range.start)
                .is_some_and(readable_start_of_an_error_line);
        // A run that starts with a blank is not an invalid token but the rest
        // of a heading line after its `*`, which the lexer skips unread.
        if starts_the_line || text.starts_with([' ', '\t']) {
            // The line's error stands for this first token; when it holds a
            // stray BOM, that error is the BOM diagnostic, now spent on it.
            bom_diagnostic_spent |= starts_the_line && bom_led;
            continue;
        }
        if holds_bom && secondary_bom {
            secondary_bom = false;
            continue;
        }
        if holds_bom && !bom_led && !bom_diagnostic_spent {
            continue;
        }
        report(range.clone(), text, out);
    }
}

/// The invalid tokens of `rest`, the text after the first blank of an unread
/// heading line: each blank-free run beancount cannot read whole, as ranges
/// into `rest`. A run is invalid when the lexer makes an error token of any
/// of it, or when a lone capital in it is glued to the token after it
/// (beancount's `CAPITAL` needs a blank after it). A comment ends the line,
/// and the second value says whether one did.
///
/// A `{#` is read as beancount reads it, a `{` and then whatever the `#`
/// starts (`{#t` is a brace and a tag, no invalid token): the lexer resumes
/// right after the brace, mid-line, so the cost stays linear in `rest`.
fn invalid_runs(rest: &str) -> (Vec<std::ops::Range<usize>>, bool) {
    use crate::logos_lexer::{Token, TokenIter};
    let mut out = Vec::new();
    // The open run: its range and whether it is invalid so far.
    let mut run: Option<(std::ops::Range<usize>, bool)> = None;
    let mut after_lone_capital = false;
    // Where the token before this one starts: a lone capital there starts
    // beancount's invalid token.
    let mut prev_start = 0;
    let close = |run: &mut Option<(std::ops::Range<usize>, bool)>,
                 out: &mut Vec<std::ops::Range<usize>>| {
        if let Some((range, true)) = run.take() {
            out.push(range);
        }
    };
    let mut tokens = TokenIter::new(rest, true);
    let mut comment = false;
    while let Some((token, span)) = tokens.next() {
        let (span, error) = match token {
            Token::Whitespace(_) | Token::Newline => {
                close(&mut run, &mut out);
                after_lone_capital = false;
                continue;
            }
            // `rest` starts with a blank, so a `#!` or `#+` in it is mid-line and
            // lexes as a `#` and the token after it (#2928), never as a comment.
            Token::Comment(_) | Token::PercentComment(_) => {
                comment = true;
                break;
            }
            // The `{` alone; the lexer resumes after it.
            Token::LBraceHash => {
                let brace_end = span.start + 1;
                tokens = TokenIter::new_mid_line(rest, true, brace_end);
                (span.start..brace_end, false)
            }
            // BOMs beancount reads into an account are no invalid token.
            Token::Error(t) => (
                span.start..span.end,
                !is_bom_account_token(rest, span.start, t),
            ),
            _ => (span.start..span.end, false),
        };
        // A token glued to a lone capital is invalid from the capital on
        // (`A{#t`, `A$x`).
        let invalid = error || after_lone_capital;
        // A run's range starts where beancount's invalid token does, past
        // the valid tokens before it (`{#t{#$x` is `$x`).
        let start = if after_lone_capital {
            prev_start
        } else {
            span.start
        };
        match run.as_mut() {
            Some((range, bad)) => {
                if invalid && !*bad {
                    range.start = start;
                }
                range.end = span.end;
                *bad |= invalid;
            }
            None => run = Some((span.clone(), invalid)),
        }
        after_lone_capital = matches!(token, Token::Currency(c) if c.len() == 1);
        prev_start = span.start;
    }
    close(&mut run, &mut out);
    (out, comment)
}

/// Whether `prefix`, the text of an `ERROR_NODE` line before its first invalid
/// token, is one beancount's grammar reads without failing: nothing (past the
/// indentation), or a date (`2024-01-01 commodi*ty USD`, where a directive
/// keyword or flag is expected next). Then the invalid token is the line's
/// first error and its line error stands for it. Any other prefix (a string,
/// a number, an orphan indented account) is where the grammar fails first.
fn readable_start_of_an_error_line(prefix: &str) -> bool {
    let rest = prefix.trim_start_matches([' ', '\t']);
    rest.is_empty()
        || crate::logos_lexer::leading_date_len(rest)
            .is_some_and(|n| rest[n..].trim_matches([' ', '\t']).is_empty())
}

/// Drop every error that starts on a line after its first invalid token,
/// other than the lexer's own errors there (#2872).
///
/// beancount's lexer reports each token it cannot read, and its grammar never
/// sees one: the statement fails at it, and bison's recovery discards the rest
/// of the line in silence, reporting nothing more for it. So
/// `custom "b" $10 /6J` is `Invalid token: '$10'` alone there, never also a
/// complaint about the bare `/6J` after it. Our per-construct checks each ran
/// on whatever followed. Kept after the invalid token: another invalid
/// token's error (an error starting at an `ERROR_TOKEN`), an invalid date
/// (beancount builds dates in its lexer, so it reports them wherever they
/// stand) and a mid-file BOM. A BOM-led token counts as an invalid token
/// (#2928), unless it is BOMs beancount reads into an account
/// (`is_bom_account_token`).
///
/// That includes a BOM that starts its line ([`is_line_start_bom_token`]),
/// which is beancount's first invalid token on the line too. Counting it
/// changes no output today: such a line is an `ERROR_NODE` line, whose line
/// error (and secondary BOM error) starts at the BOM, not after it, and whose
/// other errors are all of the kinds kept above (an invalid token's error, at
/// or inside an `ERROR_TOKEN`, an invalid date). So the line-start rule is
/// not asked here.
///
/// `errors` is sorted by start and stays so. Walks the green tree for the
/// `ERROR_TOKEN`s, only when there are errors at all, and steps over each
/// byte of the source at most once looking for line ends.
fn quiet_after_invalid_tokens(
    errors: &mut Vec<crate::ParseError>,
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
) {
    use crate::SyntaxKind as K;
    if errors.is_empty() {
        return;
    }
    let off = bom_offset as usize;
    let mut invalid: Vec<usize> = Vec::new();
    let mut unread: Vec<(usize, usize)> = Vec::new();
    let mut stack = vec![(
        root.green().to_owned(),
        usize::from(root.text_range().start()),
    )];
    while let Some((node, start)) = stack.pop() {
        let mut at = start;
        for child in node.children() {
            match child {
                rowan::NodeOrToken::Node(n) => {
                    let len = usize::from(n.text_len());
                    stack.push((n.to_owned(), at));
                    at += len;
                }
                rowan::NodeOrToken::Token(t) => {
                    if <crate::BeancountLanguage as rowan::Language>::kind_from_raw(t.kind())
                        == K::ERROR_TOKEN
                        && !is_bom_account_token(stripped, at, t.text())
                    {
                        invalid.push(at);
                        // The invalid tokens counted inside one (the unread
                        // rest of a `<BOM>*` heading line, the tail of an
                        // account a line-start BOM run starts; see
                        // `report_invalid_tokens_of_error_line`) are the
                        // lexer's own errors too.
                        unread.push((at, at + t.text().len()));
                    }
                    at += t.text().len();
                }
            }
        }
    }
    // A shortcut: with no invalid token the loop below drops nothing.
    if invalid.is_empty() {
        return;
    }
    invalid.sort_unstable();
    unread.sort_unstable();
    let inside_unread = |at: usize| {
        // `s <= at` would differ only for an error that starts where an
        // unread token does, and the one caller asks only after its search
        // of `invalid` (the same starts) found none there. That caller asks
        // for an error after its line's first invalid token, whose entry
        // comes before it, so there is always one (`is_none_or` would be
        // the same); and `at <= e` would differ only for an error that
        // starts right where a token ends, which is a blank or a line end
        // for every invalid token but a line-start BOM's, whose line's
        // errors are all kept.
        let i = unread.partition_point(|&(s, _)| s < at);
        i.checked_sub(1)
            .and_then(|i| unread.get(i))
            .is_some_and(|&(_, e)| at < e)
    };
    let mut dropped = vec![false; errors.len()];
    // The end (its `\n`, or the end of the source) of the last line handled.
    let mut line_end = 0;
    for (k, &first) in invalid.iter().enumerate() {
        // `<=` would differ only for a token at offset 0, the first
        // `line_end`: any later one is a `\n`, where no token starts. A line
        // that starts with an invalid token is an `ERROR_NODE` line, whose
        // errors are all kept below anyway (its line error starts where its
        // content does, the others are invalid tokens' own errors, invalid
        // dates and BOM errors), so handling that line changes nothing.
        if first < line_end {
            continue;
        }
        // `invalid` and `unread` hold the same starts, both sorted.
        let token_end = unread[k].1;
        let line_start = stripped[line_end..first]
            .rfind('\n')
            .map_or(line_end, |i| line_end + i + 1);
        let indented = &stripped[line_start..first];
        let content = line_start + indented.len() - indented.trim_start_matches([' ', '\t']).len();
        line_end = stripped[first..]
            .find('\n')
            .map_or(stripped.len(), |i| first + i);
        let (at, to) = (first + off, line_end + off);
        // Whether the line's grammar gets as far as the invalid token, asked
        // at most once per line and only when an error contains the token.
        let mut reaches: Option<bool> = None;
        // Past the errors that start where the line's content does: such an
        // error stands for the whole line (its line error, or a check of
        // the line from its first token), and is kept, so `<` would change
        // nothing.
        let mut i = errors.partition_point(|e| e.span.start <= content + off);
        while let Some(e) = errors.get(i) {
            // An error at the line's own `\n` is on the line, so `>`, not
            // `>=`. None starts there today (a defect at the end of a line
            // points at its last token), so the two agree.
            if e.span.start > to {
                break;
            }
            // A construct check's own error, not one that names an invalid
            // token or stands for its line (`unexpected input`).
            let construct_check = matches!(
                &e.kind,
                crate::ParseErrorKind::SyntaxError(m) if !m.starts_with("unexpected input")
            );
            // One that starts at the token and runs past it is asked below
            // whether it is a construct check, like one that starts before;
            // anything else that starts at the token is kept either way.
            dropped[i] = if e.span.start < at || (e.span.start == at && e.span.end > token_end) {
                // A check of a construct the invalid token sits inside (a
                // cost spec, an amount expression, a posting's trailing
                // tokens, a balance's amount), when the line's grammar fails
                // at that token, not before it: `{{2 .USD}}` is the invalid
                // token alone in beancount, `{}{$` an `unexpected LCURL` at
                // the second `{` and the token. Not a line error, which
                // starts where the line's content does. Such a check may
                // start right at the token, when the token is glued to what
                // comes before it: a posting's trailing tokens start where
                // its amount ends (`1 HOOL<BOM>@ 2 USD`, `1 HOOL$@ 2 USD`).
                // Only when the line's grammar reads up to the token
                // (`balance Assets:A 1.00 $~ 0.01 USD`); elsewhere the error
                // is where the grammar fails first (`price /6"E_X`: the price
                // expects a currency at the `/`), and is kept.
                //
                // Only a construct check's error, too. A header's line error
                // starts where the header does, which is past the line's
                // start, so before the token, when a BOM is left at the very
                // start of a file (`<BOM><BOM>2024-01-02 event \x11`); it
                // stands for its line and is kept. On an indented line every
                // other error that starts before the token is a line error,
                // at the line's content (skipped above), or covers one token
                // before the invalid one (an invalid date, an account), so
                // there this condition changes nothing.
                //
                // A check that ends right at the token (a posting's sign
                // check, `-$x`) is kept, one error more than beancount;
                // `>=` would drop it too (#2967).
                e.span.end > at
                    && construct_check
                    && *reaches.get_or_insert_with(|| {
                        if content > line_start {
                            indented_grammar_reaches(stripped, line_start, line_end, first)
                        } else {
                            header_grammar_reaches(root, stripped, first)
                        }
                    })
            } else {
                // The error starts at the token or after it. One at the
                // token is that token's own error: the search finds the
                // token and keeps it.
                invalid.binary_search(&(e.span.start - off)).is_err()
                    && !inside_unread(e.span.start - off)
                    && !matches!(
                        e.kind,
                        crate::ParseErrorKind::InvalidDateValue(_)
                            | crate::ParseErrorKind::BomInDirectiveBody
                    )
            };
            i += 1;
        }
    }
    let mut index = 0;
    errors.retain(|_| {
        let keep = !dropped[index];
        index += 1;
        keep
    });
}

/// Whether beancount's grammar for the indented line `stripped[line_start..
/// line_end]` (a posting, or a metadata line when it starts with a key) gets
/// as far as the invalid token at `first` before it fails, so that token is
/// the line's first error (`quiet_after_invalid_tokens`). The line is lexed
/// alone and its tokens up to that one are run through the posting or
/// metadata rule, the same rules `posting_line_check` and `meta_entry_check`
/// apply. Linear in the line.
fn indented_grammar_reaches(
    stripped: &str,
    line_start: usize,
    line_end: usize,
    first: usize,
) -> bool {
    use crate::SyntaxKind as K;
    let line = &stripped[line_start..line_end];
    let tokens: Vec<(K, std::ops::Range<usize>)> =
        super::lossless_tokens::lossless_kind_tokens(line)
            .into_iter()
            .map(|(k, r)| (k, r.start + line_start..r.end + line_start))
            .take_while(|(_, r)| r.start <= first)
            .collect();
    let end = tokens.last().map_or(first, |(_, r)| r.end);
    let is_meta = tokens
        .iter()
        .find(|(k, _)| !matches!(k, K::WHITESPACE | K::COMMENT | K::BOM))
        .is_some_and(|(k, _)| *k == K::META_KEY);
    let defect = if is_meta {
        super::directive_header::first_meta_defect(&tokens, end, stripped)
    } else {
        super::directive_header::first_posting_defect(&tokens, end, stripped)
    };
    defect.is_none_or(|d| d.range.start >= first)
}

/// Whether beancount's grammar for the header line of the non-transaction
/// directive the invalid token at `first` sits in reads up to that token
/// before it fails, so the token is the line's first error
/// (`quiet_after_invalid_tokens`): the header's tokens up to that one are run
/// through the directive's rule (`first_header_defect`), the one
/// `directive_header_check` applies. `false` for a token in no such directive, or
/// not among its header's tokens. Linear in the header.
fn header_grammar_reaches(root: &crate::SyntaxNode, stripped: &str, first: usize) -> bool {
    let Ok(offset) = u32::try_from(first) else {
        return false;
    };
    let Some(token) = root.token_at_offset(offset.into()).right_biased() else {
        return false;
    };
    let Some(node) = token
        .parent_ancestors()
        .find(|n| super::directive_header::directive_keyword(n.kind()).is_some())
    else {
        return false;
    };
    let mut tokens = Vec::new();
    header_line_tokens(&node, &mut tokens);
    tokens.retain(|(_, r)| r.start <= first);
    if tokens.last().is_none_or(|(_, r)| r.start != first) {
        return false;
    }
    // The rule points a defect at `end` (here `first`) only when it consumes
    // no token at all, and it always consumes the first one: a header's
    // first token is never whitespace, a comment or a BOM, which the rule
    // skips. So any `end` gives the same answer.
    super::directive_header::first_header_defect(node.kind(), &tokens, first, stripped)
        .is_none_or(|d| d.range.start >= first)
}

/// An unreadable token's text as an error message names it: escaped (so a
/// control character or a quote cannot garble the message) and capped at 40
/// characters, with `...` after a longer one.
fn invalid_token_name(text: &str) -> String {
    const MAX: usize = 40;
    let mut name: String = text
        .chars()
        .take(MAX)
        .flat_map(char::escape_debug)
        .collect();
    if text.chars().nth(MAX).is_some() {
        name.push_str("...");
    }
    name
}

/// Report an indented line right after a directive that takes no metadata
/// (`option`, `include`, `plugin`, `pushtag`, `poptag`, `pushmeta`,
/// `popmeta`), as beancount does (#2813): its grammar has no indented
/// continuation for them, so it reports `syntax error, unexpected INDENT` at
/// the first indented line (metadata, a comment, anything but a blank line)
/// and its recovery swallows the rest of that indented block. rledger's
/// parser absorbed `  kk: 1` into the directive as metadata and the
/// converters ignored it, so the line was dropped with no error.
///
/// Not reported where that line already has a syntax error of its own (an
/// orphan indented line, `  2024-02-30 5`), nor after a directive whose
/// header already has an error: beancount's recovery from that swallows the
/// indented line, which `previous_line_is_a_gap` relies on too. Walks the
/// green root's children and only these directives' tokens, so it costs no
/// red nodes.
fn report_no_metadata_continuations(
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    use rowan::Language as _;
    use rowan::NodeOrToken;
    let bom = bom_offset as usize;
    let mut found: Vec<(usize, usize, &str)> = Vec::new();
    let mut offset = 0usize;
    for child in root.green().children() {
        let len = match child {
            NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        };
        if let NodeOrToken::Node(n) = child {
            let kind = crate::BeancountLanguage::kind_from_raw(n.kind());
            if let Some(&(_, keyword)) = NO_METADATA_DIRECTIVES.iter().find(|(k, _)| *k == kind) {
                // The header's start (its keyword) and the end of the
                // NEWLINE that ends it. A `\n` inside a multi-line string is
                // part of a STRING token, so it does not end the header.
                let mut at = offset;
                let mut header: Option<(usize, &str)> = None;
                let mut header_end = None;
                for token in n.children() {
                    let token_len = match token {
                        NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
                        NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
                    };
                    #[cfg(test)]
                    test_counters::NO_META_SCANNED.with(|c| c.set(c.get() + 1));
                    if let NodeOrToken::Token(t) = token {
                        let k = crate::BeancountLanguage::kind_from_raw(t.kind());
                        if header.is_none() && !is_trivia_kind(k) {
                            header = Some((at, keyword));
                        } else if header.is_some() && k == K::NEWLINE {
                            header_end = Some(at + token_len);
                            break;
                        }
                    }
                    at += token_len;
                }
                if let (Some((start, keyword)), Some(end)) = (header, header_end) {
                    found.push((start, end, keyword));
                }
            }
        }
        offset += len;
    }
    if found.is_empty() {
        return;
    }
    // Sorted starts (BOM frame) of the errors on a header that swallow the
    // indented line after it (`swallows_the_next_line`), and of the syntax
    // errors that already stand for a line.
    #[cfg(test)]
    test_counters::NO_META_SCANNED.with(|c| c.set(c.get() + errors.len()));
    let starts_of = |keep: &dyn Fn(&crate::ParseErrorKind) -> bool| {
        let mut starts: Vec<usize> = errors
            .iter()
            .filter(|e| keep(&e.kind))
            .map(|e| e.span.start)
            .collect();
        starts.sort_unstable();
        starts
    };
    let swallowing = starts_of(&swallows_the_next_line);
    let syntax = starts_of(&|k| matches!(k, crate::ParseErrorKind::SyntaxError(_)));
    let error_in = |starts: &[usize], from: usize, to: usize| {
        let i = starts.partition_point(|&s| s < from + bom);
        starts.get(i).is_some_and(|&s| s < to + bom)
    };
    for (header_start, line_start, keyword) in found {
        let rest = &stripped[line_start..];
        let line = &rest[..rest.find('\n').map_or(rest.len(), |i| i + 1)];
        #[cfg(test)]
        test_counters::NO_META_SCANNED.with(|c| c.set(c.get() + line.len()));
        let body = line.trim_start_matches([' ', '\t']);
        let indented = body.len() < line.len();
        let blank = body.trim_start_matches([' ', '\t', '\r', '\n']).is_empty();
        let line_end = line_start + line.len();
        if !indented
            || blank
            || error_in(&swallowing, header_start, line_start)
            || error_in(&syntax, line_start, line_end)
        {
            continue;
        }
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(format!(
                "unexpected indented line: `{keyword}` takes no metadata"
            )),
            Span::new(line_start + bom, line_end + bom),
        ));
    }
}

/// Whether the transaction `source` starts with holds an invalid token, by
/// the rule the parser itself applies (`holds_an_invalid_token`).
///
/// `source` is a transaction's own text, from its date to the end of its
/// last line, as its directive's span gives it. beancount's grammar never
/// builds such a transaction (its recovery discards the whole statement),
/// while rledger keeps it under error recovery (#2932) with what recovery
/// could read: a posting's price or cost after the token is gone. The
/// validator asks this before it reports a balance residual for a
/// transaction (#2954), so the parser's rule is the only one. `false` when
/// `source` does not start with a transaction.
#[must_use]
pub fn transaction_holds_invalid_token(source: &str) -> bool {
    super::parser::parse_structured(source)
        .children()
        .find(|n| n.kind() == crate::SyntaxKind::TRANSACTION)
        .is_some_and(|n| holds_an_invalid_token(n.green()))
}

/// Whether `node`'s subtree holds an invalid token (`ERROR_TOKEN`), other than
/// BOMs beancount reads into an account (`is_bom_account_token`). A BOM-led
/// run is an invalid token like any other here (#2928).
///
/// `node` is an `open` or a transaction, and a BOM that starts its line
/// ([`is_line_start_bom_token`]) is never in it, so no line-start test is
/// needed: the node's header starts with its date, and every later line it
/// takes in starts with indentation (`is_indented_directive_continuation`,
/// `is_indented_transaction_body_line`), so a line a BOM starts is an
/// `ERROR_NODE` of its own. Walks green nodes only, in source order, so a
/// token of BOMs alone is followed by the token after it.
fn holds_an_invalid_token(node: &rowan::GreenNodeData) -> bool {
    use rowan::Language as _;
    let mut stack = vec![node.children()];
    // A token of BOMs alone, held until the token after it says whether an
    // account of its own follows it (`is_bom_account_token`), which makes it
    // none of beancount's invalid tokens.
    let mut pending_boms: Option<&str> = None;
    while let Some(children) = stack.last_mut() {
        match children.next() {
            None => {
                stack.pop();
            }
            Some(rowan::NodeOrToken::Node(inner)) => stack.push(inner.children()),
            Some(rowan::NodeOrToken::Token(t)) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                if let Some(boms) = pending_boms.take() {
                    let joined = format!("{boms}{}", t.text());
                    if !is_bom_account_token(&joined, 0, boms) {
                        return true;
                    }
                }
                if kind == crate::SyntaxKind::ERROR_TOKEN {
                    let text = t.text();
                    if text.chars().all(|c| c == crate::bom::BOM_CHAR) {
                        pending_boms = Some(text);
                    } else if !is_bom_account_token(text, 0, text) {
                        return true;
                    }
                }
            }
        }
    }
    pending_boms.is_some()
}

/// Report a repeated metadata key on a transaction or a posting, as
/// beancount does (#2893, #2813). Its grammar builds a transaction's and a
/// posting's metadata checking each key against the ones before, and reports
/// a repeat at the transaction's line: `Duplicate metadata field on entry` on
/// the transaction, `Duplicate posting metadata field` on a posting, where
/// `filename` and `lineno` are already set before any written key, so writing
/// either is a repeat too. The first value stands, as the converters keep it
/// (`convert_meta_entries_keeping_first`; a posting's written `filename:` /
/// `lineno:` is dropped there, so its real location stands, as in beancount).
/// Every other directive's metadata takes the last value of a repeated key
/// with no error there, and is left alone; so is a transaction's own
/// `filename:` / `lineno:`.
///
/// A metadata line with an error of its own (`kk: (bad`, `kk: 2024-02-30`,
/// `kk: 1 2`) is no repeat: beancount reports that error and drops the
/// whole entry, so the line never reaches the check. rledger keeps the
/// entry under its error-recovery policy, so only that error is reported. `error_starts` (sorted, BOM frame) holds
/// the errors reported so far; a line holding one is skipped.
///
/// Stricter than Python: beancount checks a repeat with `if value is not
/// posting_or_kv.value` (`grammar.py`, the transaction and posting
/// builders), an OBJECT IDENTITY test, so it stays silent when the repeated
/// value is the identical object: interned values such as `TRUE` / `TRUE`,
/// `""` / `""`, one-character strings, accounts and tags. That is a quirk,
/// not a rule, so every repeat is reported here, whatever its value
/// (maintainer's decision on #2897; pinned by
/// `test_parse_reports_a_repeat_with_an_identical_value_unlike_python`).
///
/// rledger accepted a repeat silently and kept the last value, and a
/// posting's written `filename:` / `lineno:` stood in for its real location.
///
/// A transaction with an invalid token anywhere in it is not checked at all:
/// beancount's grammar never builds it (its recovery discards the whole
/// statement), so the token is its only error there (#2872).
///
/// Walks the green tree, only the transactions' children, so it costs no red
/// nodes; each key is looked up in the keys before it on its owner, pairwise
/// for a handful and through a set past that, so it stays near-linear.
fn report_duplicate_metadata(
    root: &crate::SyntaxNode,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    use rowan::Language as _;
    use rowan::NodeOrToken;
    fn len_of(child: NodeOrToken<&rowan::GreenNodeData, &rowan::GreenTokenData>) -> usize {
        match child {
            NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        }
    }
    /// The key of a `META_ENTRY` node, without its colon.
    fn meta_key(meta: &rowan::GreenNodeData) -> Option<&str> {
        meta.children().find_map(|t| match t {
            NodeOrToken::Token(t)
                if crate::BeancountLanguage::kind_from_raw(t.kind()) == K::META_KEY =>
            {
                Some(t.text().trim_end_matches(':'))
            }
            _ => None,
        })
    }
    /// The repeated keys among the `META_ENTRY` children of `owner` (which
    /// starts at `base`, stripped frame), in order, counting `preset` as
    /// written before them and skipping a line `has_error` reports.
    fn repeats<'a>(
        owner: &'a rowan::GreenNodeData,
        base: usize,
        preset: &[&'a str],
        has_error: &dyn Fn(usize, usize) -> bool,
    ) -> Vec<&'a str> {
        const PAIRWISE: usize = 16;
        let mut seen: Vec<&str> = preset.to_vec();
        let mut index: Option<std::collections::HashSet<&str>> = None;
        let mut out = Vec::new();
        let mut at = base;
        for child in owner.children() {
            let start = at;
            at += len_of(child);
            let NodeOrToken::Node(meta) = child else {
                continue;
            };
            if crate::BeancountLanguage::kind_from_raw(meta.kind()) != K::META_ENTRY
                || has_error(start, at)
            {
                continue;
            }
            let Some(key) = meta_key(meta) else {
                continue;
            };
            let repeated = if let Some(set) = &mut index {
                !set.insert(key)
            } else {
                #[cfg(test)]
                test_counters::DUP_META_COMPARED.with(|c| c.set(c.get() + seen.len()));
                let repeated = seen.contains(&key);
                if !repeated {
                    seen.push(key);
                    if seen.len() > PAIRWISE {
                        index = Some(std::mem::take(&mut seen).into_iter().collect());
                    }
                }
                repeated
            };
            if repeated {
                out.push(key);
            }
        }
        out
    }
    let bom = bom_offset as usize;
    let mut starts: Vec<usize> = errors.iter().map(|e| e.span.start).collect();
    starts.sort_unstable();
    let has_error = |from: usize, to: usize| {
        let i = starts.partition_point(|&s| s < from + bom);
        starts.get(i).is_some_and(|&s| s < to + bom)
    };
    let mut found: Vec<(usize, usize, String)> = Vec::new();
    let mut offset = 0usize;
    for child in root.green().children() {
        let len = len_of(child);
        if let NodeOrToken::Node(txn) = child
            && crate::BeancountLanguage::kind_from_raw(txn.kind()) == K::TRANSACTION
            && !holds_an_invalid_token(txn)
        {
            // The header line: from the first non-trivia token to the end of
            // its NEWLINE.
            let mut header: Option<usize> = None;
            let mut header_end: Option<usize> = None;
            let mut messages: Vec<String> = repeats(txn, offset, &[], &has_error)
                .into_iter()
                .map(|key| format!("duplicate metadata field on entry: `{key}`"))
                .collect();
            let mut at = offset;
            for part in txn.children() {
                let part_len = len_of(part);
                match part {
                    NodeOrToken::Token(t) => {
                        let k = crate::BeancountLanguage::kind_from_raw(t.kind());
                        if header.is_none() && !is_trivia_kind(k) {
                            header = Some(at);
                        } else if header.is_some() && header_end.is_none() && k == K::NEWLINE {
                            header_end = Some(at + part_len);
                        }
                    }
                    NodeOrToken::Node(posting)
                        if crate::BeancountLanguage::kind_from_raw(posting.kind())
                            == K::POSTING =>
                    {
                        for key in repeats(posting, at, &POSTING_LOCATION_KEYS, &has_error) {
                            messages.push(if matches!(key, "filename" | "lineno") {
                                format!(
                                    "duplicate posting metadata field `{key}`: beancount \
                                     sets `filename` and `lineno` on every posting itself"
                                )
                            } else {
                                format!("duplicate posting metadata field: `{key}`")
                            });
                        }
                    }
                    NodeOrToken::Node(_) => {}
                }
                at += part_len;
            }
            if let (Some(start), false) = (header, messages.is_empty()) {
                let end = header_end.unwrap_or(offset + len);
                for message in messages {
                    found.push((start, end, message));
                }
            }
        }
        offset += len;
    }
    for (start, end, message) in found {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(message),
            Span::new(start + bom, end + bom),
        ));
    }
}

/// Name a misspelled boolean (#2813): beancount's only boolean spellings are
/// `TRUE` and `FALSE`, so `true`, `false`, `True` and `False` are its
/// `Invalid token`, and a parse error here too. The generic `unexpected input`
/// on such a word becomes `invalid token 'true' (booleans are written TRUE or
/// FALSE)`, so the fix is in the message.
///
/// The word is read from the source around the error: the ASCII letters on
/// both sides, at most one more than the five of `false`, so `Truex` is left
/// alone and a long word costs nothing. It is renamed only when it stands alone as a
/// value: a line start or whitespace before it, and whitespace, a line end or
/// the end of the source after it (a glued `;` is part of the invalid token,
/// as in beancount: `true;c` is named whole). Anything else around it
/// (`Assets:true`, `true.`, `True'`, `trueé`) makes it part of a longer token,
/// which beancount names whole, so the generic message stays.
fn name_misspelled_booleans(errors: &mut [crate::ParseError], stripped: &str, bom_offset: u32) {
    const LIMIT: usize = 5;
    let bom = bom_offset as usize;
    let bytes = stripped.as_bytes();
    for e in errors.iter_mut() {
        if !matches!(&e.kind, crate::ParseErrorKind::SyntaxError(m) if m == "unexpected input") {
            continue;
        }
        let (Some(start), Some(end)) = (e.span.start.checked_sub(bom), e.span.end.checked_sub(bom))
        else {
            continue;
        };
        if end > bytes.len() || start >= end || end - start > LIMIT {
            continue;
        }
        let is_letter = |i: usize| bytes.get(i).is_some_and(u8::is_ascii_alphabetic);
        // At most `LIMIT + 1` letters in all: enough to tell a five-letter
        // boolean from a longer word.
        let mut from = start;
        while from > 0 && end - from <= LIMIT && is_letter(from - 1) {
            from -= 1;
        }
        let mut to = end;
        while to - from <= LIMIT && is_letter(to) {
            to += 1;
        }
        let before_ok = from == 0 || matches!(bytes[from - 1], b' ' | b'\t' | b'\n');
        let after_ok = bytes
            .get(to)
            .is_none_or(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n' | b';'));
        let word = &stripped[from..to];
        if before_ok && after_ok && matches!(word, "true" | "false" | "True" | "False") {
            e.kind = crate::ParseErrorKind::SyntaxError(format!(
                "invalid token '{word}' (booleans are written TRUE or FALSE)"
            ));
        }
    }
}

/// Name a mid-line `#!` or `#+` in the error its line gets (#2928).
///
/// Only at column 0 does beancount skip a `#` line; anywhere else, indented
/// too, `#!` and `#+` are a `#` and a `!` or `+`, which its grammar has no
/// place for, so the lexer reads them as those tokens. The line's error is
/// then the generic `unexpected input`, at the line's start for an indented
/// line, which does not name the comment the writer most likely meant (an org-mode
/// `  #+STARTUP` line, a `#!` note after a posting). Where the marker leads
/// its line, this rewrites that error, the first on the line at or before the
/// `#` (only blanks lie between, so the list stays sorted), to point at the
/// `#!` / `#+` and say that only `;` starts a comment there. A defect
/// already reported at the `#` itself (a directive header's or a
/// posting's) is widened to the two characters and given the same hint;
/// after another token, an error before the `#` is that token's and is left
/// alone. Only the message and span move: every error is still there, on its
/// line, so the counts stay beancount's.
///
/// Shared by both parse paths, keyed on the source text and the error list;
/// the markers are found by the lexer itself, so a `#!` in a string or a
/// comment is none.
fn name_mid_line_hash_comments(errors: &mut [crate::ParseError], stripped: &str, bom_offset: u32) {
    use crate::logos_lexer::{Token, TokenIter};
    if !stripped.contains("#!") && !stripped.contains("#+") {
        return;
    }
    let bom = bom_offset as usize;
    let mut markers = Vec::new();
    let mut prev_hash: Option<usize> = None;
    for (token, span) in TokenIter::new(stripped, true) {
        if let Some(at) = prev_hash.take()
            && span.start == at + 1
            && matches!(token, Token::Pending | Token::Plus)
        {
            markers.push(at);
        }
        if matches!(token, Token::Hash) {
            prev_hash = Some(span.start);
        }
    }
    for at in markers {
        let marker = &stripped[at..at + 2];
        let line_start = stripped[..at].rfind('\n').map_or(0, |i| i + 1);
        // Only a marker that leads its line (after its indentation) stands
        // for the line's whole error. After another token, an error before
        // the `#` is that token's (`$x #+y`, a stray `\r`), and only one the
        // line reports at the `#` itself is the marker's.
        let leads = stripped[line_start..at]
            .trim_start_matches([' ', '\t'])
            .is_empty();
        let Some(e) = errors.iter_mut().find(|e| {
            e.span.start.checked_sub(bom).is_some_and(|s| {
                if leads {
                    (line_start..=at).contains(&s)
                } else {
                    s == at
                }
            })
        }) else {
            continue;
        };
        let crate::ParseErrorKind::SyntaxError(msg) = &e.kind else {
            continue;
        };
        let hint = format!(
            "only `;` starts a comment that is indented or in the middle of a line; \
             `{marker}` starts one only at the beginning of a line"
        );
        let message = if msg == "unexpected input" {
            format!("unexpected {marker:?}: {hint}")
        } else if e.span.start == at + bom
            && let Some(rest) = msg.strip_prefix("unexpected \"#\"")
        {
            let rest = rest.replace("`#` starts one", &format!("`{marker}` starts one"));
            if rest.contains("starts a comment") {
                format!("unexpected {marker:?}{rest}")
            } else {
                format!("unexpected {marker:?}{rest}: {hint}")
            }
        } else {
            continue;
        };
        e.kind = crate::ParseErrorKind::SyntaxError(message);
        e.span = Span::new(at + bom, at + 2 + bom);
    }
}

/// Name the problem when an unlexable character is glued to the end of a
/// currency (`CAC_`, `HOOL'`, `USD.`).
///
/// A currency ends with a letter or digit, as in beancount (#2802), so the
/// trailing `_`, `'` or `.` is left over as an `ERROR_TOKEN`, whose generic
/// message is `unexpected input`. Shared by both parse paths: it rewrites the
/// message of an error both walkers already produced, keyed only on the source
/// text.
fn name_a_currency_tail(
    err: crate::ParseError,
    stripped: &str,
    bom_offset: u32,
) -> crate::ParseError {
    let crate::ParseErrorKind::SyntaxError(msg) = &err.kind else {
        return err;
    };
    if msg != "unexpected input" {
        return err;
    }
    let Some(start) = err.span.start.checked_sub(bom_offset as usize) else {
        return err;
    };
    let Some(tail @ ('_' | '\'' | '.')) = stripped.get(start..).and_then(|s| s.chars().next())
    else {
        return err;
    };
    let before = &stripped[..start];
    // `char_indices`, not `rfind + 1`: the character before the word may be
    // multibyte, and slicing inside it would panic.
    let stop = before
        .char_indices()
        .rev()
        .find(|&(_, c)| !(c.is_ascii_alphanumeric() || "'._-/".contains(c)));
    // A currency is ASCII, so a word glued to a non-ASCII character (`ÜSD_`) is
    // not one; naming the ASCII fragment after it (`SD`) would mislead.
    if stop.is_some_and(|(_, c)| !c.is_ascii()) {
        return err;
    }
    let word_start = stop.map_or(0, |(i, c)| i + c.len_utf8());
    let word = &before[word_start..];
    // After a `:` it is the end of an account segment, not a currency.
    if word.is_empty() || before[..word_start].ends_with(':') || !crate::is_valid_currency(word) {
        return err;
    }
    crate::ParseError {
        kind: crate::ParseErrorKind::SyntaxError(format!(
            "unexpected `{tail}` after the currency `{word}`: a currency cannot end in `{tail}`"
        )),
        ..err
    }
}
