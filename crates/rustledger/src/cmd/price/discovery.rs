//! Symbol discovery from beancount files.
//!
//! Walks a loaded ledger to identify which commodities to fetch prices for.
//! The default (strict) mode is verified against upstream
//! `beanprice/price.py::find_currencies_declared`:
//!
//! - `commodity` directives carrying a `price:` metadata key drive
//!   metadata-based discovery. Format: `"<quote>:<source>/<ticker>"`,
//!   optionally chained with `,` for fallback alternatives, e.g.
//!   `"USD:yahoo/AAPL,USD:google/NASDAQ:AAPL"`.
//! - `quote_currency:` metadata supplies a per-commodity quote currency,
//!   used as the `--currency` default for that one symbol. (This is a
//!   permissive extension over bean-price, which only treats `price:` as
//!   a discovery trigger; `quote_currency:` alone is enough here.)
//! - `price: ""` (empty/whitespace) explicitly opts a commodity *out* of
//!   fetching, even if it would otherwise be picked up. Mirrors
//!   `bean-price`'s "Skipping ignored currency (with empty price)" rule.
//!
//! By default, only "active" commodities are returned: those with a non-zero
//! balance in at least one open balance-sheet account. Set `inactive: true`
//! to skip the activity filter — corresponds to `bean-price --inactive`.
//!
//! ## `undeclared` divergence
//!
//! Setting `undeclared: true` re-enables a ticker-shape heuristic for
//! `commodity` directives that lack metadata (uppercase letters / digits /
//! dashes / dots, ≤ 10 chars). This is **not** a 1:1 match for
//! `bean-price --undeclared`, which instead unions the at-cost, converted,
//! and priced currencies *seen in transactions* with no name filtering.
//! Our heuristic is a strict subset chosen deliberately so that currency
//! codes like `EUR` or `BAM` aren't auto-routed to a stock source and
//! produce wrong prices (issue #962). Closer alignment with bean-price's
//! transaction-walking semantics is tracked in the audit issue.

use crate::config::{CommodityMapping, DetailedMapping, FallbackDetail, FallbackEntry, SourceRef};
use rust_decimal::Decimal;
use rustledger_core::{Directive, MetaValue, NaiveDate};
use rustledger_loader::Options;
use rustledger_parser::Spanned;
use std::collections::{HashMap, HashSet};

/// One declared `(quote_currency, mapping)` pair for a commodity.
///
/// A commodity with `price: "USD:yahoo/AAPL CAD:google/AAPL"` produces two
/// `QuoteSpec` entries — bean-price emits one fetch job per `(base, quote)`
/// pair and rledger now matches that.
#[derive(Debug, Clone)]
pub struct QuoteSpec {
    /// Quote currency for this fetch job (e.g. `USD`, `CAD`).
    pub quote_currency: String,
    /// `None` for `quote_currency:`-only discovery — source/ticker comes
    /// from config, CLI args, or `[price.default_source]` downstream.
    pub mapping: Option<CommodityMapping>,
}

/// What the discovery pass produces for a single commodity symbol.
///
/// `mapping` and `quote_currency` mirror the FIRST entry of `quote_specs`
/// (kept for back-compat with code paths that fetch only one quote per
/// symbol). When `quote_specs.len() > 1`, callers that want full
/// multi-currency support should iterate `quote_specs`.
#[derive(Debug, Clone, Default)]
pub struct DiscoveredCommodity {
    /// First spec's mapping. `None` when discovery was driven by
    /// `quote_currency:` metadata alone, by the `--undeclared`
    /// ticker-shape heuristic, or by a CLI-supplied symbol.
    pub mapping: Option<CommodityMapping>,
    /// First spec's quote currency. `None` when only the heuristic fired.
    pub quote_currency: Option<String>,
    /// All declared `(quote_currency, mapping)` pairs. Empty for
    /// commodities discovered only via the `--undeclared` heuristic.
    /// When non-empty, the first entry mirrors
    /// `(quote_currency, mapping)` above.
    pub quote_specs: Vec<QuoteSpec>,
}

/// One parsed entry from a `price:` metadata string.
#[derive(Debug, Clone, PartialEq, Eq)]
struct PriceSpec {
    quote_currency: String,
    source: String,
    ticker: String,
}

/// Discover the set of commodities to fetch prices for from a loaded ledger.
///
/// Returns a map from commodity symbol to discovery info, covering only
/// commodities present in the ledger that meet the discovery criteria.
/// CLI-supplied symbols are intentionally NOT injected here — the caller
/// handles them separately so that explicit `rledger price BAM`
/// invocations hit the explicit-source-required check (#966) instead of
/// the auto-synthesized default-source mapping that file-discovered
/// commodities get.
///
/// `inactive` corresponds to `bean-price --inactive`: when false (the
/// default), only commodities with a non-zero balance on at least one open
/// balance-sheet account are returned.
///
/// `undeclared` corresponds to `bean-price --undeclared`: when false (the
/// default), only commodities with `price:` or `quote_currency:` metadata
/// are returned. With `undeclared = true`, commodities whose name looks
/// like a ticker symbol are also picked up using configured/default
/// sources.
///
/// Takes the directive slice directly so it works with either `LoadResult`
/// (raw load) or the post-processing `Ledger` type without coupling. Reads
/// the configured account-type names from `options` so the
/// active-commodity check works on ledgers using non-English account
/// roots (e.g., `Activos:` instead of `Assets:`).
pub fn discover_symbols(
    directives: &[Spanned<Directive>],
    options: &Options,
    inactive: bool,
    undeclared: bool,
    as_of: Option<NaiveDate>,
) -> HashMap<String, DiscoveredCommodity> {
    let active = if inactive {
        None
    } else {
        Some(active_commodities(directives, options, as_of))
    };

    let mut out: HashMap<String, DiscoveredCommodity> = HashMap::new();

    // Track which symbols already had a Commodity directive walk so the
    // transaction-walking pass below doesn't duplicate them.
    let mut seen_commodity_decl: HashSet<String> = HashSet::new();

    for spanned in directives {
        let Directive::Commodity(comm) = &spanned.value else {
            continue;
        };
        // Match bean-price's `find_currencies_declared`: a commodity declared
        // ON OR AFTER the as-of date is excluded from historical discovery.
        // (Beanprice uses `entry.date >= date: break` since its directive list
        // is date-sorted; we use `continue` because our slice may not be.)
        if let Some(cutoff) = as_of
            && comm.date >= cutoff
        {
            continue;
        }
        let symbol = comm.currency.as_str();
        seen_commodity_decl.insert(symbol.to_string());

        let classification = classify_commodity_meta(&comm.meta);

        // Warn on a non-empty `price:` value that didn't yield any usable
        // specs — almost always a typo. Matches `bean-price`, which logs
        // "Ignoring currency with invalid 'price' source" for the same
        // case. We still skip the commodity (no source to fetch from);
        // the warning surfaces the misconfiguration.
        if classification.malformed_price {
            eprintln!(
                "warning: commodity {symbol} has malformed `price:` metadata; \
                 expected `<quote>:<source>/<ticker>` (e.g. `USD:yahoo/AAPL`). Skipping."
            );
        }

        let info = match classification.decision {
            // `price: ""` (or whitespace) is an explicit opt-out, honored
            // regardless of `undeclared` so users can suppress commodities
            // that would otherwise be picked up by the heuristic.
            DiscoveryDecision::OptOut => continue,
            DiscoveryDecision::Discovered(info) => info,
            // No metadata: only include if `--undeclared` is set AND the
            // commodity name looks like a ticker symbol. This is a strict
            // subset of `bean-price --undeclared` (see module docs for the
            // rationale).
            DiscoveryDecision::Inherit => {
                if !(undeclared && looks_like_ticker(symbol)) {
                    continue;
                }
                DiscoveredCommodity::default()
            }
        };

        // Skip inactive commodities unless the user opted in.
        if let Some(ref active_set) = active
            && !active_set.contains(symbol)
        {
            continue;
        }

        out.insert(symbol.to_string(), info);
    }

    // Bean-price compat for `--undeclared`: also walk transactions and pick
    // up commodities that appear in postings (units, at-cost currency, @
    // price annotation currency) but lack their own `commodity` directive.
    // This brings rledger closer to bean-price's transaction-walking
    // semantics. Note `looks_like_ticker` only filters out *non-ticker-shaped*
    // names (lowercase, > 10 chars) — 3-letter uppercase codes like `EUR`
    // or `BAM` DO pass the heuristic and will be picked up here. The #962
    // protection isn't this filter; it's that the strict DEFAULT requires
    // `price:` metadata. Opting into `--undeclared` is opting into the
    // shape-only filter, which has known false positives for currency codes.
    if undeclared {
        let txn_symbols = transaction_walked_currencies(directives, as_of);
        for symbol in txn_symbols {
            if seen_commodity_decl.contains(&symbol) {
                continue;
            }
            if !looks_like_ticker(&symbol) {
                continue;
            }
            if let Some(ref active_set) = active
                && !active_set.contains(&symbol)
            {
                continue;
            }
            out.entry(symbol).or_default();
        }
    }

    out
}

/// Currencies referenced from any posting in any transaction strictly before
/// `as_of`. Includes the units currency, the at-cost currency, and the `@`
/// price annotation currency. Matches bean-price's transaction-walking pass
/// for `--undeclared` (which uses `entry.date >= date: break`); the caller
/// applies `looks_like_ticker`, which rejects only lowercase / > 10-char
/// names — 3-letter uppercase codes like `EUR`, `USD`, `BAM` still pass.
/// The #962 protection isn't this filter; it's that the strict default
/// (no `--undeclared`) requires `price:` metadata.
///
/// The strict-less-than convention also matches the commodity-walk above
/// (line 138) and `find_currencies_declared` in upstream beanprice. Note
/// `active_commodities` further down uses inclusive `<=` for its own
/// reasons (active-balance is "as of end of `as_of`"); the discovery walks
/// here use exclusive bounds so the two cutoff conventions don't drift
/// out of sync with bean-price.
fn transaction_walked_currencies(
    directives: &[Spanned<Directive>],
    as_of: Option<NaiveDate>,
) -> HashSet<String> {
    let in_window = |d: NaiveDate| as_of.is_none_or(|cutoff| d < cutoff);
    let mut out = HashSet::new();
    for spanned in directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };
        if !in_window(txn.date) {
            continue;
        }
        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                out.insert(amount.currency.to_string());
            }
            if let Some(cost) = &posting.cost
                && let Some(c) = &cost.currency
            {
                out.insert(c.to_string());
            }
            if let Some(price) = &posting.price
                && let Some(amount) = price.amount()
            {
                out.insert(amount.currency.to_string());
            }
        }
    }
    out
}

/// Outcome of inspecting one `commodity` directive's metadata.
enum DiscoveryDecision {
    /// `price: ""` (or whitespace-only) — user explicitly opted this
    /// commodity out of fetching.
    OptOut,
    /// `price:` and/or `quote_currency:` metadata is present.
    Discovered(DiscoveredCommodity),
    /// No relevant metadata. Whether to include depends on `undeclared`
    /// and the name heuristic.
    Inherit,
}

/// Result of classifying a commodity, plus a flag for whether the
/// commodity had a non-empty `price:` value that didn't parse (typo /
/// misconfig). The caller surfaces this as a warning.
struct Classification {
    decision: DiscoveryDecision,
    malformed_price: bool,
}

/// Classify a commodity by its metadata in a single pass over the map.
fn classify_commodity_meta(meta: &rustledger_core::Metadata) -> Classification {
    let price_raw = meta.get("price").and_then(metavalue_as_str);

    // Empty or whitespace-only `price:` is the explicit opt-out marker.
    if let Some(p) = price_raw
        && p.trim().is_empty()
    {
        return Classification {
            decision: DiscoveryDecision::OptOut,
            malformed_price: false,
        };
    }

    let price_specs = price_raw.map(parse_price_metadata).unwrap_or_default();
    // A non-empty `price:` that produces zero parsed specs is malformed.
    // We still return `Inherit`/`Discovered` based on other signals; the
    // caller logs a warning.
    let malformed_price = price_raw.is_some_and(|s| !s.trim().is_empty()) && price_specs.is_empty();

    let quote_currency_meta = meta.get("quote_currency").and_then(|v| match v {
        MetaValue::String(s) | MetaValue::Currency(s) => Some(s.clone()),
        _ => None,
    });

    // Group price_specs by quote currency, preserving first-seen order.
    // Each group becomes one QuoteSpec; multi-currency `price:` metadata
    // (e.g. `USD:yahoo/AAPL CAD:google/AAPL`) yields multiple specs.
    let mut quote_specs: Vec<QuoteSpec> = Vec::new();
    for spec in &price_specs {
        if let Some(existing) = quote_specs
            .iter_mut()
            .find(|qs| qs.quote_currency == spec.quote_currency)
        {
            // Same quote currency, additional source — fold into existing
            // mapping by rebuilding from all specs that share this quote.
            let same_quote: Vec<PriceSpec> = price_specs
                .iter()
                .filter(|s| s.quote_currency == existing.quote_currency)
                .cloned()
                .collect();
            existing.mapping = build_mapping(&same_quote);
        } else {
            let same_quote: Vec<PriceSpec> = price_specs
                .iter()
                .filter(|s| s.quote_currency == spec.quote_currency)
                .cloned()
                .collect();
            quote_specs.push(QuoteSpec {
                quote_currency: spec.quote_currency.clone(),
                mapping: build_mapping(&same_quote),
            });
        }
    }
    // `quote_currency:` metadata adds a single spec when `price:` didn't
    // already cover it (the metadata is a backstop, not an additional fetch).
    if quote_specs.is_empty()
        && let Some(qc) = &quote_currency_meta
    {
        quote_specs.push(QuoteSpec {
            quote_currency: qc.clone(),
            mapping: None,
        });
    }

    let first_mapping = quote_specs.first().and_then(|qs| qs.mapping.clone());
    let first_quote = quote_specs.first().map(|qs| qs.quote_currency.clone());

    let info = DiscoveredCommodity {
        mapping: first_mapping,
        quote_currency: first_quote,
        quote_specs,
    };

    let decision = if info.mapping.is_some() || info.quote_currency.is_some() {
        DiscoveryDecision::Discovered(info)
    } else {
        DiscoveryDecision::Inherit
    };

    Classification {
        decision,
        malformed_price,
    }
}

/// Convert parsed `PriceSpec` entries into the existing `CommodityMapping`
/// shape so the rest of the price pipeline doesn't need new branches.
fn build_mapping(specs: &[PriceSpec]) -> Option<CommodityMapping> {
    if specs.is_empty() {
        return None;
    }
    if specs.len() == 1 {
        let s = &specs[0];
        return Some(CommodityMapping::Detailed(DetailedMapping {
            source: SourceRef::Single(s.source.clone()),
            ticker: Some(s.ticker.clone()),
            quote_currency: None,
        }));
    }
    // Multiple specs: build a fallback chain that PRESERVES each spec's
    // ticker. Issue #963: previously we collapsed all sources onto the
    // first spec's ticker, which broke metadata like
    // `price: "EUR:ecbrates/GBP-EUR,EUR:ecb/GBP"` — the ECB source got
    // queried with `GBP-EUR` (ecbrates' shape) instead of `GBP`.
    //
    // Dedup by `(source, ticker)` to suppress accidental duplicate entries
    // from typos like `"USD:yahoo/AAPL,USD:yahoo/AAPL"` — without this,
    // the runtime would re-invoke yahoo on the first attempt's failure
    // and the dry-run would print the same source twice. First occurrence
    // wins (preserves order, which is significant for fallback semantics).
    let mut seen: HashSet<(String, String)> = HashSet::new();
    let entries: Vec<FallbackEntry> = specs
        .iter()
        .filter(|s| seen.insert((s.source.clone(), s.ticker.clone())))
        .map(|s| {
            FallbackEntry::Detailed(FallbackDetail {
                source: s.source.clone(),
                ticker: Some(s.ticker.clone()),
            })
        })
        .collect();
    // After dedup, a single-entry chain collapses to Single (matches what
    // the earlier `specs.len() == 1` short-circuit would have produced).
    if entries.len() == 1
        && let FallbackEntry::Detailed(d) = &entries[0]
    {
        return Some(CommodityMapping::Detailed(DetailedMapping {
            source: SourceRef::Single(d.source.clone()),
            ticker: d.ticker.clone(),
            quote_currency: None,
        }));
    }
    Some(CommodityMapping::Detailed(DetailedMapping {
        source: SourceRef::Fallback(entries),
        // The parent ticker is no longer load-bearing for fallback chains
        // (each entry carries its own), but keep the first spec's ticker
        // here as a sensible fallback if a future change ever consults
        // `parent.ticker` directly.
        ticker: Some(specs[0].ticker.clone()),
        quote_currency: None,
    }))
}

/// Parse a `price:` metadata value into one or more specs.
///
/// Parses both rledger's and `bean-price`'s `price:` metadata syntaxes.
///
/// **bean-price form**: `<curr1>:<src1>,<src2>,...  <curr2>:<src1>,...`
/// where currency blocks are separated by whitespace or `;`, and within
/// each block sources are comma-separated, each as `<source>/<ticker>`.
///
/// **rledger form** (per #963/#970): `<curr>:<src>/<ticker>,<curr>:<src>/<ticker>,...`
/// where each comma-separated entry repeats the currency.
///
/// The two are disambiguated per source-entry: if the part before the
/// first `/` contains `:`, the entry is rledger's redundant form and
/// supplies its own currency; otherwise it inherits the block's currency.
/// That handles both natively without a mode flag and lets users mix the
/// styles in one metadata string.
///
/// Examples (all valid):
///   `"USD:yahoo/AAPL"`                               (single)
///   `"USD:yahoo/AAPL,google/AAPL"`                   (bean-price multi-source)
///   `"USD:yahoo/AAPL,USD:google/AAPL"`               (rledger redundant form)
///   `"EUR:ecbrates/GBP-EUR,ecb/GBP"`                 (bean-price chain)
///   `"USD:yahoo/AAPL CAD:google/AAPL"`               (bean-price multi-currency)
///   `"USD:google/NASDAQ:AAPL"`                       (ticker contains `:`, fine)
///
/// Malformed entries are silently skipped — matches bean-price's lenient
/// parsing (it logs a warning and continues; we already surface a malformed
/// warning at the caller, see `classify_commodity_meta`).
fn parse_price_metadata(raw: &str) -> Vec<PriceSpec> {
    let mut specs = Vec::new();
    // First split on whitespace/semicolons → currency blocks (bean-price multi-currency form).
    for block in raw.split([' ', '\t', ';']) {
        let block = block.trim();
        if block.is_empty() {
            continue;
        }
        let Some((block_quote, sources_str)) = block.split_once(':') else {
            continue;
        };
        let block_quote = block_quote.trim();
        if block_quote.is_empty() {
            continue;
        }
        // Then split on `,` → sources within the currency block. Each
        // source is either bean-price's bare `<source>/<ticker>` (inherits
        // block currency) or rledger's redundant `<curr>:<source>/<ticker>`
        // (overrides block currency). Disambiguate by whether the part
        // before the first `/` contains a `:` — `:` AFTER the slash is
        // part of the ticker, not a currency prefix.
        for entry in sources_str.split(',') {
            let entry = entry.trim();
            if entry.is_empty() {
                continue;
            }
            let Some((before_slash, ticker)) = entry.split_once('/') else {
                continue;
            };
            let (effective_quote, source) = if let Some((q, src)) = before_slash.split_once(':') {
                (q.trim(), src.trim())
            } else {
                (block_quote, before_slash.trim())
            };
            let ticker = ticker.trim();
            if effective_quote.is_empty() || source.is_empty() || ticker.is_empty() {
                continue;
            }
            specs.push(PriceSpec {
                quote_currency: effective_quote.to_string(),
                source: source.to_string(),
                ticker: ticker.to_string(),
            });
        }
    }
    specs
}

const fn metavalue_as_str(v: &MetaValue) -> Option<&str> {
    match v {
        MetaValue::String(s) | MetaValue::Currency(s) => Some(s.as_str()),
        _ => None,
    }
}

/// Heuristic preserved for backward compat: a name is "ticker-shaped" if it's
/// uppercase ASCII letters, digits, dashes, or dots, length ≤ 10. The dot
/// allowance handles common exchange-suffixed tickers like `VECP.AS`,
/// `BRK.B`, or `7203.T` (issue #952). Beancount itself permits dots in
/// commodity names; the heuristic was previously stricter than the parser.
///
/// Intentionally permissive about the leading character (`7203.T` legitimately
/// starts with a digit). False positives like `..` are accepted because the
/// downstream price fetch will fail loudly for nonsense names — there's no
/// gain to encoding stricter validation here than the parser already does.
fn looks_like_ticker(symbol: &str) -> bool {
    !symbol.is_empty()
        && symbol.len() <= 10
        && symbol
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-' || c == '.')
}

/// Compute the set of commodity codes that have a non-zero balance in at
/// least one open balance-sheet (Assets or Liabilities) account.
///
/// Restricting to balance-sheet accounts is the correct definition of
/// "currently held": Equity accounts (e.g. `Equity:Opening-Balances`)
/// retain inverse balances of every commodity that ever moved through the
/// ledger, so including them would mark long-closed positions as active.
/// Income and Expenses are never holdings.
///
/// The "Assets" / "Liabilities" prefix is read from `options` so ledgers
/// using translated account roots (`Activos`, `Aktiva`, etc.) work too.
fn active_commodities(
    directives: &[Spanned<Directive>],
    options: &Options,
    as_of: Option<NaiveDate>,
) -> HashSet<String> {
    let assets_prefix = format!("{}:", options.name_assets);
    let liabilities_prefix = format!("{}:", options.name_liabilities);
    let is_balance_sheet = |account: &str| {
        account.starts_with(&assets_prefix) || account.starts_with(&liabilities_prefix)
    };
    // Match bean-price's file-as-of-date semantics: with --date, both balance
    // computation and account-close handling reflect the state on that date,
    // not the latest. A commodity held on `as_of` but liquidated since then
    // should still be considered active for the historical fetch.
    let in_window = |date: NaiveDate| as_of.is_none_or(|cutoff| date <= cutoff);

    let mut balances: HashMap<(String, String), Decimal> = HashMap::new();
    let mut closed: HashSet<String> = HashSet::new();

    for spanned in directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                if !in_window(txn.date) {
                    continue;
                }
                for posting in &txn.postings {
                    let account = posting.account.as_str();
                    if !is_balance_sheet(account) {
                        continue;
                    }
                    if let Some(amount) = posting.amount() {
                        let key = (account.to_string(), amount.currency.to_string());
                        *balances.entry(key).or_default() += amount.number;
                    }
                }
            }
            Directive::Close(close) => {
                if !in_window(close.date) {
                    continue;
                }
                closed.insert(close.account.to_string());
            }
            _ => {}
        }
    }

    let mut active: HashSet<String> = HashSet::new();
    for ((account, currency), amount) in &balances {
        if !amount.is_zero() && !closed.contains(account) {
            active.insert(currency.clone());
        }
    }
    active
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Close, Commodity, NaiveDate, Open, Posting, Transaction};
    use rustledger_parser::Span;

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        rustledger_core::naive_date(y, m, d).unwrap()
    }

    fn directives(items: Vec<Directive>) -> Vec<Spanned<Directive>> {
        items
            .into_iter()
            .map(|d| Spanned::new(d, Span::new(0, 0)))
            .collect()
    }

    #[test]
    fn parses_single_price_spec() {
        let specs = parse_price_metadata("USD:yahoo/AAPL");
        assert_eq!(
            specs,
            vec![PriceSpec {
                quote_currency: "USD".into(),
                source: "yahoo".into(),
                ticker: "AAPL".into(),
            }]
        );
    }

    #[test]
    fn parses_chained_price_specs() {
        let specs = parse_price_metadata("USD:yahoo/AAPL, USD:google/NASDAQ:AAPL");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].source, "yahoo");
        assert_eq!(specs[1].source, "google");
        // Ticker preserves embedded colons after the first / split.
        assert_eq!(specs[1].ticker, "NASDAQ:AAPL");
    }

    #[test]
    fn build_mapping_dedups_identical_fallback_entries() {
        // User typo: `"USD:yahoo/AAPL,USD:yahoo/AAPL"`. Without dedup, the
        // runtime would re-invoke yahoo on the first attempt's failure and
        // the dry-run would print yahoo twice. After dedup the chain
        // collapses to a Single mapping (one entry).
        let specs = parse_price_metadata("USD:yahoo/AAPL,USD:yahoo/AAPL");
        assert_eq!(specs.len(), 2, "parser preserves duplicates as written");
        let m = build_mapping(&specs).expect("mapping should be built");
        match m {
            CommodityMapping::Detailed(d) => match d.source {
                SourceRef::Single(s) => assert_eq!(s, "yahoo"),
                SourceRef::Fallback(entries) => {
                    panic!("duplicates should collapse to Single, got Fallback({entries:?})")
                }
            },
            CommodityMapping::Simple(_) => panic!("expected Detailed mapping"),
        }
    }

    #[test]
    fn build_mapping_dedups_in_fallback_chain_preserves_distinct_entries() {
        // Mixed: yahoo,ecb,yahoo — dedup drops the second yahoo, keeping
        // the original first-seen order [yahoo, ecb]. Fallback semantics
        // depend on order.
        let specs = parse_price_metadata("USD:yahoo/AAPL,USD:ecb/AAPL,USD:yahoo/AAPL");
        assert_eq!(specs.len(), 3);
        let m = build_mapping(&specs).expect("mapping should be built");
        match m {
            CommodityMapping::Detailed(d) => match d.source {
                SourceRef::Fallback(entries) => {
                    assert_eq!(entries.len(), 2, "duplicate yahoo dropped");
                    match &entries[0] {
                        FallbackEntry::Detailed(fd) => assert_eq!(fd.source, "yahoo"),
                        FallbackEntry::Name(_) => panic!("expected Detailed entry"),
                    }
                    match &entries[1] {
                        FallbackEntry::Detailed(fd) => assert_eq!(fd.source, "ecb"),
                        FallbackEntry::Name(_) => panic!("expected Detailed entry"),
                    }
                }
                SourceRef::Single(_) => panic!("expected Fallback chain of 2"),
            },
            CommodityMapping::Simple(_) => panic!("expected Detailed mapping"),
        }
    }

    #[test]
    fn parse_price_skips_malformed_entries() {
        let specs = parse_price_metadata("USD:yahoo/AAPL,bogus,EUR:ecb/EUR.USD");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].quote_currency, "USD");
        assert_eq!(specs[1].quote_currency, "EUR");
    }

    #[test]
    fn parses_bean_price_multi_source_form() {
        // Bean-price syntax: one currency block, comma-separated bare sources.
        // Each source inherits the block's currency.
        let specs = parse_price_metadata("EUR:ecbrates/GBP-EUR,ecb/GBP");
        assert_eq!(
            specs,
            vec![
                PriceSpec {
                    quote_currency: "EUR".into(),
                    source: "ecbrates".into(),
                    ticker: "GBP-EUR".into(),
                },
                PriceSpec {
                    quote_currency: "EUR".into(),
                    source: "ecb".into(),
                    ticker: "GBP".into(),
                },
            ]
        );
    }

    #[test]
    fn parses_bean_price_multi_currency_form() {
        // Bean-price syntax: currency blocks separated by whitespace.
        // Each (quote_currency, source/ticker) tuple flows downstream as its
        // own QuoteSpec, so the fetch loop emits one job per (base, quote)
        // — matching bean-price's per-(base, quote) behavior.
        let specs = parse_price_metadata("USD:yahoo/AAPL CAD:google/AAPL");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].quote_currency, "USD");
        assert_eq!(specs[0].source, "yahoo");
        assert_eq!(specs[1].quote_currency, "CAD");
        assert_eq!(specs[1].source, "google");
        // Semicolon also accepted as a block separator.
        let specs = parse_price_metadata("USD:yahoo/AAPL;CAD:google/AAPL");
        assert_eq!(specs.len(), 2);
    }

    #[test]
    fn parses_mixed_form() {
        // First entry inherits from the block; second carries its own
        // (redundant) `:` prefix per rledger's per-entry form.
        let specs = parse_price_metadata("USD:yahoo/AAPL,USD:google/NASDAQ:AAPL");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].source, "yahoo");
        assert_eq!(specs[1].source, "google");
        assert_eq!(specs[1].ticker, "NASDAQ:AAPL");
    }

    #[test]
    fn parses_ticker_with_embedded_colon_in_bean_price_form() {
        // The disambiguation rule: a `:` AFTER the first `/` is part of
        // the ticker, not a currency prefix.
        let specs = parse_price_metadata("USD:google/NASDAQ:AAPL");
        assert_eq!(specs.len(), 1);
        assert_eq!(specs[0].quote_currency, "USD");
        assert_eq!(specs[0].source, "google");
        assert_eq!(specs[0].ticker, "NASDAQ:AAPL");
    }

    #[test]
    fn ticker_heuristic_rejects_long_or_lowercase() {
        assert!(looks_like_ticker("AAPL"));
        assert!(looks_like_ticker("BTC-USD"));
        assert!(looks_like_ticker("VTI2025"));
        // Issue #952: exchange-suffixed tickers (dots) used to be silently dropped.
        assert!(looks_like_ticker("VECP.AS"));
        assert!(looks_like_ticker("BRK.B"));
        assert!(looks_like_ticker("7203.T"));
        assert!(!looks_like_ticker("usd"));
        assert!(!looks_like_ticker("Vanguard"));
        assert!(!looks_like_ticker("VERYLONGTICKER"));
        assert!(!looks_like_ticker(""));
    }

    #[test]
    fn active_filter_keeps_held_commodities() {
        // Bought 100 AAPL, never sold = active.
        // Bought and sold all BTC = inactive.
        // EUR cash held in Assets:Cash = active.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "AAPL")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "BTC")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "EUR")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy AAPL")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "AAPL"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "AAPL"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 3, 1), "Buy BTC")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(1), "BTC"),
                    ))
                    .with_posting(Posting::new("Equity:Opening", Amount::new(dec!(-1), "BTC"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 4, 1), "Sell BTC")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(-1), "BTC"),
                    ))
                    .with_posting(Posting::new("Equity:Opening", Amount::new(dec!(1), "BTC"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 5, 1), "Receive EUR")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(500), "EUR")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-500), "EUR"),
                    )),
            ),
        ]);
        let active = active_commodities(&dirs, &Options::new(), None);
        assert!(active.contains("AAPL"));
        assert!(active.contains("EUR"));
        assert!(
            !active.contains("BTC"),
            "BTC was fully sold, should not be active"
        );
    }

    #[test]
    fn as_of_filter_includes_holdings_at_that_date_only() {
        // Bean-price compat: with --date X, the active filter should reflect
        // balances ON X, not the latest. A commodity bought before X then
        // fully sold afterwards must STILL be active when fetching as-of X.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "buy SHIB")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "SHIB"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "SHIB"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "sell SHIB")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(-100), "SHIB"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(100), "SHIB"),
                    )),
            ),
        ]);

        // No as_of: the latest balance is zero — SHIB is NOT active.
        let active_now = active_commodities(&dirs, &Options::new(), None);
        assert!(!active_now.contains("SHIB"));

        // as_of in the holding window: SHIB IS active.
        let active_during = active_commodities(&dirs, &Options::new(), Some(date(2024, 4, 1)));
        assert!(
            active_during.contains("SHIB"),
            "SHIB held on 2024-04-01 should be active when fetching as-of that date"
        );

        // as_of after the sell: SHIB no longer active.
        let active_after = active_commodities(&dirs, &Options::new(), Some(date(2024, 12, 31)));
        assert!(!active_after.contains("SHIB"));

        // Boundary: exactly on the buy date — buy applies, SHIB active.
        let active_buy_day = active_commodities(&dirs, &Options::new(), Some(date(2024, 2, 1)));
        assert!(active_buy_day.contains("SHIB"));

        // Boundary: exactly on the sell date — both buy and sell apply, balance=0.
        let active_sell_day = active_commodities(&dirs, &Options::new(), Some(date(2024, 6, 1)));
        assert!(!active_sell_day.contains("SHIB"));
    }

    #[test]
    fn as_of_ignores_close_directive_after_cutoff() {
        // A close in the future shouldn't retroactively wipe out balances
        // that were active on the as-of date.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "buy")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "DOGE"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "DOGE"),
                    )),
            ),
            Directive::Close(Close::new(date(2024, 12, 31), "Assets:Brokerage")),
        ]);
        // As of mid-2024 the account is still open and DOGE is held.
        let active = active_commodities(&dirs, &Options::new(), Some(date(2024, 6, 1)));
        assert!(active.contains("DOGE"));
        // After the close directive's date, DOGE is no longer active.
        let active_after = active_commodities(&dirs, &Options::new(), Some(date(2025, 1, 1)));
        assert!(!active_after.contains("DOGE"));

        // Boundary: exactly on the close date — close is inclusive, so DOGE inactive.
        let active_close_day = active_commodities(&dirs, &Options::new(), Some(date(2024, 12, 31)));
        assert!(!active_close_day.contains("DOGE"));
    }

    #[test]
    fn as_of_filters_commodity_directives_before_walking_them() {
        // Bean-price compat: a commodity directive dated ON OR AFTER the
        // cutoff is excluded — the commodity didn't exist yet at as-of date.
        // Without this filter, a future-dated `commodity` declaration with
        // `price:` metadata would still trigger discovery for a historical
        // fetch.
        let mut early = Commodity::new(date(2024, 1, 1), "AAPL");
        early.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/AAPL".into()),
        );
        let mut late = Commodity::new(date(2030, 1, 1), "FUTURECOIN");
        late.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/FUTURECOIN".into()),
        );
        let dirs = directives(vec![
            Directive::Commodity(early),
            Directive::Commodity(late),
        ]);

        // No as_of: both commodity declarations visible (neither is active,
        // so both filtered by the active check; bypass with inactive=true).
        let all = discover_symbols(&dirs, &Options::new(), true, false, None);
        assert!(all.contains_key("AAPL"));
        assert!(all.contains_key("FUTURECOIN"));

        // as_of in 2025: AAPL declared before, FUTURECOIN declared after.
        // Only AAPL should be discoverable.
        let historical =
            discover_symbols(&dirs, &Options::new(), true, false, Some(date(2025, 6, 1)));
        assert!(historical.contains_key("AAPL"));
        assert!(
            !historical.contains_key("FUTURECOIN"),
            "commodity declared 2030-01-01 must not be discovered when fetching as-of 2025-06-01"
        );

        // Boundary: exactly on the declaration date is exclusive (matches
        // bean-price's `entry.date >= date` skip rule).
        let on_decl_day =
            discover_symbols(&dirs, &Options::new(), true, false, Some(date(2030, 1, 1)));
        assert!(!on_decl_day.contains_key("FUTURECOIN"));

        // One day after: now visible.
        let after_decl =
            discover_symbols(&dirs, &Options::new(), true, false, Some(date(2030, 1, 2)));
        assert!(after_decl.contains_key("FUTURECOIN"));
    }

    #[test]
    fn closed_account_balance_does_not_count_as_active() {
        // A balance left over in a closed account is treated as inactive
        // (the close directive supersedes; any non-zero residual is a
        // validation problem, not an "active" signal for price fetching).
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy stale token")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "DEFUNCT"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "DEFUNCT"),
                    )),
            ),
            Directive::Close(Close::new(date(2024, 12, 31), "Assets:Brokerage")),
        ]);
        let active = active_commodities(&dirs, &Options::new(), None);
        assert!(!active.contains("DEFUNCT"));
    }

    #[test]
    fn undeclared_walks_transactions_for_ticker_shaped_currencies() {
        // Bean-price compat: --undeclared also picks up commodities that
        // appear in postings without their own `commodity` directive.
        // The ticker-shape filter still applies — but only filters out
        // *non-ticker-shaped* names (lowercase, > 10 chars). 3-letter
        // uppercase codes like BAM and SHIB BOTH pass the heuristic
        // and are discovered. The #962 protection is the strict default
        // requiring `price:` metadata, NOT this heuristic.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy SHIB and BAM")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "SHIB"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "SHIB"),
                    ))
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(50), "BAM"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-50), "BAM"),
                    )),
            ),
        ]);

        // Without --undeclared: nothing discovered (no commodity directives).
        let strict = discover_symbols(&dirs, &Options::new(), false, false, None);
        assert!(strict.is_empty());

        // With --undeclared: SHIB AND BAM are both discovered — both pass
        // the ticker-shape heuristic (uppercase, ≤10 chars). The shape
        // filter does NOT filter out 3-letter currency codes; the #962
        // protection is the strict default that excludes commodities
        // without `price:` metadata. Opting into --undeclared opts into
        // the known false-positive exposure for currency codes.
        let with_undeclared = discover_symbols(&dirs, &Options::new(), false, true, None);
        assert!(
            with_undeclared.contains_key("SHIB"),
            "ticker-shaped commodity in transactions should be discovered with --undeclared"
        );
        assert!(
            with_undeclared.contains_key("BAM"),
            "3-letter uppercase currency codes also pass the heuristic — \
             documents the known false-positive exposure of --undeclared"
        );
    }

    #[test]
    fn undeclared_walks_transactions_picks_up_at_cost_currency() {
        // A purchase like `10 AAPL {150 USD}` should make USD discoverable
        // (in addition to AAPL) — bean-price's at-cost-currency walk.
        // USD doesn't pass the ticker-shape filter, but BTC-shaped does.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Wallet")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy ETH with BTC")
                    .with_posting(
                        Posting::new("Assets:Wallet", Amount::new(dec!(1), "ETH"))
                            .with_cost(rustledger_core::CostSpec::empty().with_currency("BTC-USD")),
                    )
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-50000), "USD"),
                    )),
            ),
        ]);

        let with_undeclared = discover_symbols(&dirs, &Options::new(), true, true, None);
        assert!(with_undeclared.contains_key("ETH"));
        assert!(
            with_undeclared.contains_key("BTC-USD"),
            "at-cost currency should also be discovered with --undeclared"
        );
        // USD is a 3-letter uppercase symbol → passes the ticker-shape
        // heuristic too. The #962 protection isn't to filter currency
        // codes from --undeclared output (they're hard to distinguish
        // from tickers shape-wise) — it's that the strict DEFAULT
        // requires `price:` metadata. Opting into --undeclared is
        // declaring "I accept the heuristic might fetch currency codes."
        assert!(with_undeclared.contains_key("USD"));
    }

    #[test]
    fn undeclared_transaction_walk_uses_strict_less_than_for_as_of() {
        // The transaction-walking pass uses strict-less-than (matches
        // bean-price's `entry.date >= date: break` and the commodity-walk
        // above). A transaction dated exactly on `as_of` must NOT contribute
        // its currencies. Without this, multi-day batch runs that pass
        // `--date today` would pick up tomorrow's morning trades from a
        // single ledger.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 3, 1), "boundary day SHIB buy")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "SHIB"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "SHIB"),
                    )),
            ),
        ]);

        // as_of == txn.date → exclude (strict less-than).
        let at_cutoff =
            discover_symbols(&dirs, &Options::new(), true, true, Some(date(2024, 3, 1)));
        assert!(
            !at_cutoff.contains_key("SHIB"),
            "transaction dated exactly on as_of must be excluded (strict less-than, matches bean-price)"
        );

        // as_of > txn.date → include.
        let after_cutoff =
            discover_symbols(&dirs, &Options::new(), true, true, Some(date(2024, 3, 2)));
        assert!(after_cutoff.contains_key("SHIB"));
    }

    #[test]
    fn undeclared_lowercase_or_long_names_still_excluded() {
        // The ticker-shape filter still rejects non-ticker-shaped names
        // even when they appear in transactions (e.g. accidentally-lowercase
        // commodity names from a misconfigured bank importer).
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:X")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Y")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "use weird names")
                    .with_posting(Posting::new("Assets:X", Amount::new(dec!(1), "Vanguard")))
                    .with_posting(Posting::new("Equity:Y", Amount::new(dec!(-1), "Vanguard"))),
            ),
        ]);
        let discovered = discover_symbols(&dirs, &Options::new(), true, true, None);
        assert!(
            !discovered.contains_key("Vanguard"),
            "non-uppercase name should not be picked up even with --undeclared"
        );
    }

    #[test]
    fn discover_picks_up_metadata_driven_commodity() {
        let mut comm = Commodity::new(date(2024, 1, 1), "Vanguard_VTI");
        comm.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/VTI".into()),
        );
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy VTI")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "Vanguard_VTI"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "Vanguard_VTI"),
                    )),
            ),
        ]);
        let discovered = discover_symbols(&dirs, &Options::new(), false, false, None);

        // Even though "Vanguard_VTI" doesn't pass the ticker heuristic,
        // it has price: metadata, so it's discovered.
        let info = discovered
            .get("Vanguard_VTI")
            .expect("should be discovered");
        assert!(info.mapping.is_some());
        assert_eq!(info.quote_currency.as_deref(), Some("USD"));
        assert_eq!(info.quote_specs.len(), 1);
        assert_eq!(info.quote_specs[0].quote_currency, "USD");
    }

    /// Multi-currency `price:` metadata (`USD:yahoo/AAPL CAD:google/AAPL`)
    /// must produce one `QuoteSpec` per declared quote currency. The fetch
    /// loop iterates `quote_specs` and emits one job per (base, quote) —
    /// matching bean-price. Pre-fix, only the first quote was retained and
    /// the CAD price was silently dropped.
    #[test]
    fn discover_picks_up_multi_currency_price_metadata() {
        let mut comm = Commodity::new(date(2024, 1, 1), "AAPL");
        comm.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/AAPL CAD:google/AAPL".into()),
        );
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy AAPL")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "AAPL"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "AAPL"),
                    )),
            ),
        ]);
        let discovered = discover_symbols(&dirs, &Options::new(), false, false, None);

        let info = discovered.get("AAPL").expect("should be discovered");
        assert_eq!(
            info.quote_specs.len(),
            2,
            "multi-currency price: metadata must produce one QuoteSpec per quote"
        );
        assert_eq!(info.quote_specs[0].quote_currency, "USD");
        assert_eq!(info.quote_specs[1].quote_currency, "CAD");
        // Each spec carries its own source/ticker.
        match info.quote_specs[0].mapping.as_ref().expect("USD mapping") {
            CommodityMapping::Detailed(d) => match &d.source {
                SourceRef::Single(s) => assert_eq!(s, "yahoo"),
                SourceRef::Fallback(_) => panic!("expected Single yahoo for USD"),
            },
            CommodityMapping::Simple(_) => panic!("expected Detailed mapping for USD"),
        }
        match info.quote_specs[1].mapping.as_ref().expect("CAD mapping") {
            CommodityMapping::Detailed(d) => match &d.source {
                SourceRef::Single(s) => assert_eq!(s, "google"),
                SourceRef::Fallback(_) => panic!("expected Single google for CAD"),
            },
            CommodityMapping::Simple(_) => panic!("expected Detailed mapping for CAD"),
        }
        // First-spec mirrors are preserved for legacy callers.
        assert_eq!(info.quote_currency.as_deref(), Some("USD"));
        assert!(info.mapping.is_some());
    }

    #[test]
    fn discover_skips_inactive_by_default() {
        let mut comm = Commodity::new(date(2024, 1, 1), "OLD");
        comm.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/OLD".into()),
        );
        let dirs = directives(vec![Directive::Commodity(comm)]);

        // Default: no active postings means OLD is not discovered.
        let discovered = discover_symbols(&dirs, &Options::new(), false, false, None);
        assert!(!discovered.contains_key("OLD"));

        // Opt-in: inactive=true brings it back.
        let discovered_all = discover_symbols(&dirs, &Options::new(), true, false, None);
        assert!(discovered_all.contains_key("OLD"));
    }

    /// `discover_symbols` returns only file-discovered commodities; CLI
    /// symbols are now handled separately by the caller (`price_cmd.rs`)
    /// so they can be subjected to the explicit-source-required check
    /// (#966) instead of getting auto-synthesized default-source
    /// mappings like file-discovered symbols do.
    #[test]
    fn discover_returns_empty_for_empty_ledger() {
        let dirs: Vec<Spanned<Directive>> = vec![];
        let discovered = discover_symbols(&dirs, &Options::new(), false, false, None);
        assert!(discovered.is_empty());
    }

    /// Issue #962: a ticker-shaped commodity name without `price:`
    /// metadata must NOT be discovered by default. `bean-price -f` only
    /// fetches commodities with explicit `price:` metadata; the previous
    /// rustledger fallback to the name heuristic produced unwanted
    /// downloads (e.g., currency code `BAM` was treated as a stock).
    #[test]
    fn discover_skips_no_metadata_commodity_by_default() {
        // `BAM` looks ticker-shaped (3 uppercase letters) and has an
        // active balance, but has no `price:` metadata, so it must be
        // skipped by default.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "BAM")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        let strict = discover_symbols(&dirs, &Options::new(), false, false, None);
        assert!(
            !strict.contains_key("BAM"),
            "BAM has no `price:` metadata, must not be discovered by default (#962)"
        );

        // `--undeclared` brings the heuristic back.
        let with_undeclared = discover_symbols(&dirs, &Options::new(), false, true, None);
        assert!(with_undeclared.contains_key("BAM"));
    }

    /// `price: ""` is an explicit opt-out (bean-price-compatible). It
    /// must suppress discovery even with `--undeclared`, so users can
    /// override the heuristic on a per-commodity basis.
    #[test]
    fn discover_honors_empty_price_opt_out() {
        let mut comm = Commodity::new(date(2024, 1, 1), "BAM");
        comm.meta
            .insert("price".to_string(), MetaValue::String(String::new()));
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        // Even with --undeclared, the empty price: opt-out wins.
        let discovered = discover_symbols(&dirs, &Options::new(), false, true, None);
        assert!(!discovered.contains_key("BAM"));
    }

    /// `quote_currency:` alone (no `price:`) is an explicit user opt-in
    /// for fetching with a configured/default source — it should be
    /// discovered without needing `--undeclared`.
    #[test]
    fn discover_picks_up_quote_currency_only_commodity() {
        let mut comm = Commodity::new(date(2024, 1, 1), "GOVT_EU");
        comm.meta.insert(
            "quote_currency".to_string(),
            MetaValue::String("EUR".into()),
        );
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy GOVT_EU")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "GOVT_EU"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "GOVT_EU"),
                    )),
            ),
        ]);

        let discovered = discover_symbols(&dirs, &Options::new(), false, false, None);
        let info = discovered
            .get("GOVT_EU")
            .expect("quote_currency: alone should opt into discovery");
        assert!(info.mapping.is_none());
        assert_eq!(info.quote_currency.as_deref(), Some("EUR"));
    }

    #[test]
    fn discover_inactive_undeclared_combined_matches_legacy_all_commodities() {
        // Sanity check that --inactive=true + --undeclared=true behaves
        // like the old --all-commodities path: heuristic on, no active
        // filter. Matches the legacy discovery surface.
        let dirs = directives(vec![Directive::Commodity(Commodity::new(
            date(2024, 1, 1),
            "OLD",
        ))]);
        let discovered = discover_symbols(&dirs, &Options::new(), true, true, None);
        assert!(discovered.contains_key("OLD"));
    }

    /// Malformed `price:` metadata (e.g. typo, wrong format) produces no
    /// parsed specs. The commodity is skipped under the strict default
    /// (no usable source), but the malformed flag is set so the caller
    /// can log a warning. This matches `bean-price`, which logs
    /// "Ignoring currency with invalid 'price' source" for the same case.
    #[test]
    fn classify_flags_malformed_price_metadata() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert(
            "price".to_string(),
            MetaValue::String("BOGUS_FORMAT".into()),
        );
        let classification = classify_commodity_meta(&meta);
        assert!(classification.malformed_price);
        assert!(matches!(
            classification.decision,
            DiscoveryDecision::Inherit
        ));
    }

    /// A malformed `price:` paired with a valid `quote_currency:` should
    /// still surface the malformed-price warning, even though the
    /// commodity is included via `quote_currency:`. The caller can then
    /// nudge the user to fix the typo.
    #[test]
    fn classify_flags_malformed_price_even_when_quote_currency_present() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert(
            "price".to_string(),
            MetaValue::String("BOGUS_FORMAT".into()),
        );
        meta.insert(
            "quote_currency".to_string(),
            MetaValue::String("EUR".into()),
        );
        let classification = classify_commodity_meta(&meta);
        assert!(classification.malformed_price);
        assert!(matches!(
            classification.decision,
            DiscoveryDecision::Discovered(_)
        ));
    }

    /// `price: ""` is an opt-out, not malformed — ensure we don't emit a
    /// false-positive warning for the explicit opt-out path.
    #[test]
    fn classify_does_not_flag_empty_price_as_malformed() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert("price".to_string(), MetaValue::String(String::new()));
        let classification = classify_commodity_meta(&meta);
        assert!(!classification.malformed_price);
        assert!(matches!(classification.decision, DiscoveryDecision::OptOut));
    }

    /// Whitespace-only `price:` is treated the same as empty — explicit
    /// opt-out — so users can write `price: "   "` and still suppress
    /// fetching consistently with `price: ""`.
    #[test]
    fn discover_honors_whitespace_only_price_opt_out() {
        let mut comm = Commodity::new(date(2024, 1, 1), "BAM");
        comm.meta
            .insert("price".to_string(), MetaValue::String("   ".into()));
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        let discovered = discover_symbols(&dirs, &Options::new(), false, true, None);
        assert!(!discovered.contains_key("BAM"));
    }

    #[test]
    fn active_filter_handles_explicit_amounts_on_balance_sheet_side() {
        // Simulates the post-booking shape: every posting has explicit units,
        // including the asset side. Confirms the active filter sees the
        // asset-side amount and includes the commodity. The actual
        // interpolation happens in the booking engine before this function
        // sees the directives — `price_cmd.rs` calls `process::load` with
        // booking enabled to ensure that.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy AAPL")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "AAPL"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "AAPL"),
                    )),
            ),
        ]);
        let active = active_commodities(&dirs, &Options::new(), None);
        assert!(active.contains("AAPL"));
    }
}
