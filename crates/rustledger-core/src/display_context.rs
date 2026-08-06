//! Display context for formatting numbers with consistent precision.
//!
//! This module provides the [`DisplayContext`] type which tracks a frequency
//! distribution of decimal places per currency, observed during parsing. The
//! configured [`Precision`] policy then determines how that distribution is
//! collapsed to a single per-currency precision for display.
//!
//! Default policy is [`Precision::MostCommon`] — the *mode* of the dp
//! distribution. This matches Python `bean-query`'s default rendering and
//! ensures that outliers (e.g. a single 28-decimal computed price annotation)
//! don't inflate the display precision for an otherwise 2dp-dominant currency.
//!
//! [`Precision::Maximum`] selects the highest dp ever observed, which is what
//! Python uses when rendering price tables. Callers opt in via
//! [`DisplayContext::set_precision`].
//!
//! # Example
//!
//! ```
//! use rustledger_core::DisplayContext;
//! use rust_decimal_macros::dec;
//!
//! let mut ctx = DisplayContext::new();
//!
//! // Track samples for USD: tied 1×0dp + 1×2dp → tie-break favors larger.
//! ctx.update(dec!(100), "USD");       // 0 dp
//! ctx.update(dec!(50.25), "USD");     // 2 dp
//! ctx.update(dec!(1.5), "EUR");       // 1 dp
//!
//! // Default policy (MostCommon) returns the mode of the per-currency dist.
//! assert_eq!(ctx.get_precision("USD"), Some(2));
//! assert_eq!(ctx.get_precision("EUR"), Some(1));
//! assert_eq!(ctx.get_precision("GBP"), None); // Never seen
//!
//! // format() uses the policy's effective precision.
//! assert_eq!(ctx.format(dec!(100), "USD"), "100.00");
//! assert_eq!(ctx.format(dec!(50.25), "USD"), "50.25");
//! assert_eq!(ctx.format(dec!(1.5), "EUR"), "1.5");
//! ```

use crate::Directive;
use rust_decimal::{Decimal, MathematicalOps};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Sentinel currency key for "naked-decimal" observations.
///
/// Used for values with no associated currency, e.g. BQL `Value::Number`
/// results from `SUM(number)` or `cost_number` columns. Matches Python's
/// `__default__` convention in `beancount.core.display_context`.
pub const DEFAULT_CURRENCY: &str = "__default__";

/// Per-currency frequency distribution of decimal-place counts.
///
/// Replaces the old "max-only" `u32` storage so that [`Precision::MostCommon`]
/// can pick the *mode* of observed precisions (matching Python `bean-query`'s
/// default), while [`Precision::Maximum`] still picks the historical max.
///
/// Uses `BTreeMap` so iteration order is deterministic and `mode()`'s
/// tie-breaking matches Python's "largest dp wins on ties" rule (Python
/// iterates sorted ascending with `>=`, which keeps the *last* equal-count
/// entry — i.e. the largest dp).
#[derive(Debug, Clone, Default)]
struct Distribution {
    hist: BTreeMap<u32, u32>,
}

impl Distribution {
    fn update(&mut self, dp: u32) {
        *self.hist.entry(dp).or_insert(0) += 1;
    }

    fn merge(&mut self, other: &Self) {
        for (&dp, &count) in &other.hist {
            *self.hist.entry(dp).or_insert(0) += count;
        }
    }

    fn max(&self) -> Option<u32> {
        self.hist.keys().next_back().copied()
    }

    /// Most-common dp. On ties, prefer the larger dp (matches
    /// `beancount.core.distribution.Distribution.mode`, which iterates
    /// sorted-ascending with `count >= max_count`).
    fn mode(&self) -> Option<u32> {
        let mut best: Option<(u32, u32)> = None; // (count, dp)
        for (&dp, &count) in &self.hist {
            // `>=` keeps the larger dp on ties because BTreeMap iterates ascending
            if best.is_none_or(|(c, _)| count >= c) {
                best = Some((count, dp));
            }
        }
        best.map(|(_, dp)| dp)
    }
}

/// Policy for resolving the per-currency display precision from the
/// observed distribution.
///
/// Matches Python `beancount.core.display_context.Precision`:
/// - [`MostCommon`](Self::MostCommon) returns the mode of the dp histogram.
///   Used by `bean-query` for its result tables. Outliers (a single 28-decimal
///   price annotation, a single integer-valued cost amid mostly 2dp postings)
///   don't dominate.
/// - [`Maximum`](Self::Maximum) returns the highest dp ever observed for the
///   currency. Used by Python `display_context` when rendering prices, where
///   preserving the highest-precision sample is the explicit goal.
///
/// Default is `MostCommon` to match `bean-query`'s default rendering of
/// position/amount columns. See PR #985 follow-up and beanquery#275 for
/// the upstream conversation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Precision {
    /// Mode of the per-currency distribution (Python `MOST_COMMON`).
    #[default]
    MostCommon,
    /// Maximum dp ever observed (Python `MAXIMUM`).
    Maximum,
}

/// What kind of consumer an output surface is written for.
///
/// Decides whether thousands separators appear. The question is not "will a
/// person read this" but **does the consumer have a grammar**:
///
/// - **machine interchange** (CSV, JSON) does not. A separator forces the
///   field to be quoted and is then rejected by ordinary decimal parsers —
///   `Decimal(field)` breaks (issue #1892). Suppressed unconditionally, and
///   that suppression outranks any ledger or per-commodity declaration.
/// - **ledger text** (`format`, `query --format beancount`) does. Grouped
///   numerals are part of Beancount syntax, so every conforming reader must
///   accept them; the parser, not the file, is the machine boundary. Honors
///   the ledger's declaration (#1896).
/// - **rendered tables** read by a person likewise honor it.
///
/// This exists so the rule is stated ONCE. It was previously re-derived per
/// writer, and the surfaces had already drifted apart: `query --format
/// beancount` emitted separators into ledger text while `format` stripped
/// them, and CSV emitted them while JSON did not.
///
/// `LedgerText` initially suppressed them, on the premise that ledger text has
/// one canonical on-disk form. #1896 abandoned that premise deliberately —
/// `rledger format --ledger` now GROUPS, because a ledger that asks for
/// separators should get them in the file it owns — which put the two ledger
/// text producers back in disagreement until this arm followed. Beancount
/// itself groups here: `grammar.py` calls `dcontext.set_commas(options
/// ["render_commas"])` while parsing, and `printer.py` renders through that
/// same context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputSurface {
    /// A rendered table or report read by a person.
    Human,
    /// CSV/JSON consumed by another program.
    Machine,
    /// Beancount source text.
    LedgerText,
}

impl OutputSurface {
    /// Whether this surface renders thousands separators when the ledger asks
    /// for them.
    ///
    /// Only [`Self::Machine`] refuses, because only its consumers lack a
    /// grammar that admits the separator.
    #[must_use]
    pub const fn renders_thousands_separators(self) -> bool {
        match self {
            Self::Human | Self::LedgerText => true,
            Self::Machine => false,
        }
    }
}

/// Display context for formatting numbers with consistent precision per currency.
///
/// Tracks a frequency distribution of decimal places per currency and exposes
/// it via [`get_precision`](Self::get_precision) under the configured
/// [`Precision`] policy. Default policy is [`Precision::MostCommon`] to match
/// Python `bean-query`.
///
/// Fixed per-currency overrides (from `option "display_precision"`) always
/// win over inferred precision regardless of the policy.
#[derive(Debug, Clone, Default)]
pub struct DisplayContext {
    /// Per-currency observed decimal-place distributions.
    distributions: HashMap<String, Distribution>,

    /// Whether to render commas in numbers (from `option "render_commas"`).
    ///
    /// The LEDGER-WIDE default. A commodity may override it — see
    /// [`Self::render_commas_for`] — so a 4000:1 currency can be grouped
    /// without also grouping two-digit USD amounts.
    render_commas: bool,
    /// Per-commodity overrides of [`Self::render_commas`], from
    /// `render_commas:` metadata on a `commodity` directive.
    ///
    /// Mirrors `fixed_precisions`: grouping and precision are both per-currency
    /// display style, resolved by the same three tiers (inference / global
    /// option / commodity metadata). Grouping had only the global tier, which
    /// is the asymmetry this closes.
    group_overrides: rustc_hash::FxHashMap<String, bool>,

    /// Fixed precision overrides (from `option "display_precision"`).
    /// These take precedence over inferred precision under any policy.
    fixed_precisions: HashMap<String, u32>,

    /// Inference policy for [`DisplayContext::get_precision`]. Defaults
    /// to [`Precision::MostCommon`] to match Python `bean-query`.
    precision: Precision,
}

impl DisplayContext {
    /// Create a new empty display context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Update the display context with a number for a currency.
    ///
    /// Records the decimal precision (number of digits after the decimal
    /// point) of `number` against `currency`'s histogram, so subsequent
    /// `get_precision` calls reflect the new sample under the active
    /// [`Precision`] policy.
    pub fn update(&mut self, number: Decimal, currency: &str) {
        let dp = Self::decimal_precision(number);
        self.distributions
            .entry(currency.to_string())
            .or_default()
            .update(dp);
    }

    /// Update the display context from another display context.
    ///
    /// - Inferred per-currency distributions: merge histograms (sum counts
    ///   across both sides). This preserves frequency information so the
    ///   merged context's mode reflects the union of samples — strictly more
    ///   correct than the old "max of maxes" merge, and matches Python
    ///   `display_context.DisplayContext.update_from`.
    /// - Fixed per-currency overrides (`option "display_precision"`):
    ///   propagated from `other` only when `self` has no fixed override for
    ///   that currency (so a per-context override stays authoritative).
    /// - `render_commas`: enabled if either side has it on (one-way
    ///   "sticky on" merge — same rationale as before).
    /// - `precision` policy: NOT propagated. The policy is a property of
    ///   the consumer (e.g. BQL renderer vs price-display formatter), not
    ///   the data, so it stays as set on `self`.
    ///
    /// The fixed-precision and `render_commas` merging matters when a column
    /// context inherits from a ledger context for `Value::Number` rendering:
    /// without it, the ledger's display options would silently fail to apply
    /// to naked-decimal columns. See PR #961 follow-up.
    pub fn update_from(&mut self, other: &Self) {
        for (currency, dist) in &other.distributions {
            self.distributions
                .entry(currency.clone())
                .or_default()
                .merge(dist);
        }
        for (currency, precision) in &other.fixed_precisions {
            self.fixed_precisions
                .entry(currency.clone())
                .or_insert(*precision);
        }
        if other.render_commas {
            self.render_commas = true;
        }
        // Per-commodity grouping declarations travel with the flag they
        // override. Merging the ledger-wide bit alone silently downgraded a
        // commodity's own `render_commas:` to the global default (#1896).
        for (currency, render) in &other.group_overrides {
            self.group_overrides
                .entry(currency.clone())
                .or_insert(*render);
        }
    }

    /// Adopt `other`'s grouping policy wholesale: the ledger-wide flag and
    /// every per-commodity override.
    ///
    /// Distinct from [`Self::update_from`], which merges precision *facts*
    /// inferred from data and is one-way for grouping. Separator rendering is
    /// presentation policy for a whole table, so a derived context — the query
    /// writer's per-column contexts, say — must take it entire rather than
    /// reconstruct it. Reconstructing it is exactly how `SUM(number)` came to
    /// disagree with `SUM(position)` in one query (#1892), and how a
    /// commodity's own declaration came to be dropped (#1896).
    pub fn adopt_grouping_from(&mut self, other: &Self) {
        self.render_commas = other.render_commas;
        self.group_overrides.clone_from(&other.group_overrides);
    }

    /// Set the inference policy for [`Self::get_precision`].
    ///
    /// Default is [`Precision::MostCommon`] to match Python `bean-query`.
    /// Callers that need to preserve the highest-precision sample (e.g.
    /// price-display formatters) can opt into [`Precision::Maximum`].
    pub const fn set_precision(&mut self, precision: Precision) {
        self.precision = precision;
    }

    /// Get the active inference policy.
    #[must_use]
    pub const fn precision(&self) -> Precision {
        self.precision
    }

    /// Iterate the currencies that have observed dp samples or fixed
    /// overrides, in deterministic-but-unspecified order.
    ///
    /// Skips the `__default__` sentinel — that bucket is for naked-decimal
    /// columns (BQL `Value::Number`) and isn't a "real" currency from the
    /// user's perspective.
    pub fn currencies(&self) -> impl Iterator<Item = &str> {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut out: Vec<&str> = Vec::new();
        for currency in self
            .distributions
            .keys()
            .chain(self.fixed_precisions.keys())
            .map(String::as_str)
        {
            if currency != DEFAULT_CURRENCY && seen.insert(currency) {
                out.push(currency);
            }
        }
        out.sort_unstable();
        out.into_iter()
    }

    /// Export every currency's RESOLVED precision (fixed override if
    /// set, else the inferred precision under the active policy) as a
    /// wire-friendly list, sorted by currency. This is what crosses the
    /// FFI boundary as `ledger-options.display-precision` (#1766): the
    /// same per-currency answer [`Self::get_precision`] would give, so
    /// an embedder consuming the list renders with this context's
    /// precision decisions without re-deriving inference (rustfava's
    /// loader keeps a Python re-derivation only as a fallback for
    /// engines that predate this field). Skips the `__default__`
    /// naked-decimal bucket (see [`Self::currencies`]).
    #[must_use]
    pub fn resolved_precisions(&self) -> Vec<(String, u32)> {
        self.currencies()
            .filter_map(|c| self.get_precision(c).map(|p| (c.to_string(), p)))
            .collect()
    }

    /// Return the dp histogram for `currency` as ascending `(dp, count)`
    /// pairs. Empty if the currency has no observed samples.
    ///
    /// Useful for diagnostic / debugging tooling
    /// (e.g. `rledger doctor display-context`) that wants to show *why*
    /// a particular precision was chosen.
    #[must_use]
    pub fn histogram(&self, currency: &str) -> Vec<(u32, u32)> {
        self.distributions.get(currency).map_or_else(Vec::new, |d| {
            d.hist.iter().map(|(&dp, &c)| (dp, c)).collect()
        })
    }

    /// Look up the precision that *would* be returned under a specific
    /// policy, without mutating `self`. Same semantics as
    /// [`Self::get_precision`] but lets a single context be queried
    /// under both policies (e.g. for diagnostic output that compares
    /// `MostCommon` vs `Maximum`).
    #[must_use]
    pub fn precision_under(&self, currency: &str, policy: Precision) -> Option<u32> {
        if let Some(&fixed) = self.fixed_precisions.get(currency) {
            return Some(fixed);
        }
        let dist = self.distributions.get(currency)?;
        match policy {
            Precision::MostCommon => dist.mode(),
            Precision::Maximum => dist.max(),
        }
    }

    /// True if `currency` has a fixed-precision override
    /// (from `option "display_precision"` or
    /// [`Self::set_fixed_precision`]).
    #[must_use]
    pub fn has_fixed_precision(&self, currency: &str) -> bool {
        self.fixed_precisions.contains_key(currency)
    }

    /// This context, adjusted for the surface it will be written to.
    ///
    /// Only `render_commas` is affected — precision is a property of the data
    /// and is identical on every surface. See [`OutputSurface`] for why the
    /// distinction exists.
    ///
    /// Borrows unless the flag actually has to change, so the common cases
    /// cost nothing: a ledger where nothing groups (almost all of them) and
    /// any human-facing surface both borrow. Only suppressing separators for a
    /// machine or ledger-text surface clones, and that clone carries the
    /// per-currency histograms — worth avoiding on a REPL's hot path, and
    /// wasted entirely on the JSON writer, which ignores the context.
    ///
    /// The borrow test is [`Self::renders_any_commas`], not the ledger-wide
    /// flag: a commodity may declare `render_commas: TRUE` while the ledger
    /// default is off, and borrowing on the strength of the global flag alone
    /// would leak that commodity's separators onto a machine surface.
    #[must_use]
    pub fn for_surface(&self, surface: OutputSurface) -> std::borrow::Cow<'_, Self> {
        if !self.renders_any_commas() || surface.renders_thousands_separators() {
            return std::borrow::Cow::Borrowed(self);
        }
        let mut ctx = self.clone();
        ctx.render_commas = false;
        // Suppression is absolute: a per-commodity opt-in must not survive
        // onto a surface whose consumer has no grammar for separators.
        ctx.group_overrides.clear();
        std::borrow::Cow::Owned(ctx)
    }

    /// Set the `render_commas` flag.
    pub const fn set_render_commas(&mut self, render_commas: bool) {
        self.render_commas = render_commas;
    }

    /// Declare whether `currency` renders thousands separators, overriding the
    /// ledger-wide [`Self::set_render_commas`].
    pub fn set_render_commas_for(&mut self, currency: &str, render: bool) {
        self.group_overrides.insert(currency.to_string(), render);
    }

    /// Whether `currency` renders thousands separators: its own declaration if
    /// it has one, else the ledger-wide default.
    ///
    /// Numerals with no currency in scope — metadata values, `custom`
    /// directive values — have nothing to look up and take the default.
    #[must_use]
    pub fn render_commas_for(&self, currency: &str) -> bool {
        self.group_overrides
            .get(currency)
            .copied()
            .unwrap_or(self.render_commas)
    }

    /// Whether ANY currency renders separators.
    ///
    /// Lets a caller skip the per-numeral lookup entirely for the overwhelming
    /// majority of ledgers, which declare nothing.
    #[must_use]
    pub fn renders_any_commas(&self) -> bool {
        self.render_commas || self.group_overrides.values().any(|v| *v)
    }

    /// Get the `render_commas` flag.
    #[must_use]
    pub const fn render_commas(&self) -> bool {
        self.render_commas
    }

    /// Set a fixed precision for a currency (from `option "display_precision"`).
    ///
    /// Fixed precision takes precedence over inferred precision.
    pub fn set_fixed_precision(&mut self, currency: &str, precision: u32) {
        self.fixed_precisions
            .insert(currency.to_string(), precision);
    }

    /// Build a display context from a set of directives plus fixed
    /// per-currency overrides. This is THE canonical builder — the loader
    /// calls it for every load, and the FFI component's `session.format`
    /// calls it over the held entries (#1766) — so the sampling rules
    /// below stay in one place.
    ///
    /// Four stages, in precedence order (later wins):
    /// 1. Scan every directive's amounts to infer per-currency dp
    ///    distributions (posting units, cost specs, price annotations,
    ///    balance amounts + tolerances, price directives).
    /// 2. Apply `fixed_precisions` (from `option "display_precision"`).
    /// 3. Apply per-commodity `precision: N` metadata (issue #991), AFTER
    ///    the options so a commodity-level declaration wins over the
    ///    global option. Multi-declaration of the same currency is
    ///    last-wins (matches typical option-stacking semantics). Invalid
    ///    values are silently skipped here — `rustledger-validate`
    ///    surfaces them as `InvalidPrecisionMetadata` warnings (E5003) so
    ///    users see the problem without breaking loading.
    ///
    /// 4. Apply `render_commas`, the ledger-wide grouping flag, plus the
    ///    per-commodity `render_commas: TRUE|FALSE` declarations picked up in
    ///    the same walk as stage 3. Grouping resolves by the same tiers as
    ///    precision — see [`Self::render_commas_for`].
    ///
    /// The iterator must be cheaply cloneable (e.g. a slice iter or a
    /// `map` over one) because the directives are walked twice (amount
    /// scan, then commodity metadata).
    ///
    /// `render_commas` is a PARAMETER rather than something callers apply
    /// afterwards with [`Self::set_render_commas`]. It used to be the latter,
    /// and both production callers carried their own copy of
    /// `from_directives(..)` + `set_render_commas(..)`; deleting the second
    /// line from the FFI copy passed the entire test suite. Requiring it here
    /// makes that omission a compile error (#1902 Phase 2).
    ///
    /// [`Self::set_render_commas`] remains for contexts built some other way —
    /// a derived or per-column context, which is not a ledger load.
    pub fn from_directives<'a, I>(
        directives: I,
        fixed_precisions: impl IntoIterator<Item = (&'a str, u32)>,
        render_commas: bool,
    ) -> Self
    where
        I: IntoIterator<Item = &'a Directive>,
        I::IntoIter: Clone,
    {
        let directives = directives.into_iter();
        let mut ctx = Self::new();

        // Stage 1: scan directives for amounts to infer precision.
        for directive in directives.clone() {
            match directive {
                Directive::Transaction(txn) => {
                    for posting in &txn.postings {
                        // Units (IncompleteAmount)
                        if let Some(ref units) = posting.units
                            && let (Some(number), Some(currency)) =
                                (units.number(), units.currency())
                        {
                            ctx.update(number, currency);
                        }
                        // Cost (CostSpec) — feed the user-written amount to
                        // the display-context inference. Prefer `total()`
                        // over `per_unit()` so that for `PerUnitFromTotal`
                        // we sample the user's literal `{{ total }}` rather
                        // than the booker-derived per-unit (which has been
                        // divided by |units| and typically carries far more
                        // trailing precision than the source spec).
                        if let Some(ref cost) = posting.cost
                            && let (Some(number), Some(currency)) = (
                                cost.number.map(|cn| {
                                    cn.total().or_else(|| cn.per_unit()).unwrap_or_default()
                                }),
                                &cost.currency,
                            )
                        {
                            ctx.update(number, currency.as_str());
                        }
                        // Price annotations: included so the per-currency dist
                        // sees them, matching Python beancount's DisplayContext
                        // population. With the default `Precision::MostCommon`
                        // policy (introduced for bean-query parity), high-
                        // precision computed exchange rates are naturally
                        // ignored by the mode — they're a small minority next
                        // to mainstream postings. Pre-fix (under MAX policy)
                        // they were excluded to avoid inflating display
                        // precision; that exclusion is no longer needed.
                        if let Some(ref price) = posting.price
                            && let Some(amount) = price.amount()
                        {
                            ctx.update(amount.number, amount.currency.as_str());
                        }
                    }
                }
                Directive::Balance(bal) => {
                    ctx.update(bal.amount.number, bal.amount.currency.as_str());
                    if let Some(tol) = bal.tolerance {
                        ctx.update(tol, bal.amount.currency.as_str());
                    }
                }
                Directive::Price(p) => {
                    // Same rationale as posting price annotations above —
                    // included now that MostCommon is the default. The single
                    // 28dp computed-rate price won't shift the mode for a
                    // currency with hundreds of mainstream postings.
                    ctx.update(p.amount.number, p.amount.currency.as_str());
                }
                // A `custom` directive can carry amounts (Fava's
                // `custom "budget" Expenses:Food "monthly" 400.00 USD`), but they
                // deliberately do NOT inform display precision.
                //
                // They were tried as a source and are not one: the decimal count
                // a user writes in a budget line is a stylistic choice about the
                // DECLARATION, while the figure a budget report prints is
                // pro-rated and a repeating decimal by construction. Taking the
                // declared scale rounded `0.5 BTC` accrued over 14/31 of a month
                // to `0.2` against a true 0.22580645 — 12% low — and taking an
                // integer `1 BTC` pinned the currency to 0 dp. A consumer that
                // needs to render a currency this context has never seen should
                // choose its own precision (the budget report rounds and
                // normalizes), rather than inferring one from metadata.
                Directive::Custom(_)
                | Directive::Pad(_)
                | Directive::Open(_)
                | Directive::Close(_)
                | Directive::Commodity(_)
                | Directive::Event(_)
                | Directive::Query(_)
                | Directive::Note(_)
                | Directive::Document(_) => {}
            }
        }

        // Stage 2: fixed precisions from options (override inferred values).
        for (currency, precision) in fixed_precisions {
            ctx.set_fixed_precision(currency, precision);
        }

        // Stage 2b: the ledger-wide grouping flag.
        //
        // A PARAMETER rather than a post-construction setter on purpose. Both
        // production callers — the loader's `build_display_context` and the FFI
        // component's `session.format` — used to call `set_render_commas`
        // immediately after this, as two independent copies of the same
        // six-line recipe with nothing asserting they agreed. Deleting the call
        // from the FFI copy passed the entire workspace test suite. Threading it
        // through the signature makes forgetting it a compile error instead.
        ctx.set_render_commas(render_commas);

        // Stage 3: per-commodity `precision: N` metadata (see doc above).
        for directive in directives {
            if let Directive::Commodity(comm) = directive
                && let Some(value) = comm.meta.get("precision")
                && let Ok(precision) = crate::parse_precision_meta(value)
            {
                ctx.set_fixed_precision(comm.currency.as_str(), precision);
            }
            // Same tier, same walk: per-commodity `render_commas: TRUE|FALSE`.
            // Deliberately the same mechanism as `precision:` — beancount
            // ignores metadata keys it does not know, so a ledger carrying this
            // still round-trips through beancount and fava untouched.
            if let Directive::Commodity(comm) = directive
                && let Some(value) = comm.meta.get("render_commas")
                && let Some(render) = crate::meta_value_as_bool(value)
            {
                ctx.set_render_commas_for(comm.currency.as_str(), render);
            }
        }

        ctx
    }

    /// Get the precision for a currency.
    ///
    /// Returns the fixed precision if set; otherwise looks up the inferred
    /// precision under the active [`Precision`] policy
    /// ([`MostCommon`](Precision::MostCommon) by default — the mode of the
    /// observed distribution; or [`Maximum`](Precision::Maximum) — the highest
    /// observed dp). Returns `None` if the currency has never been seen.
    #[must_use]
    pub fn get_precision(&self, currency: &str) -> Option<u32> {
        if let Some(&precision) = self.fixed_precisions.get(currency) {
            return Some(precision);
        }
        let dist = self.distributions.get(currency)?;
        match self.precision {
            Precision::MostCommon => dist.mode(),
            Precision::Maximum => dist.max(),
        }
    }

    /// Get the default precision used when formatting a Decimal that has no
    /// associated currency (e.g. the result of `SUM(number)` in BQL).
    ///
    /// Resolution order (matches the BQL renderer's expectations after
    /// PR #986):
    ///
    /// 1. **`__default__` bucket** — if any naked-decimal observations have
    ///    been recorded via `update(n, DEFAULT_CURRENCY)`, the bucket's
    ///    effective precision wins. This is what BQL populates for
    ///    `Value::Number` columns (matches Python `bean-query`'s per-column
    ///    `DecimalRenderer`).
    /// 2. **Max effective precision across every other currency** — fallback
    ///    when no naked-decimal observations exist. Covers issue #954: a
    ///    column of `Value::Number(0)` that came from an aggregate
    ///    collapsing to literal zero still renders with the column's
    ///    expected dp (e.g. `0.00` for a USD-only file).
    /// 3. **Returns 0** if no currencies have been recorded at all.
    ///
    /// "Effective" precision means per-currency `fixed` overrides `inferred`
    /// (same rule as [`Self::get_precision`]) and respects the active
    /// [`Precision`] policy, so a fixed `display_precision` of 2 for USD
    /// won't be overridden by an inferred 4-digit value.
    #[must_use]
    pub fn default_precision(&self) -> u32 {
        // Prefer the `__default__` bucket if it has samples — this is what
        // BQL renderers populate for naked-Decimal columns (`Value::Number`
        // results from `SUM(number)`, `cost_number`, etc.). Matches Python
        // `bean-query`'s `DecimalRenderer`, which tracks per-column dp
        // independently of the per-currency dctx.
        if let Some(dp) = self.get_precision(DEFAULT_CURRENCY) {
            return dp;
        }

        // Fall back to max-of-effective-precisions across all known
        // currencies. Used when no explicit naked-decimal observations
        // were made (e.g. a query that returns aggregates with implicit
        // 0 results — issue #954). `get_precision` handles fixed-vs-
        // inferred priority and respects the active `Precision` policy.
        let mut max_dp: u32 = 0;
        let mut seen: HashSet<&str> = HashSet::new();
        for currency in self
            .fixed_precisions
            .keys()
            .chain(self.distributions.keys())
            .map(String::as_str)
        {
            if seen.insert(currency)
                && currency != DEFAULT_CURRENCY
                && let Some(dp) = self.get_precision(currency)
            {
                max_dp = max_dp.max(dp);
            }
        }
        max_dp
    }

    /// Quantize a number to the tracked precision for a currency.
    ///
    /// Mirrors Python's `Decimal.quantize`: the result has *exactly* the
    /// target scale — rounding when the input has more dp, padding with
    /// trailing zeros when the input has fewer. This matches what
    /// `bean-query`'s `AmountRenderer` does: it quantizes via the ledger
    /// dctx before populating the column dctx, so the column dctx sees
    /// uniformly-padded values.
    ///
    /// If the currency has no tracked precision, returns the number
    /// unchanged.
    ///
    /// Pre-fix this used `round_dp(dp)`, which only ROUNDS down — it
    /// never PADS up. That meant a 2dp input under a 4dp target stayed
    /// 2dp, the column dctx saw dp=2, and the output rendered 2dp instead
    /// of bean-query's 4dp.
    #[must_use]
    pub fn quantize(&self, number: Decimal, currency: &str) -> Decimal {
        if let Some(dp) = self.get_precision(currency) {
            let mut rounded = number.round_dp(dp);
            // round_dp can leave a smaller scale than `dp` (it only rounds
            // *down* the dp count). rescale pads up to exactly `dp`.
            rounded.rescale(dp);
            rounded
        } else {
            number
        }
    }

    /// Format a decimal number for a currency using the tracked precision.
    ///
    /// Render rules (matching bean-query's `AmountRenderer.format`):
    /// - If the value's intrinsic scale exceeds the currency's tracked
    ///   precision, render at the value's scale. Python's `decimal`
    ///   carries scale through arithmetic and bean-query preserves it,
    ///   so a `SUM(number) GROUP BY currency` that aggregates a
    ///   `-805.50896` row and a `-396.50000` row renders as
    ///   `-1202.00896` (scale=5), not `-1202.01` (rounded to USD's 2dp).
    /// - If the value's scale is less than the tracked precision, pad
    ///   with trailing zeros (`7.5 USD` → `7.50`). Preserves the
    ///   #954 fix that stops `SUM(0.00) = 0` rendering as plain `0`.
    /// - If the currency has no tracked precision, fall through to the
    ///   value's natural rendering with trailing zeros stripped.
    ///
    /// The previous implementation always quantized to the tracked
    /// precision via `round_dp(dp)`. That was correct for under-scale
    /// padding but wrong for over-scale truncation — it lost
    /// arithmetic precision that bean-query preserved (closes #1103).
    #[must_use]
    pub fn format(&self, number: Decimal, currency: &str) -> String {
        let precision = self.get_precision(currency);

        if let Some(dp) = precision {
            // Render at max(value_scale, tracked_dp). When value_scale
            // already meets or exceeds dp, `round_dp` is a no-op (it only
            // rounds when scale > target). When value_scale is shorter,
            // `ensure_decimal_places` pads to dp. So this branch covers
            // both "preserve high precision" and "pad short precision"
            // without losing either.
            let effective_dp = number.scale().max(dp);
            let rounded = number.round_dp(effective_dp);
            let formatted = format!("{rounded}");
            let formatted = Self::ensure_decimal_places(&formatted, effective_dp);
            if self.render_commas_for(currency) {
                Self::add_commas(&formatted)
            } else {
                formatted
            }
        } else {
            // No tracked precision - use natural formatting
            let formatted = number.normalize().to_string();
            if self.render_commas_for(currency) {
                Self::add_commas(&formatted)
            } else {
                formatted
            }
        }
    }

    /// Ledger-text variant of [`Self::format`] (#1766): pads a TRACKED
    /// currency's value to the tracked precision (never rounding an
    /// over-precise value away), and returns an UNTRACKED currency's
    /// value at its own scale, byte-faithful — no `normalize()`
    /// trailing-zero stripping, which would silently widen a balance
    /// assertion's implicit tolerance. Never emits thousands
    /// separators regardless of `render_commas`: canonical ledger text
    /// carries none (separators stay a report/query display concern).
    #[must_use]
    pub fn format_plain(&self, number: Decimal, currency: &str) -> String {
        match self.get_precision(currency) {
            Some(dp) => {
                let effective_dp = number.scale().max(dp);
                let rounded = number.round_dp(effective_dp);
                let formatted = format!("{rounded}");
                Self::ensure_decimal_places(&formatted, effective_dp)
            }
            None => number.to_string(),
        }
    }

    /// Format an amount (number + currency) using the tracked precision.
    ///
    /// Unlike [`Self::format`] (which preserves over-scale arithmetic
    /// precision to match Python `bean-query`'s `DecimalRenderer` for
    /// scalar `Value::Number` results), this method always *quantizes* to
    /// the currency's tracked dp — matching bean-query's `AmountRenderer`
    /// for Amounts, Positions, and Inventory entries.
    ///
    /// Python uses two distinct renderers for the two semantic kinds of
    /// output:
    ///
    /// - `DecimalRenderer` for naked decimals (preserves scale, since
    ///   Python `decimal` carries scale through arithmetic).
    /// - `AmountRenderer` for amount-typed values (uses the ledger's
    ///   display context per-currency dp, which is the user-facing
    ///   "how many decimal places does this currency render at" setting).
    ///
    /// Rust used to conflate the two through a single `format` call,
    /// which is why #1103's fix (preserving scale in `format`) inadvertently
    /// regressed the BQL compat suite by ~7pp on queries that produce
    /// `Value::Inventory` — the position amounts inside the inventory now
    /// render with raw arithmetic scale instead of the currency's display
    /// dp. See #1112 for the regression analysis.
    #[must_use]
    pub fn format_amount(&self, number: Decimal, currency: &str) -> String {
        format!("{} {}", self.format_quantized(number, currency), currency)
    }

    /// Format the number portion of an Amount/Position (no currency
    /// suffix), quantized to the tracked dp.
    ///
    /// Used by the BQL `numberify` rendering path that strips the
    /// currency from positions/inventories — same semantics as
    /// [`Self::format_amount`] but without the trailing ` <CURRENCY>`.
    #[must_use]
    pub fn format_amount_number(&self, number: Decimal, currency: &str) -> String {
        self.format_quantized(number, currency)
    }

    /// Internal: quantize `number` to `currency`'s tracked dp (rounding
    /// and padding) and stringify. Falls back to natural representation
    /// when the currency is untracked.
    fn format_quantized(&self, number: Decimal, currency: &str) -> String {
        let raw = match self.get_precision(currency) {
            Some(dp) => {
                let mut rounded = number.round_dp(dp);
                // `round_dp` leaves a smaller scale than `dp` when the
                // input had fewer dp; `rescale` pads with trailing zeros
                // to exactly `dp`.
                rounded.rescale(dp);
                rounded.to_string()
            }
            None => number.normalize().to_string(),
        };
        if self.render_commas_for(currency) {
            Self::add_commas(&raw)
        } else {
            raw
        }
    }

    /// Format a Decimal that has no associated currency.
    ///
    /// Used by the BQL query renderer for `Value::Number` results —
    /// bare Decimals produced by aggregates like `SUM(number)` or
    /// columns like `cost_number`.
    ///
    /// Matches Python `bean-query`'s `DecimalRenderer.format`, which
    /// uses the value's *natural* string representation (preserving the
    /// scale baked into the Decimal) without imposing uniform precision
    /// across rows. So `Value::Number(Decimal('0.00'))` renders `0.00`
    /// (scale survives — covers issue #954) while `Value::Number(0)`
    /// renders `0` (no artificial padding).
    ///
    /// When the value has scale 0 (no fractional part) but the context
    /// has a `__default__`-bucket precision, we DO pad up to that
    /// precision — this is the issue #954 path: an aggregate that
    /// collapsed to literal zero (scale lost) still gets rendered with
    /// the column's expected dp.
    #[must_use]
    pub fn format_default(&self, number: Decimal) -> String {
        // Match Python `bean-query`'s `DecimalRenderer.format`: render
        // each value at its intrinsic scale. No padding to a "column
        // default precision" — that branch was added as a fix for
        // #954 ("`SUM(0.00 + -0.00)` rendered as `0` instead of
        // `0.00`"), but the real bug there was `n.normalize()` stripping
        // the SUM result's scale to 0 *before* rendering. Once that
        // normalize was removed, scale-2 SUMs naturally render as
        // `0.00` via `to_string()` without any padding step. The padding
        // overfit covered up the symptom but caused two new shapes of
        // divergence:
        //
        // 1. Mixed-scale columns where a scale-0 cell renders next to
        //    a scale-25 cell get the scale-0 value padded to 25dp
        //    (`1000` → `1000.0000000000000000000000000`). Bean-query
        //    renders the scale-0 cell as `1000`.
        // 2. Literal `Decimal(0)` values rendered as `0.00` instead of
        //    `0` even when no SUM aggregator was involved. Bean-query
        //    renders `Decimal(0)` as `0`.
        //
        // Cap total significant digits at 28 to match Python's default
        // `Decimal` context precision (`getcontext().prec`). rust_decimal's
        // 96-bit mantissa can land at 29 sig figs from some divisions
        // (e.g. `300 / 1.763 = 170.16449…` with 26 fractional + 3 integer
        // = 29 digits, where Python clamps the same division at 25
        // fractional digits = 28 total).
        const PYTHON_DECIMAL_PRECISION: u32 = 28;
        let capped = Self::cap_significant_digits(number, PYTHON_DECIMAL_PRECISION);
        let formatted = capped.to_string();
        if self.render_commas {
            Self::add_commas(&formatted)
        } else {
            formatted
        }
    }

    /// Round `number` to at most `max_sig` significant digits, matching
    /// Python's `Decimal` context-precision-clamped arithmetic. No-op
    /// when the value already fits; otherwise rounds half-even (Python's
    /// `Decimal` default rounding mode).
    ///
    /// Handles both fractional and integer-only excess:
    ///
    /// - Fractional case (`new_scale > 0`): rounds via
    ///   [`Decimal::round_dp_with_strategy`] which truncates trailing
    ///   fractional digits.
    /// - Integer-only case (`number.scale() < digits - max_sig`):
    ///   `round_dp_with_strategy(0, …)` would leave the over-precise
    ///   integer unchanged, since it can't go to negative scales. We
    ///   scale by a power of ten, round to nearest integer, then
    ///   restore the magnitude — same as Python's clamp on a 29-digit
    ///   integer, which puts it in scientific form with a 28-digit
    ///   mantissa. Caught by Copilot review on PR #1064.
    fn cap_significant_digits(number: Decimal, max_sig: u32) -> Decimal {
        // mantissa() returns the integer mantissa; its decimal length is
        // the number of significant digits regardless of scale. Zero has
        // zero significant digits by this convention — `ilog10` returns
        // `None` and we fall through to the early-return below.
        let mantissa_abs = number.mantissa().unsigned_abs();
        let digits = mantissa_abs.checked_ilog10().map_or(0, |x| x + 1);
        if digits <= max_sig {
            return number;
        }
        let excess = digits - max_sig;
        if excess <= number.scale() {
            // Trimming only affects fractional digits — use the standard
            // dp-based rounding directly.
            return number.round_dp_with_strategy(
                number.scale() - excess,
                rust_decimal::RoundingStrategy::MidpointNearestEven,
            );
        }
        // Excess exceeds the available fractional digits: we have to
        // round integer-portion digits, which `round_dp_with_strategy`
        // can't express (it doesn't support negative dp). Lift by a
        // power of 10, round to nearest integer, drop back.
        // `integer_excess` is always >= 1 here.
        let integer_excess = excess - number.scale();
        let Some(factor) = Decimal::TEN.checked_powu(u64::from(integer_excess)) else {
            // `10^integer_excess` overflows when `integer_excess` is
            // implausibly large (>28). The input must have been an
            // already-overflowed Decimal; bail out with the original
            // value rather than panicking.
            return number;
        };
        let lifted = number / factor;
        let rounded =
            lifted.round_dp_with_strategy(0, rust_decimal::RoundingStrategy::MidpointNearestEven);
        rounded * factor
    }

    /// Get the decimal precision (number of digits after decimal point) of a number.
    const fn decimal_precision(number: Decimal) -> u32 {
        // scale() returns the number of decimal digits
        number.scale()
    }

    /// Ensure a formatted number has exactly `dp` decimal places.
    /// Adds trailing zeros if needed, or adds ".00..." if no decimal point.
    fn ensure_decimal_places(s: &str, dp: u32) -> String {
        if dp == 0 {
            // No decimal places needed - remove any decimal point
            return s.split('.').next().unwrap_or(s).to_string();
        }

        let dp = dp as usize;
        if let Some(dot_pos) = s.find('.') {
            let current_decimals = s.len() - dot_pos - 1;
            if current_decimals >= dp {
                // Already has enough or more decimals
                s.to_string()
            } else {
                // Need to add trailing zeros
                let zeros_needed = dp - current_decimals;
                format!("{s}{}", "0".repeat(zeros_needed))
            }
        } else {
            // No decimal point - add one with zeros
            format!("{s}.{}", "0".repeat(dp))
        }
    }

    /// Add thousand separators (commas) to a formatted number string.
    fn add_commas(s: &str) -> String {
        // Split on decimal point
        let (integer_part, decimal_part) = match s.find('.') {
            Some(pos) => (&s[..pos], Some(&s[pos..])),
            None => (s, None),
        };

        // Handle negative sign
        let (sign, digits) = if let Some(stripped) = integer_part.strip_prefix('-') {
            ("-", stripped)
        } else {
            ("", integer_part)
        };

        // Add commas to integer part (from right to left)
        let mut result = String::with_capacity(digits.len() + digits.len() / 3);
        for (i, c) in digits.chars().rev().enumerate() {
            if i > 0 && i % 3 == 0 {
                result.push(',');
            }
            result.push(c);
        }
        let integer_with_commas: String = result.chars().rev().collect();

        // Combine parts
        match decimal_part {
            Some(dec) => format!("{sign}{integer_with_commas}{dec}"),
            None => format!("{sign}{integer_with_commas}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_update_and_get_precision_most_common_default() {
        // Default policy is MostCommon (matches Python bean-query). With
        // 2 integer-valued samples and 1 fractional, the mode is 0dp.
        let mut ctx = DisplayContext::new();

        ctx.update(dec!(100), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        // Tied at 1×0dp + 1×2dp → tie-break favors larger dp = 2.
        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Now 2×0dp + 1×2dp → mode is 0dp (most common).
        ctx.update(dec!(1), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        // Unknown currency
        assert_eq!(ctx.get_precision("EUR"), None);
    }

    #[test]
    fn test_update_and_get_precision_maximum_policy() {
        // Same samples as the MostCommon test, but with Maximum policy:
        // the highest dp ever observed wins — preserves the historical
        // behavior for callers that opt in.
        let mut ctx = DisplayContext::new();
        ctx.set_precision(Precision::Maximum);

        ctx.update(dec!(100), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Adding more 0dp samples doesn't lower the max.
        ctx.update(dec!(1), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_default_precision_prefers_default_bucket_over_max_of_modes() {
        // When BQL renders a naked-Decimal column, it observes the column's
        // actual values into the `__default__` bucket (matching Python
        // bean-query's per-column DecimalRenderer). default_precision must
        // prefer that bucket over the max-of-modes across other currencies
        // — otherwise an unrelated currency with a higher mode (e.g. VBMPX
        // at 3dp from `3.149 VBMPX` postings) would inflate the precision
        // of a USD `cost_number` column.
        let mut ctx = DisplayContext::new();
        // Ledger context: USD has mode 2, VBMPX has mode 3.
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        for _ in 0..5 {
            ctx.update(dec!(1.234), "VBMPX");
        }
        // Without naked-decimal observations, default_precision falls
        // back to max-of-modes = 3 (VBMPX wins).
        assert_eq!(ctx.default_precision(), 3);
        // After observing two 2dp values into __default__, that bucket's
        // mode (2) takes precedence regardless of VBMPX.
        ctx.update(dec!(128.99), DEFAULT_CURRENCY);
        ctx.update(dec!(131.73), DEFAULT_CURRENCY);
        assert_eq!(ctx.default_precision(), 2);
    }

    #[test]
    fn test_format_default_integer_column_stays_integer() {
        // A naked-decimal column where every observed value has scale 0
        // (e.g. an integer count column from a query like
        // `SELECT account, SUM(units) WHERE units > 0`) should render
        // each value as an integer, NOT pad to some fractional precision
        // borrowed from an unrelated currency.
        //
        // Even though USD has 2dp inferred, the __default__ bucket's
        // mode is 0, so format_default returns the value's natural
        // string ("100", "5", etc.) — the scale==0 padding branch only
        // fires when the resolved default_precision > 0. Here dp = 0
        // so no padding.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // ledger USD has 2dp
        // Column observes integer values into __default__:
        for n in [dec!(100), dec!(5), dec!(42)] {
            ctx.update(n, DEFAULT_CURRENCY);
        }
        // __default__ mode is 0 → no padding, natural rendering.
        assert_eq!(ctx.format_default(dec!(100)), "100");
        assert_eq!(ctx.format_default(dec!(5)), "5");
        // A fractional value still prints at its natural scale (matches
        // Python `DecimalRenderer` per-row formatting).
        assert_eq!(ctx.format_default(dec!(7.5)), "7.5");
    }

    #[test]
    fn test_default_precision_falls_back_when_default_bucket_empty() {
        // Issue #954: a column of `Value::Number(0)` (e.g. SUM that
        // collapsed to zero) has no naked-decimal observations to
        // populate __default__. default_precision falls back to the
        // max-of-modes so we still render `0.00` instead of `0`.
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        // No __default__ observations.
        assert_eq!(ctx.default_precision(), 2);
    }

    // ===== Diagnostic-API tests (currencies / histogram / precision_under) =====

    #[test]
    fn test_currencies_skips_default_sentinel() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.update(dec!(0.5), "EUR");
        ctx.update(dec!(100), DEFAULT_CURRENCY); // sentinel — must be hidden
        let cs: Vec<&str> = ctx.currencies().collect();
        assert_eq!(cs, vec!["EUR", "USD"]); // sorted, no __default__
    }

    #[test]
    fn test_currencies_includes_fixed_only_currencies() {
        let mut ctx = DisplayContext::new();
        // Only a fixed override, no observed samples.
        ctx.set_fixed_precision("BTC", 8);
        let cs: Vec<&str> = ctx.currencies().collect();
        assert_eq!(cs, vec!["BTC"]);
    }

    #[test]
    fn test_histogram_returns_ascending_pairs() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD"); // 2dp × 5
        }
        for _ in 0..2 {
            ctx.update(dec!(1.234), "USD"); // 3dp × 2
        }
        ctx.update(dec!(100), "USD"); // 0dp × 1
        let h = ctx.histogram("USD");
        // Ascending dp order, full counts preserved.
        assert_eq!(h, vec![(0, 1), (2, 5), (3, 2)]);
    }

    #[test]
    fn test_histogram_empty_for_unknown_currency() {
        let ctx = DisplayContext::new();
        assert!(ctx.histogram("XYZ").is_empty());
    }

    #[test]
    fn test_precision_under_does_not_mutate_active_policy() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(1.234), "USD");
        // Active policy is MostCommon; mode = 0.
        assert_eq!(ctx.get_precision("USD"), Some(0));
        // Querying under Maximum returns 3 — without changing active.
        assert_eq!(ctx.precision_under("USD", Precision::Maximum), Some(3));
        // Active policy unchanged after the introspection call.
        assert_eq!(ctx.precision(), Precision::MostCommon);
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_precision_under_returns_zero_when_fixed_is_zero() {
        // `set_fixed_precision(c, 0)` is a legitimate setting (forces a
        // currency to render as integer). Both policies must return Some(0)
        // — not None, not the inferred precision.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "JPY"); // inferred mode = 3
        ctx.set_fixed_precision("JPY", 0); // user wants integer JPY
        assert_eq!(ctx.precision_under("JPY", Precision::MostCommon), Some(0));
        assert_eq!(ctx.precision_under("JPY", Precision::Maximum), Some(0));
        assert_eq!(ctx.get_precision("JPY"), Some(0));
    }

    #[test]
    fn test_precision_under_respects_fixed_override() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        // Both policies see the fixed override, regardless.
        assert_eq!(ctx.precision_under("USD", Precision::MostCommon), Some(2));
        assert_eq!(ctx.precision_under("USD", Precision::Maximum), Some(2));
    }

    #[test]
    fn test_has_fixed_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        assert!(!ctx.has_fixed_precision("USD"));
        ctx.set_fixed_precision("USD", 2);
        assert!(ctx.has_fixed_precision("USD"));
    }

    #[test]
    fn test_quantize_pads_scale_upward() {
        // Pinned because `Decimal::round_dp(dp)` only rounds *down* — it
        // doesn't pad scale upward. Pre-fix, quantize(150.67, "USD") with
        // USD precision=4 returned 150.67 (scale 2), which broke the
        // bean-query parity for column-level dist tracking.
        let mut ctx = DisplayContext::new();
        for _ in 0..10 {
            ctx.update(dec!(0.0400), "USD"); // 10×4dp samples → mode=4
        }
        for _ in 0..3 {
            ctx.update(dec!(150.67), "USD"); // 3×2dp samples
        }
        // Mode is 4 (ten 4dp samples win).
        assert_eq!(ctx.get_precision("USD"), Some(4));
        // Quantize must produce a Decimal with scale exactly 4, not 2.
        let q = ctx.quantize(dec!(150.67), "USD");
        assert_eq!(q.scale(), 4);
        assert_eq!(q.to_string(), "150.6700");
    }

    #[test]
    fn test_format_with_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100), "USD");
        ctx.update(dec!(50.25), "USD");

        // 1×0dp + 1×2dp → mode tie-breaks to the larger (2dp), so format
        // uses 2 fractional digits. (See test_mode_tie_break_favors_larger_dp.)
        assert_eq!(ctx.format(dec!(100), "USD"), "100.00");
        assert_eq!(ctx.format(dec!(50.25), "USD"), "50.25");
        assert_eq!(ctx.format(dec!(7.5), "USD"), "7.50");
    }

    /// Issue #1103: when the value's intrinsic scale exceeds the
    /// currency's tracked precision, render at the value's scale
    /// rather than quantizing down. Matches bean-query: a
    /// `SUM(number)` over a fixture with high-precision arithmetic
    /// (cost-spec interpolation residuals, manual high-dp postings)
    /// produces a Decimal whose scale we MUST preserve to align with
    /// Python's `decimal` representation. The currency hint only ever
    /// PADS UP from a shorter scale; it never rounds DOWN from a
    /// longer one.
    #[test]
    fn test_format_preserves_value_scale_above_tracked_precision() {
        let mut ctx = DisplayContext::new();
        // USD tracked at 2dp (mode of two 2dp observations).
        ctx.update(dec!(100.00), "USD");
        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Value scale > tracked dp → preserve value scale (no round-down).
        assert_eq!(ctx.format(dec!(1.234), "USD"), "1.234");
        assert_eq!(ctx.format(dec!(-1202.00896), "USD"), "-1202.00896");
        assert_eq!(ctx.format(dec!(0.00000), "USD"), "0.00000");

        // Value scale ≤ tracked dp → pad up (unchanged from #988 fix).
        assert_eq!(ctx.format(dec!(7.5), "USD"), "7.50");
        assert_eq!(ctx.format(dec!(0), "USD"), "0.00");
    }

    /// Pins the post-#1112 fix: `format` and `format_amount` must NOT share
    /// rounding behavior.
    ///
    /// `format` (used for scalar `Value::Number`) preserves the Decimal's
    /// arithmetic scale — matches Python `DecimalRenderer`. `format_amount`
    /// (used for Amounts/Positions/Inventory) quantizes to the currency's
    /// tracked dp — matches Python `AmountRenderer`. Conflating them is
    /// what caused the 7pp BQL compat regression on main since #1106.
    #[test]
    fn test_format_vs_format_amount_split_semantics() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100.00), "USD");
        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // `format`: scalar Number → preserve arithmetic scale (over and under).
        assert_eq!(ctx.format(dec!(-1202.00896), "USD"), "-1202.00896");
        assert_eq!(ctx.format(dec!(7.5), "USD"), "7.50");

        // `format_amount`: Amount → quantize to tracked dp (over and under).
        assert_eq!(ctx.format_amount(dec!(-1202.00896), "USD"), "-1202.01 USD");
        assert_eq!(ctx.format_amount(dec!(7.5), "USD"), "7.50 USD");
        // Cost-spec interpolation can produce 26-digit per-unit values; the
        // Amount renderer must clamp those to the currency's display dp.
        assert_eq!(
            ctx.format_amount(dec!(170.16449234259784458309699376), "USD"),
            "170.16 USD"
        );

        // `format_amount_number`: same quantize semantics, no currency suffix.
        assert_eq!(
            ctx.format_amount_number(dec!(-1202.00896), "USD"),
            "-1202.01"
        );
        assert_eq!(ctx.format_amount_number(dec!(7.5), "USD"), "7.50");
    }

    /// Untracked currencies fall through to natural rendering in both
    /// `format` and `format_amount`. Trailing zeros are stripped because
    /// there's no display-precision target to pad against.
    #[test]
    fn test_format_amount_untracked_currency_uses_natural_scale() {
        let ctx = DisplayContext::new();
        // No prior `update` calls — get_precision("USD") returns None.
        assert_eq!(ctx.format_amount(dec!(170.164), "USD"), "170.164 USD");
        assert_eq!(ctx.format_amount(dec!(7.5), "USD"), "7.5 USD");
        assert_eq!(ctx.format_amount(dec!(100), "USD"), "100 USD");
    }

    #[test]
    fn test_format_unknown_currency() {
        let ctx = DisplayContext::new();

        // Unknown currency uses natural formatting
        assert_eq!(ctx.format(dec!(100), "EUR"), "100");
        assert_eq!(ctx.format(dec!(50.25), "EUR"), "50.25");
    }

    #[test]
    fn test_fixed_precision_override() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100), "USD");
        ctx.update(dec!(50.25), "USD");

        // Inferred precision is 2
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Set fixed precision to 4
        ctx.set_fixed_precision("USD", 4);
        assert_eq!(ctx.get_precision("USD"), Some(4));

        // Formatting uses fixed precision
        assert_eq!(ctx.format(dec!(100), "USD"), "100.0000");
    }

    // ===== Precision policy tests =====

    #[test]
    fn test_mode_picks_most_common_dp() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD"); // 2dp × 5
        }
        for _ in 0..2 {
            ctx.update(dec!(1.234), "USD"); // 3dp × 2
        }
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_mode_tie_break_favors_larger_dp() {
        // Pins Python's `Distribution.mode()` tie-break: when counts tie,
        // the LARGEST dp wins. Python iterates sorted-ascending with `>=`
        // (in beancount/core/distribution.py), keeping the last equal
        // entry. We match by iterating the BTreeMap ascending with `>=`.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // 2dp × 1
        ctx.update(dec!(1.234), "USD"); // 3dp × 1
        ctx.update(dec!(1.2345), "USD"); // 4dp × 1
        assert_eq!(ctx.get_precision("USD"), Some(4));
    }

    #[test]
    fn test_mode_outlier_does_not_dominate() {
        // The bean-query parity case: 5x integer + 1x 28dp price annotation
        // → mode = 0dp, NOT 28. Pre-fix rledger returned 28 (the max);
        // post-fix returns 0 to match bean-query's MOST_COMMON default.
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(0.0000000000000000000000000001), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_switching_to_maximum_returns_max() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(1.234567), "USD");
        // Default MostCommon: integer mode wins
        assert_eq!(ctx.get_precision("USD"), Some(0));
        // Switch policy to Maximum: the single 6dp sample wins
        ctx.set_precision(Precision::Maximum);
        assert_eq!(ctx.get_precision("USD"), Some(6));
        // Switch back: mode again
        ctx.set_precision(Precision::MostCommon);
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_fixed_precision_overrides_both_policies() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        assert_eq!(ctx.get_precision("USD"), Some(2));
        // Maximum policy still respects the fixed override
        ctx.set_precision(Precision::Maximum);
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_update_from_merges_distributions_not_just_max() {
        // Pre-fix: update_from took max(self.max, other.max) per currency,
        // collapsing distributions. Post-fix: merges histograms so the mode
        // reflects the union of frequencies. Without this, a column ctx
        // inheriting from a ledger ctx would only see the ledger's MAX
        // value, defeating the whole MostCommon design.
        let mut a = DisplayContext::new();
        for _ in 0..5 {
            a.update(dec!(1.23), "USD"); // 2dp × 5
        }

        let mut b = DisplayContext::new();
        for _ in 0..10 {
            b.update(dec!(1.234), "USD"); // 3dp × 10
        }

        a.update_from(&b);
        // After merge: 5×2dp + 10×3dp → mode = 3dp
        assert_eq!(a.get_precision("USD"), Some(3));
    }

    #[test]
    fn test_update_from_is_not_idempotent_under_add_merge() {
        // Pin the semantics that triggered Copilot's review on PR #986:
        // since update_from now ADDS counts (not max-merges), calling it
        // multiple times multiplies the source's contribution. This is
        // why the BQL renderer must guard against repeated inheritance
        // per row (see crates/rustledger/src/cmd/query/output.rs).
        let mut src = DisplayContext::new();
        for _ in 0..10 {
            src.update(dec!(1.23), "USD"); // 2dp × 10
        }

        let mut dst1 = DisplayContext::new();
        dst1.update_from(&src);
        // After 1 merge: 10×2dp.
        assert_eq!(dst1.histogram("USD"), vec![(2, 10)]);

        let mut dst2 = DisplayContext::new();
        dst2.update_from(&src);
        dst2.update_from(&src);
        // After 2 merges: 20×2dp — counts compounded.
        assert_eq!(dst2.histogram("USD"), vec![(2, 20)]);
    }

    #[test]
    fn test_update_from_does_not_propagate_precision_policy() {
        // Policy is a property of the consumer, not the data. A column ctx
        // that opted into Maximum shouldn't have its policy clobbered by
        // a ledger ctx that uses the MostCommon default.
        let mut ledger = DisplayContext::new();
        // ledger uses default MostCommon
        ledger.update(dec!(1.23), "USD");

        let mut col = DisplayContext::new();
        col.set_precision(Precision::Maximum);
        col.update_from(&ledger);

        assert_eq!(col.precision(), Precision::Maximum);
    }

    #[test]
    fn test_render_commas() {
        let mut ctx = DisplayContext::new();
        ctx.set_render_commas(true);
        ctx.update(dec!(1234567.89), "USD");

        assert_eq!(ctx.format(dec!(1234567.89), "USD"), "1,234,567.89");
        assert_eq!(ctx.format(dec!(1000), "USD"), "1,000.00");
    }

    #[test]
    fn test_add_commas() {
        assert_eq!(DisplayContext::add_commas("1234567"), "1,234,567");
        assert_eq!(DisplayContext::add_commas("1234567.89"), "1,234,567.89");
        assert_eq!(DisplayContext::add_commas("-1234567.89"), "-1,234,567.89");
        assert_eq!(DisplayContext::add_commas("123"), "123");
        assert_eq!(DisplayContext::add_commas("1"), "1");
    }

    #[test]
    fn test_update_from() {
        let mut ctx1 = DisplayContext::new();
        ctx1.update(dec!(100), "USD");

        let mut ctx2 = DisplayContext::new();
        ctx2.update(dec!(50.25), "USD");
        ctx2.update(dec!(1.5), "EUR");

        ctx1.update_from(&ctx2);

        assert_eq!(ctx1.get_precision("USD"), Some(2));
        assert_eq!(ctx1.get_precision("EUR"), Some(1));
    }

    #[test]
    fn test_update_from_propagates_fixed_precisions_and_render_commas() {
        // Copilot review on PR #961: previously update_from only merged
        // inferred precisions, so naked-decimal columns inheriting from a
        // ledger context with `option "display_precision"` would miss the
        // fixed overrides.
        let mut ledger = DisplayContext::new();
        ledger.update(dec!(1.234), "USD"); // inferred precision 3
        ledger.set_fixed_precision("USD", 2); // fixed override
        ledger.set_fixed_precision("BTC", 8);
        ledger.set_render_commas(true);

        let mut col = DisplayContext::new();
        col.update_from(&ledger);

        // Inferred precision distribution merged — under default
        // MostCommon policy, USD has only the single 3dp sample so
        // mode = 3.
        assert_eq!(
            col.distributions.get("USD").and_then(Distribution::mode),
            Some(3)
        );
        // Fixed overrides also propagated.
        assert_eq!(col.fixed_precisions.get("USD"), Some(&2));
        assert_eq!(col.fixed_precisions.get("BTC"), Some(&8));
        // get_precision still respects the fixed override.
        assert_eq!(col.get_precision("USD"), Some(2));
        assert_eq!(col.get_precision("BTC"), Some(8));
        // render_commas propagated.
        assert!(col.render_commas);
    }

    #[test]
    fn test_update_from_preserves_self_fixed_overrides() {
        // If self already has a fixed override for a currency, update_from
        // shouldn't clobber it with the other's value. Self wins.
        let mut ledger = DisplayContext::new();
        ledger.set_fixed_precision("USD", 2);

        let mut col = DisplayContext::new();
        col.set_fixed_precision("USD", 4); // self's override
        col.update_from(&ledger);

        assert_eq!(col.fixed_precisions.get("USD"), Some(&4));
    }

    #[test]
    fn test_default_precision_respects_fixed_override_lower_than_inferred() {
        // Copilot review on PR #961: if USD has inferred=4 but fixed=2,
        // the user said "render USD with 2 decimals" — default_precision
        // for naked Decimals must respect that, not fall back to the
        // inferred max (4).
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.2345), "USD"); // inferred 4
        ctx.set_fixed_precision("USD", 2); // fixed override

        // get_precision returns the effective precision (fixed wins).
        assert_eq!(ctx.get_precision("USD"), Some(2));
        // default_precision must use the same effective view, not raw max.
        assert_eq!(ctx.default_precision(), 2);
    }

    #[test]
    fn test_default_precision_takes_max_across_currencies_with_overrides() {
        // EUR fixed=4 wins over USD fixed=2 → default = 4.
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("USD", 2);
        ctx.set_fixed_precision("EUR", 4);

        assert_eq!(ctx.default_precision(), 4);
    }

    #[test]
    fn test_format_amount() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(50.25), "USD");

        assert_eq!(ctx.format_amount(dec!(100), "USD"), "100.00 USD");
    }

    #[test]
    fn test_default_precision_picks_max_across_currencies() {
        // Issue #954: bare Decimals (e.g. SUM(number) result) need a default
        // precision matching what bean-query uses — the max precision across
        // every known currency.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // precision 2
        ctx.update(dec!(1.2345), "EUR"); // precision 4
        ctx.update(dec!(0.5), "GBP"); // precision 1

        assert_eq!(ctx.default_precision(), 4);
    }

    #[test]
    fn test_default_precision_includes_fixed_overrides() {
        // Fixed precision (from `option "display_precision"`) should also
        // contribute to the max.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_fixed_precision("BTC", 8);

        assert_eq!(ctx.default_precision(), 8);
    }

    #[test]
    fn test_default_precision_empty_context_is_zero() {
        let ctx = DisplayContext::new();
        assert_eq!(ctx.default_precision(), 0);
    }

    #[test]
    fn test_format_default_does_not_pad_scale_zero_to_column_precision() {
        // Inverted from the pre-fix `test_format_default_pads_to_max_precision`.
        //
        // Python `bean-query`'s `DecimalRenderer.format` calls
        // `str(value)` — no padding step. A `Decimal(0)` (scale 0)
        // renders as `"0"` regardless of what other cells in the
        // column look like; a `Decimal(0.0000)` renders as `"0.0000"`.
        //
        // We used to pad scale-0 values to the column's default
        // precision as an over-fit for #954, but that broke mixed-scale
        // columns (issue #1051's `cost-basis-fields` cases on fixtures
        // like `tests_test_inputs_missing_prices.beancount`, where a
        // scale-0 `cost_number=1000` was rendered as
        // `"1000.0000000000000000000000000"` because the column's other
        // row had a scale-25 cost from a `{{total}}`-form spec). The
        // #954 case (`SUM(0.00 + -0.00)`) still renders `"0.00"`
        // correctly because the aggregator preserves the inputs' max
        // scale — `to_string()` on the resulting `Decimal('0.00')` is
        // `"0.00"` without any padding.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.update(dec!(1.2345), "EUR");
        assert_eq!(ctx.format_default(dec!(0)), "0");
        assert_eq!(ctx.format_default(dec!(100)), "100");
    }

    #[test]
    fn test_format_default_preserves_natural_scale_for_overprecise_values() {
        // Updated post-#985-follow-up: format_default no longer ROUNDS to
        // a uniform precision. Instead it preserves each value's natural
        // scale (matches Python `bean-query`'s DecimalRenderer, which
        // formats with `{value:<width}` — no precision specifier). That
        // means 1.235 prints as "1.235", NOT rounded to "1.24".
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        assert_eq!(ctx.format_default(dec!(1.235)), "1.235");
    }

    #[test]
    fn test_format_default_empty_context_natural() {
        let ctx = DisplayContext::new();
        // No tracked precision → integer-like rendering (no padding,
        // no rounding, value's natural scale).
        assert_eq!(ctx.format_default(dec!(42)), "42");
        // Fractional values keep their natural scale.
        assert_eq!(ctx.format_default(dec!(1.5)), "1.5");
    }

    #[test]
    fn test_format_default_renders_commas() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_render_commas(true);

        assert_eq!(ctx.format_default(dec!(1234567.89)), "1,234,567.89");
    }

    /// Issue #1051 example 4: `rust_decimal`'s 96-bit mantissa can land
    /// at 29 sig figs from divisions like `300 / 1.763`, where Python's
    /// default `Decimal` context (`getcontext().prec = 28`) clamps the
    /// same operation at 28. Without the cap in `format_default`, BQL's
    /// `cost_number` rendering would show 29 digits where bean-query
    /// shows 28, surfacing as a `cost-basis-fields` mismatch on every
    /// fixture with computed (`{{total}}`-form) cost specs.
    #[test]
    fn test_format_default_caps_significant_digits_at_28() {
        let ctx = DisplayContext::new();
        // 300 / 1.763 in rust_decimal lands at 29 sig figs:
        // 170.16449234259784458309699376 (3 integer + 26 fractional).
        let v = Decimal::from_str_exact("170.16449234259784458309699376").unwrap();
        assert_eq!(v.scale(), 26, "test setup: input has scale 26");
        // After capping to 28 sig figs total, the fractional scale drops
        // by 1 to 25 — matching Python's `Decimal('300') / Decimal('1.763')
        // = Decimal('170.1644923425978445830969938')`.
        assert_eq!(
            ctx.format_default(v),
            "170.1644923425978445830969938",
            "should cap at 28 sig figs (3 integer + 25 fractional)"
        );
    }

    #[test]
    fn test_format_default_28_digit_or_fewer_passes_through_unchanged() {
        let ctx = DisplayContext::new();
        // Fits within 28 — no rounding. Don't accidentally re-quantize
        // values that are already at the right precision.
        assert_eq!(ctx.format_default(dec!(170.16449)), "170.16449");
        // Edge case: exactly 28 digits.
        let v = Decimal::from_str_exact("1.234567890123456789012345678").unwrap();
        assert_eq!(v.scale(), 27);
        assert_eq!(
            ctx.format_default(v),
            "1.234567890123456789012345678",
            "value at exactly 28 sig figs must pass through unchanged"
        );
    }

    #[test]
    fn test_format_default_cap_preserves_sign_and_integer_part() {
        let ctx = DisplayContext::new();
        // Negative value > 28 sig figs: sign and integer part survive
        // the rescale; only fractional digits get truncated.
        let v = Decimal::from_str_exact("-1234.5678901234567890123456789").unwrap();
        // mantissa has 29 digits; capping to 28 drops the last fractional digit.
        assert_eq!(
            ctx.format_default(v),
            "-1234.567890123456789012345679",
            "negative + integer part preserved; fractional rounded half-even"
        );
    }

    /// Integer-only excess: a 29-digit scale-0 Decimal must actually
    /// round (to nearest 10), not pass through unchanged. Pre-fix
    /// `cap_significant_digits` did `saturating_sub` on the scale
    /// which clamped to 0, and `round_dp_with_strategy(0, …)` left
    /// the integer alone — contradicting the doc comment. Caught by
    /// Copilot review on PR #1064.
    #[test]
    fn test_format_default_caps_integer_only_excess() {
        let ctx = DisplayContext::new();
        // 29 digits, scale 0. Cap to 28 → round to nearest 10.
        // 12345678901234567890123456789 / 10 = 1234567890123456789012345678.9
        // rounded half-even at 0dp = 1234567890123456789012345679
        // × 10 = 12345678901234567890123456790
        let v = Decimal::from_str_exact("12345678901234567890123456789").unwrap();
        assert_eq!(v.scale(), 0);
        assert_eq!(
            ctx.format_default(v),
            "12345678901234567890123456790",
            "29-digit integer must round to nearest 10 (28 sig figs), \
             trailing 0 marks the rounded position"
        );
    }

    /// Zero values render at their intrinsic scale and skip the
    /// significant-digit cap (since `mantissa()` is 0). Guards against
    /// `checked_ilog10(0) → None` regressing into an off-by-one or
    /// accidental cap. Together with
    /// `test_format_default_does_not_pad_scale_zero_to_column_precision`
    /// this locks in bean-query parity for both `Decimal(0)` and
    /// `Decimal(0.00)` shapes.
    #[test]
    fn test_format_default_zero_preserves_intrinsic_scale() {
        let ctx = DisplayContext::new();
        assert_eq!(ctx.format_default(dec!(0)), "0", "Decimal(0) → \"0\"");
        assert_eq!(
            ctx.format_default(dec!(0.00)),
            "0.00",
            "Decimal(0.00) → \"0.00\" — the SUM-of-scale-2-zeros case from #954"
        );
        assert_eq!(
            ctx.format_default(dec!(-0.0000)),
            "0.0000",
            "Decimal(-0.0000) — rust_decimal canonicalizes negative zero"
        );
    }

    /// The canonical builder's three-stage precedence (#1766): amount-scan
    /// inference < `display_precision` option < commodity `precision:`
    /// metadata. The loader and the FFI component's `session.format` both
    /// call this — the precedence must not depend on which one.
    #[test]
    fn from_directives_precedence_inferred_option_commodity() {
        use crate::{Amount, Balance, Commodity, Directive, MetaValue};
        let d = crate::naive_date(2024, 1, 1).unwrap();
        let mut usd_commodity = Commodity::new(d, "USD");
        usd_commodity
            .meta
            .insert("precision".to_string(), MetaValue::Int(4));
        let dirs = [
            // USD: 2dp twice, 0dp once -> inferred mode 2.
            Directive::Balance(Balance::new(d, "Assets:A", Amount::new(dec!(1.50), "USD"))),
            Directive::Balance(Balance::new(d, "Assets:B", Amount::new(dec!(2.25), "USD"))),
            Directive::Balance(Balance::new(d, "Assets:C", Amount::new(dec!(3), "USD"))),
            // EUR: single 1dp observation -> inferred 1.
            Directive::Balance(Balance::new(d, "Assets:D", Amount::new(dec!(9.5), "EUR"))),
            // JPY: never observed as an amount, no fixed override.
            Directive::Commodity(usd_commodity),
        ];

        // No overrides: pure inference.
        let ctx = DisplayContext::from_directives(dirs.iter().take(4), std::iter::empty(), false);
        assert_eq!(ctx.get_precision("USD"), Some(2), "mode of {{2,2,0}}dp");
        assert_eq!(ctx.get_precision("EUR"), Some(1));
        assert_eq!(
            ctx.resolved_precisions(),
            vec![("EUR".to_string(), 1), ("USD".to_string(), 2)],
            "the wire export carries inferred precisions too — embedders \
             render from it without re-deriving inference"
        );
        assert_eq!(
            ctx.get_precision("JPY"),
            None,
            "unseen currency stays untracked"
        );

        // Option override beats inference; commodity metadata beats both.
        let ctx = DisplayContext::from_directives(dirs.iter(), [("EUR", 3), ("USD", 5)], false);
        assert_eq!(
            ctx.get_precision("USD"),
            Some(4),
            "commodity `precision: 4` metadata wins over the option's 5"
        );
        assert_eq!(
            ctx.get_precision("EUR"),
            Some(3),
            "option override wins over the inferred 1"
        );
        assert_eq!(
            ctx.resolved_precisions(),
            vec![("EUR".to_string(), 3), ("USD".to_string(), 4)],
            "the wire export reflects the fixed-table precedence"
        );
    }
}

#[cfg(test)]
mod custom_directive_precision_tests {
    use super::*;
    use crate::{Amount, Custom, Directive, MetaValue, Posting, Transaction, naive_date};
    use rust_decimal_macros::dec;

    fn custom_with_amount(day: u32, amount: Amount) -> Directive {
        Directive::Custom(
            Custom::new(naive_date(2024, 1, day).unwrap(), "budget")
                .with_value(MetaValue::Amount(amount)),
        )
    }

    /// Amounts inside `custom` directives do NOT inform display precision.
    ///
    /// The decimal count in a budget line is a stylistic choice about the
    /// declaration; a budget report's figure is pro-rated and repeating by
    /// construction. Inferring from the declaration rounded a 0.22580645 BTC
    /// accrual to `0.2`. A consumer needing to render a currency this context
    /// has never seen picks its own precision instead.
    #[test]
    fn custom_amounts_do_not_inform_precision() {
        let directives = [custom_with_amount(1, Amount::new(dec!(0.5), "BTC"))];
        let ctx = DisplayContext::from_directives(directives.iter(), std::iter::empty(), false);
        assert_eq!(ctx.get_precision("BTC"), None);
        assert!(
            !ctx.currencies().any(|c| c == "BTC"),
            "a currency seen only in metadata must not enter the ledger's \
             currency list, which crosses the FFI"
        );
    }

    /// And they certainly must not outvote postings: three 4 dp budget lines
    /// against one 2 dp posting once moved USD's mode to 4 dp, silently
    /// re-rendering every report in the CLI.
    #[test]
    fn custom_amounts_do_not_outvote_postings() {
        let directives = [
            custom_with_amount(1, Amount::new(dec!(400.0000), "USD")),
            custom_with_amount(2, Amount::new(dec!(100.0000), "USD")),
            custom_with_amount(3, Amount::new(dec!(50.0000), "USD")),
            Directive::Transaction(
                Transaction::new(naive_date(2024, 2, 1).unwrap(), "a").with_synthesized_posting(
                    Posting::new("Expenses:Food", Amount::new(dec!(10.00), "USD")),
                ),
            ),
        ];
        let ctx = DisplayContext::from_directives(directives.iter(), std::iter::empty(), false);
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    /// The surface rule, stated once and asserted here so a new
    /// `OutputSurface` variant cannot quietly default to rendering separators
    /// (#1892).
    #[test]
    fn only_machine_surfaces_suppress_thousands_separators() {
        assert!(OutputSurface::Human.renders_thousands_separators());
        assert!(
            !OutputSurface::Machine.renders_thousands_separators(),
            "CSV/JSON consumers have no grammar admitting a separator; this \
             suppression outranks any ledger or per-commodity declaration"
        );
        assert!(
            OutputSurface::LedgerText.renders_thousands_separators(),
            "grouped numerals are Beancount syntax, so every conforming \
             reader accepts them — `format --ledger` groups and `query \
             --format beancount` must agree with it (#1896)"
        );
    }

    /// A commodity's own `render_commas` declaration governs report and query
    /// text, not just `rledger format`.
    ///
    /// Review catch on #1896: the per-commodity overrides were parsed and
    /// stored but only the CST formatter consulted them, so `format` and
    /// `format_quantized` — which have the currency right there in the
    /// signature — still asked the ledger-wide flag. A commodity opting out of
    /// grouping was silently grouped in every report.
    #[test]
    fn a_commoditys_own_declaration_governs_report_text() {
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("USD", 2);
        ctx.set_fixed_precision("IQD", 2);
        ctx.set_render_commas(true);
        ctx.set_render_commas_for("USD", false);

        assert_eq!(
            ctx.format(Decimal::from_str_exact("1234567.89").unwrap(), "USD"),
            "1234567.89",
            "USD declared render_commas: FALSE — a report must honor it"
        );
        assert_eq!(
            ctx.format(Decimal::from_str_exact("1234567.89").unwrap(), "IQD"),
            "1,234,567.89",
            "IQD declared nothing and takes the ledger-wide default"
        );
        // The ledger-text path (`query --format beancount`) resolves per
        // currency too, so the two surfaces cannot disagree.
        assert_eq!(
            ctx.format_quantized(Decimal::from_str_exact("1234567.89").unwrap(), "USD"),
            "1234567.89"
        );
        assert_eq!(
            ctx.format_quantized(Decimal::from_str_exact("1234567.89").unwrap(), "IQD"),
            "1,234,567.89"
        );

        // And the inverse tier: nothing global, one commodity opting IN.
        let mut opted_in = DisplayContext::new();
        opted_in.set_fixed_precision("IQD", 2);
        opted_in.set_render_commas_for("IQD", true);
        assert_eq!(
            opted_in.format(Decimal::from_str_exact("1234567.89").unwrap(), "IQD"),
            "1,234,567.89"
        );
    }

    /// Suppressing separators for a machine surface must clear the
    /// per-commodity opt-ins too, not just the ledger-wide flag.
    ///
    /// The borrow fast path used to test `render_commas` alone. A ledger whose
    /// global flag is off but which has one commodity declaring
    /// `render_commas: TRUE` would take that path and hand the CSV writer a
    /// context that still groups that commodity — `Decimal(field)` breaks on
    /// the result.
    #[test]
    fn machine_surfaces_suppress_per_commodity_opt_ins() {
        use std::borrow::Cow;

        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("IQD", 2);
        ctx.set_render_commas_for("IQD", true); // global stays FALSE

        assert!(
            !ctx.render_commas(),
            "precondition: nothing is set ledger-wide"
        );
        assert!(ctx.renders_any_commas(), "but one commodity opts in");

        let machine = ctx.for_surface(OutputSurface::Machine);
        assert!(
            matches!(machine, Cow::Owned(_)),
            "the global flag is off, but an override still has to be cleared"
        );
        assert!(!machine.render_commas_for("IQD"));
        assert_eq!(
            machine.format(Decimal::from_str_exact("1234567.89").unwrap(), "IQD"),
            "1234567.89",
            "a CSV/JSON consumer has no grammar for separators"
        );

        // Human surface keeps the opt-in, and still borrows.
        let human = ctx.for_surface(OutputSurface::Human);
        assert!(matches!(human, Cow::Borrowed(_)));
        assert_eq!(
            human.format(Decimal::from_str_exact("1234567.89").unwrap(), "IQD"),
            "1,234,567.89"
        );
    }

    /// `for_surface` avoids cloning whenever the flag does not have to change.
    ///
    /// The clone carries the per-currency histograms, and the JSON writer
    /// ignores the context entirely, so paying for one on every query would be
    /// pure waste (review catch on #1893). The two cases that matter most are
    /// the cheap ones: a ledger that never set `render_commas`, and any
    /// human-facing surface.
    #[test]
    fn for_surface_borrows_unless_the_flag_must_change() {
        use std::borrow::Cow;

        let mut plain = DisplayContext::new();
        plain.set_fixed_precision("USD", 2);
        assert!(
            matches!(plain.for_surface(OutputSurface::Machine), Cow::Borrowed(_)),
            "a ledger without render_commas never needs a clone"
        );

        let mut commas = DisplayContext::new();
        commas.set_render_commas(true);
        assert!(
            matches!(commas.for_surface(OutputSurface::Human), Cow::Borrowed(_)),
            "a human surface keeps the flag, so no clone"
        );
        assert!(
            matches!(commas.for_surface(OutputSurface::Machine), Cow::Owned(_)),
            "only actually suppressing separators clones"
        );
    }

    /// `for_surface` narrows ONLY the separator flag — precision is a property
    /// of the data and must survive on every surface.
    #[test]
    fn for_surface_narrows_separators_but_keeps_precision() {
        let mut ctx = DisplayContext::new();
        ctx.set_render_commas(true);
        ctx.set_fixed_precision("USD", 2);

        let human = ctx.for_surface(OutputSurface::Human);
        let machine = ctx.for_surface(OutputSurface::Machine);
        assert!(human.render_commas());
        assert!(!machine.render_commas());
        assert_eq!(
            machine.format_amount_number(rust_decimal_macros::dec!(1234.5), "USD"),
            human
                .format_amount_number(rust_decimal_macros::dec!(1234.5), "USD")
                .replace(',', ""),
            "the two differ ONLY by separators, never by precision"
        );

        // A ledger that never asked for separators is unaffected either way.
        let mut plain = DisplayContext::new();
        plain.set_fixed_precision("USD", 2);
        assert!(!plain.for_surface(OutputSurface::Human).render_commas());
    }
}
