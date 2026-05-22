#![no_main]
//! Fuzz target for the booking engine.
//!
//! Generates structured transaction inputs with varying cost specs,
//! booking methods, and inventory states to find panics, overflows,
//! or other crashes in the booking and interpolation logic.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rust_decimal::Decimal;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookedCost, BookingMethod, CostNumber, CostSpec, IncompleteAmount, NaiveDate, Posting,
    Transaction,
};

/// Fuzzer-friendly booking method selector.
#[derive(Debug, Arbitrary)]
enum FuzzBookingMethod {
    Strict,
    StrictWithSize,
    Fifo,
    Lifo,
    Hifo,
    Average,
    None,
}

impl From<FuzzBookingMethod> for BookingMethod {
    fn from(m: FuzzBookingMethod) -> Self {
        match m {
            FuzzBookingMethod::Strict => BookingMethod::Strict,
            FuzzBookingMethod::StrictWithSize => BookingMethod::StrictWithSize,
            FuzzBookingMethod::Fifo => BookingMethod::Fifo,
            FuzzBookingMethod::Lifo => BookingMethod::Lifo,
            FuzzBookingMethod::Hifo => BookingMethod::Hifo,
            FuzzBookingMethod::Average => BookingMethod::Average,
            FuzzBookingMethod::None => BookingMethod::None,
        }
    }
}

/// Fuzzer-friendly cost-number variant. Single tagged enum mirroring
/// the host `CostNumber`, so the fuzzer can only produce inputs the
/// type system allows (no silent both-set state from parallel
/// `Option<i32>` axes).
#[derive(Debug, Arbitrary)]
enum FuzzCostNumber {
    /// `{value USD}` per-unit shape.
    PerUnit { value_cents: i32 },
    /// `{{value USD}}` total shape.
    Total { value_cents: i32 },
    /// Post-booking shape with both halves. The fuzzer can supply
    /// inconsistent pairs (per_unit * |units| ≠ total) to stress the
    /// trust-boundary code in `from_wrapper` / FFI input that must
    /// reject or coerce them rather than silently inject garbage.
    PerUnitFromTotal {
        per_unit_cents: i32,
        total_cents: i32,
    },
}

/// Fuzzer-friendly cost spec configuration.
#[derive(Debug, Arbitrary)]
struct FuzzCostSpec {
    /// Cost number variant (none → bare `{}` cost spec).
    number: Option<FuzzCostNumber>,
    /// Whether to use a cost currency
    has_currency: bool,
    /// Whether to merge lots (average cost)
    merge: bool,
}

/// Fuzzer-friendly posting configuration.
#[derive(Debug, Arbitrary)]
struct FuzzPosting {
    /// Account index (0-4, maps to predefined accounts)
    account_idx: u8,
    /// Amount in cents (to keep decimals reasonable)
    amount_cents: i32,
    /// Currency index (0=USD, 1=EUR, 2=CORP)
    currency_idx: u8,
    /// Optional cost spec
    cost: Option<FuzzCostSpec>,
    /// Whether this posting has a missing amount (for interpolation)
    missing_amount: bool,
}

/// Fuzzer-friendly transaction with multiple postings.
#[derive(Debug, Arbitrary)]
struct FuzzTransaction {
    /// Booking method to use
    booking_method: FuzzBookingMethod,
    /// Year offset (2020-2025)
    year_offset: u8,
    /// Month (1-12)
    month: u8,
    /// Day (1-28)
    day: u8,
    /// Postings (2-8, filtered at runtime)
    postings: Vec<FuzzPosting>,
    /// Optional prior transactions to build inventory state
    prior_buys: Vec<FuzzPriorBuy>,
}

/// A prior buy transaction to populate inventory before the main transaction.
#[derive(Debug, Arbitrary)]
struct FuzzPriorBuy {
    /// Number of units to buy (whole units, not cents)
    units: u16,
    /// Cost per unit in cents
    cost_cents: u16,
    year_offset: u8,
}

const ACCOUNTS: &[&str] = &[
    "Assets:Stock",
    "Assets:Cash",
    "Expenses:Fees",
    "Income:Gains",
    "Equity:Opening",
];

const CURRENCIES: &[&str] = &["USD", "EUR", "CORP"];

fn make_date(year_offset: u8, month: u8, day: u8) -> NaiveDate {
    let year = 2020 + (year_offset % 6) as i32;
    let month = ((month % 12) + 1) as u32;
    let day = ((day % 28) + 1) as u32;
    rustledger_core::naive_date(year, month, day)
        .unwrap_or(rustledger_core::naive_date(2020, 1, 1).unwrap())
}

fn make_decimal(cents: i32) -> Decimal {
    Decimal::new(cents as i64, 2)
}

fuzz_target!(|input: FuzzTransaction| {
    // Need at least 2 postings for a meaningful transaction
    if input.postings.len() < 2 || input.postings.len() > 8 {
        return;
    }

    let method: BookingMethod = input.booking_method.into();
    let mut engine = BookingEngine::with_method(method);

    let date = make_date(input.year_offset, input.month, input.day);

    // Build prior inventory state with buy transactions
    for (i, buy) in input.prior_buys.iter().take(5).enumerate() {
        if buy.units == 0 || buy.cost_cents == 0 {
            continue;
        }
        let buy_date = make_date(buy.year_offset, 1, 1);
        let units = Decimal::new(buy.units as i64, 0);
        let cost = make_decimal(buy.cost_cents as i32);

        let posting = Posting::new("Assets:Stock", Amount::new(units, "CORP")).with_cost(
            CostSpec::empty()
                .with_number(CostNumber::PerUnit { value: cost })
                .with_currency("USD"),
        );
        let counter = Posting::new("Assets:Cash", Amount::new(-units * cost, "USD"));

        let txn = Transaction::new(buy_date, format!("Buy {i}"))
            .with_synthesized_posting(posting)
            .with_synthesized_posting(counter);

        // Ignore errors — we're building up state, some combos may fail
        if let Ok(result) = engine.book_and_interpolate(&txn) {
            engine.apply(&result.transaction);
        }
    }

    // Build the main transaction
    let mut txn = Transaction::new(date, "Fuzz transaction");

    for fuzz_posting in &input.postings {
        let account = ACCOUNTS[(fuzz_posting.account_idx as usize) % ACCOUNTS.len()];
        let currency = CURRENCIES[(fuzz_posting.currency_idx as usize) % CURRENCIES.len()];

        if fuzz_posting.missing_amount {
            // Posting with missing amount (for interpolation)
            let posting =
                Posting::with_incomplete(account, IncompleteAmount::CurrencyOnly(currency.into()));
            txn = txn.with_synthesized_posting(posting);
        } else {
            let amount = Amount::new(make_decimal(fuzz_posting.amount_cents), currency);
            let mut posting = Posting::new(account, amount);

            if let Some(ref cost) = fuzz_posting.cost {
                let mut spec = CostSpec::empty();
                if let Some(n) = &cost.number {
                    // Construct via the typed enum directly — the
                    // fuzzer's `Arbitrary` impl picks exactly one
                    // variant, so the both-set state simply can't
                    // appear here. PerUnitFromTotal can carry an
                    // inconsistent pair (per_unit * |units| ≠ total);
                    // that's intentional, to stress trust-boundary
                    // code in other crates that consume CostSpec.
                    let cn = match n {
                        FuzzCostNumber::PerUnit { value_cents } => CostNumber::PerUnit {
                            value: make_decimal(*value_cents),
                        },
                        FuzzCostNumber::Total { value_cents } => CostNumber::Total {
                            value: make_decimal(*value_cents),
                        },
                        FuzzCostNumber::PerUnitFromTotal {
                            per_unit_cents,
                            total_cents,
                        } => CostNumber::PerUnitFromTotal(
                            // `from_fuzz_unchecked` exists specifically
                            // for this case — the fuzzer deliberately
                            // generates inconsistent (per_unit, total)
                            // pairs to stress downstream consumers
                            // (residual math, format rendering,
                            // fingerprint hashing) that read
                            // `b.per_unit` and `b.total` without
                            // re-validating. Distinct from
                            // `from_archive_bytes_trusted` so grep
                            // tells trusted archive readers apart
                            // from fuzz pathological-input generators.
                            BookedCost::from_fuzz_unchecked(
                                make_decimal(*per_unit_cents),
                                make_decimal(*total_cents),
                            ),
                        ),
                    };
                    spec = spec.with_number(cn);
                }
                if cost.has_currency {
                    spec = spec.with_currency("USD");
                }
                if cost.merge {
                    spec = spec.with_merge();
                }
                posting = posting.with_cost(spec);
            }

            txn = txn.with_synthesized_posting(posting);
        }
    }

    // The booking engine must never panic, regardless of input.
    // Errors are expected and fine — panics are bugs.
    let _ = engine.book_and_interpolate(&txn);
});
