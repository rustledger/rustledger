#![no_main]
//! Fuzz target for the booking engine.
//!
//! Generates structured transaction inputs with varying cost specs,
//! booking methods, and inventory states to find panics, overflows,
//! or other crashes in the booking and interpolation logic.

use arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::fuzz_target;
use rust_decimal::Decimal;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookedCost, BookingMethod, CostNumber, CostSpec, IncompleteAmount, NaiveDate, Posting,
    Transaction,
};

/// A decimal drawn from the whole of `Decimal`'s domain.
///
/// Every money value in this target used to come from `i32` cents and every
/// unit count from a `u16`, so the largest quotient `total / |units|` it could
/// construct was about 2.1e7 -- while the panic in #2327 needed 7.9e28, some
/// 22 orders of magnitude away, and fractional units were unreachable
/// outright. The target says it looks for "panics, overflows, or other
/// crashes" and could not reach the overflows (#2340).
///
/// Most draws stay ordinary money. A corpus of nothing but extremes explores
/// the booking RULES badly -- lot matching, interpolation and tolerance need
/// plausible ledgers -- so roughly one draw in eight comes from the edges and
/// one in eight from anywhere in the domain.
#[derive(Debug, Clone, Copy)]
struct FuzzAmount(Decimal);

/// Values at and around the limits, where the arithmetic gives way.
///
/// `Decimal::MAX`, its negation, the smallest representable magnitude, and the
/// small integers that divide badly. A quotient of `MAX / 1e-28` is what an
/// unchecked division panics on.
///
/// Built from constructors rather than parsed from strings. A string table
/// needs a fallback for the parse, and a typo in one entry would then disable
/// that edge silently and forever -- the generator would keep reporting a
/// clean run it was no longer capable of dirtying.
fn edge_values() -> [Decimal; 9] {
    [
        Decimal::MAX,
        -Decimal::MAX,
        Decimal::new(1, 28),
        Decimal::new(-1, 28),
        Decimal::ZERO,
        Decimal::ONE,
        Decimal::NEGATIVE_ONE,
        Decimal::new(3, 0),
        Decimal::new(1, 1),
    ]
}

/// The mantissa `Decimal` actually has: 96 bits.
const MANTISSA_MASK: i128 = (1i128 << 96) - 1;

impl<'a> Arbitrary<'a> for FuzzAmount {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let value = match u8::arbitrary(u)? % 8 {
            0 => {
                let edges = edge_values();
                let pick = usize::from(u8::arbitrary(u)?) % edges.len();
                edges[pick]
            }
            // Anywhere in the domain: a full-width mantissa with any scale the
            // type allows. `try_from_i128_with_scale` rather than the
            // panicking constructor -- a generator that aborts the run is a
            // false finding, which is this target's worst outcome.
            //
            // The mantissa is MASKED to 96 bits first. Handing the function a
            // raw `i128` looks like "the whole domain" and is not: it is
            // representable with probability about 2^-31, measured at 0 of
            // 200,000 draws, so every draw fell back to ZERO and this arm
            // generated nothing at all. Masking makes it uniform over the
            // mantissa range, which is what the arm was written to do.
            1 => {
                let magnitude = i128::arbitrary(u)? & MANTISSA_MASK;
                let mantissa = if bool::arbitrary(u)? {
                    -magnitude
                } else {
                    magnitude
                };
                let scale = u32::from(u8::arbitrary(u)?) % 29;
                Decimal::try_from_i128_with_scale(mantissa, scale).unwrap_or(Decimal::ZERO)
            }
            // Ordinary money, which is what the target generated exclusively
            // before and still needs for the rules that are not about limits.
            _ => Decimal::new(i64::from(i32::arbitrary(u)?), 2),
        };
        Ok(Self(value))
    }
}

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
    PerUnit { value: FuzzAmount },
    /// `{{value USD}}` total shape.
    Total { value: FuzzAmount },
    /// Post-booking shape with both halves. The fuzzer can supply
    /// inconsistent pairs (per_unit * |units| ≠ total) to stress the
    /// trust-boundary code in `from_wrapper` / FFI input that must
    /// reject or coerce them rather than silently inject garbage.
    PerUnitFromTotal {
        per_unit: FuzzAmount,
        total: FuzzAmount,
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
    /// Posting amount, drawn from the whole domain (#2340).
    amount: FuzzAmount,
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
    /// Units to buy. A `Decimal`, not a `u16`: fractional lots are ordinary
    /// in real ledgers (`1.763 VIIIX {{300.00 USD}}`) and were unreachable
    /// here, so nothing involving them was ever generated (#2340).
    units: FuzzAmount,
    /// Cost per unit.
    cost: FuzzAmount,
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
        let (units, cost) = (buy.units.0, buy.cost.0);
        if units.is_zero() || cost.is_zero() {
            continue;
        }
        let buy_date = make_date(buy.year_offset, 1, 1);
        // Checked: the generator now reaches values whose product leaves the
        // range, and a bare `*` PANICS there -- in the harness, which would be
        // reported as a finding against the engine (#2340).
        // Negation is safe -- `Decimal`'s range is symmetric, `MIN == -MAX` --
        // so only the product needs checking.
        let Some(counter_amount) = units.checked_mul(cost).map(|v| -v) else {
            continue;
        };

        let posting = Posting::new("Assets:Stock", Amount::new(units, "CORP")).with_cost(
            CostSpec::empty()
                .with_number(CostNumber::PerUnit { value: cost })
                .with_currency("USD"),
        );
        let counter = Posting::new("Assets:Cash", Amount::new(counter_amount, "USD"));

        let txn = Transaction::new(buy_date, format!("Buy {i}"))
            .with_synthesized_posting(posting)
            .with_synthesized_posting(counter);

        // Ignore errors — we're building up state, some combos may fail.
        // That includes `apply`'s overflow error (#1863): the fuzzer generates
        // arbitrary units and costs, so an out-of-range product is a legitimate
        // input to explore past, not a crash. Unwrapping here would abort the
        // run and report a false finding — the opposite of this target's job.
        if let Ok(result) = engine.book_and_interpolate(&txn) {
            let _ = engine.apply(&result.transaction);
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
            let amount = Amount::new(fuzz_posting.amount.0, currency);
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
                        FuzzCostNumber::PerUnit { value } => {
                            CostNumber::PerUnit { value: value.0 }
                        }
                        FuzzCostNumber::Total { value } => CostNumber::Total { value: value.0 },
                        FuzzCostNumber::PerUnitFromTotal { per_unit, total } => {
                            CostNumber::PerUnitFromTotal(
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
                            BookedCost::from_fuzz_unchecked(per_unit.0, total.0),
                            )
                        }
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
