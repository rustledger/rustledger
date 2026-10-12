//! Validate that reducing postings use the average cost for accounts
//! opened with the NONE booking method.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::py_literal::{self, PyValue};
use super::utils::at_entry;
use bigdecimal::{BigDecimal, Signed, Zero};
use rustledger_core::decimal::to_bigdecimal;

/// Plugin that validates reducing postings against the running average cost
/// for accounts opened with the `NONE` booking method.
///
/// When an account is opened with `NONE` booking, the ledger author is responsible
/// for lot matching — there is no booker to enforce it. This plugin is a safety net
/// for that case: it verifies that the cost basis used on any reducing leg is within
/// tolerance of the running average cost basis in the account.
///
/// Accounts opened with any other booking method (`STRICT`, `STRICT_WITH_SIZE`,
/// `FIFO`, `LIFO`, `HIFO`, `AVERAGE`, …) are skipped — their booker already validates
/// lot matching, so re-checking here would produce false positives (see issue #907).
/// This matches Python beancount's `beancount.plugins.check_average_cost` behavior.
pub struct CheckAverageCostPlugin {
    /// Tolerance for cost comparison (default: 0.01 = 1%).
    tolerance: rust_decimal::Decimal,
}

impl CheckAverageCostPlugin {
    /// Create with default tolerance (1%).
    pub fn new() -> Self {
        Self {
            tolerance: rust_decimal::Decimal::new(1, 2), // 0.01 = 1%
        }
    }

    /// Create with custom tolerance.
    pub const fn with_tolerance(tolerance: rust_decimal::Decimal) -> Self {
        Self { tolerance }
    }
}

impl Default for CheckAverageCostPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CheckAverageCostPlugin {
    fn name(&self) -> &'static str {
        "check_average_cost"
    }

    fn description(&self) -> &'static str {
        "Validate reducing postings match average cost"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::collections::{HashMap, HashSet};

        let keep = || (0..input.directives.len()).map(PluginOp::Keep).collect();
        // The tolerance, a Python float, as beancount's `eval`s it; anything
        // else is an error there too.
        let tolerance = match input.config.as_deref().map(str::trim) {
            None | Some("") => self.tolerance,
            Some(config) => match parse_float(config) {
                Some(t) => t,
                None => {
                    return PluginOutput {
                        ops: keep(),
                        errors: vec![PluginError::error(
                            "Invalid configuration for check_average_cost: must be a float",
                        )],
                    };
                }
            },
        };
        // Deliberate divergence: beancount computes `D(1 - tolerance)` from
        // the binary float, so with `0.1` its lower bound is 0.9000000000000000222
        // and a cost of exactly 90% of the average fails there. The bounds
        // here are exact decimals, so a cost exactly at a bound passes.
        let min_tolerance = to_bigdecimal(Decimal::ONE - tolerance);
        let max_tolerance = to_bigdecimal(Decimal::ONE + tolerance);

        // First pass: collect accounts opened with the NONE booking method.
        // Only these accounts are subject to the average-cost check — see the
        // type-level docstring and issue #907 for rationale.
        let none_booking_accounts: HashSet<&str> = input
            .directives
            .iter()
            .filter_map(|w| match &w.data {
                DirectiveData::Open(o) => o
                    .booking
                    .as_deref()
                    .filter(|b| b.eq_ignore_ascii_case("NONE"))
                    .map(|_| o.account.as_str()),
                _ => None,
            })
            .collect();

        // The account's inventory, as beancount keeps it: per (account,
        // currency, cost currency), its lots, every posting added at the cost
        // it was booked at, a reduction included. Under NONE booking a sale
        // is a negative lot at its own cost, so the average after it is the
        // average of what the account actually holds (#2600: rledger removed
        // a sale at the average cost instead, and its average drifted from
        // the ledger's from the first off-average sale on). The arithmetic is
        // Python `decimal`'s (28 significant digits), so the average prints
        // as beancount prints it.
        let mut inventory: HashMap<(&str, &str, &str), Vec<Lot>> = HashMap::new();

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                continue;
            };
            for posting in &txn.postings {
                // Only process accounts opened with NONE booking (issue #907).
                if !none_booking_accounts.contains(posting.account.as_str()) {
                    continue;
                }
                // Only postings held at cost. (beancount's own plugin fails
                // outright on a reduction without one.)
                let (Some(units), Some(cost)) = (&posting.units, &posting.cost) else {
                    continue;
                };
                let Some(cost_currency) = &cost.currency else {
                    continue;
                };
                let Some(units_num) = py_decimal::parse(&units.number) else {
                    continue;
                };
                // A posting of no units changes nothing (and has no per-unit
                // cost to derive from a total).
                if units_num.is_zero() {
                    continue;
                }
                // The cost number as beancount books it: as written, or for a
                // `{{total}}` cost `total / units` at Python's 28 digits.
                let cost_number = match &cost.number {
                    Some(rustledger_plugin_types::CostNumberData::PerUnitFromTotal {
                        total,
                        ..
                    }) => py_decimal::parse(total).map(|t| {
                        // Deliberate limit: a compound `{P # L}` cost arrives
                        // as its exact total `P × N + L`, where beancount
                        // rounds `P × N` to 28 digits before adding `L`, so
                        // with very long numbers the last digit can differ.
                        //
                        // beancount books `{{T}}` as `(T + 0 × |N|) / |N|`, so
                        // the dividend takes the units' exponent (and is
                        // rounded to 28 digits) before the division.
                        let n = units_num.abs();
                        let t = py_decimal::add(&t, &py_decimal::mul(&BigDecimal::zero(), &n));
                        py_decimal::div(&t, &n)
                    }),
                    other => other
                        .as_ref()
                        .and_then(|cn| cn.per_unit())
                        .and_then(py_decimal::parse),
                };
                let Some(cost_number) = cost_number else {
                    continue;
                };

                let key = (
                    posting.account.as_str(),
                    units.currency.as_str(),
                    cost_currency.as_str(),
                );
                let lots = inventory.entry(key).or_default();

                // A reduction is checked against the average before it, when
                // the account holds any (beancount skips a zero total).
                if units_num.is_negative()
                    && let Some(average) = average_cost(lots)
                {
                    let min_valid = py_decimal::mul(&average, &min_tolerance);
                    let max_valid = py_decimal::mul(&average, &max_tolerance);
                    if !(min_valid <= cost_number && cost_number <= max_valid) {
                        errors.push(at_entry(
                            PluginError::error(format!(
                                "Cost basis on reducing posting is too far from the average cost ({} vs. {})",
                                py_decimal::to_str(&cost_number),
                                py_decimal::to_str(&average)
                            )),
                            wrapper,
                        ));
                    }
                }

                add_position(
                    lots,
                    Lot {
                        cost: cost_number,
                        date: cost.date.clone(),
                        label: cost.label.clone(),
                        units: units_num,
                    },
                );
            }
        }

        PluginOutput {
            ops: keep(),
            errors,
        }
    }
}

/// `config` as a Python float literal (`0.01`, `1e-2`), as beancount's
/// `eval` must find one; `None` for anything else, an integer included.
/// beancount `eval`s the config with builtins, so an expression such as
/// `float('0.1')` also works there; only a literal does here.
fn parse_float(config: &str) -> Option<rust_decimal::Decimal> {
    use std::str::FromStr;
    let Ok(PyValue::Number { text, .. }) = py_literal::parse(config) else {
        return None;
    };
    let text = text.replace('_', "");
    if !text.contains(['.', 'e', 'E']) {
        return None;
    }
    rust_decimal::Decimal::from_str(&text)
        .or_else(|_| rust_decimal::Decimal::from_scientific(&text))
        .ok()
}

/// One lot of a beancount inventory.
struct Lot {
    cost: BigDecimal,
    date: Option<String>,
    label: Option<String>,
    units: BigDecimal,
}

/// `Inventory.add_position`: the units join the lot of the same cost, date
/// and label, which goes when it reaches zero; else they are a new lot.
fn add_position(lots: &mut Vec<Lot>, lot: Lot) {
    if let Some(i) = lots
        .iter()
        .position(|l| l.cost == lot.cost && l.date == lot.date && l.label == lot.label)
    {
        let units = py_decimal::add(&lots[i].units, &lot.units);
        if units.is_zero() {
            lots.remove(i);
        } else {
            lots[i].units = units;
        }
    } else if !lot.units.is_zero() {
        lots.push(lot);
    }
}

/// `Inventory.average()`'s cost: the lots' total cost over their total
/// units, `None` when the units sum to zero.
fn average_cost(lots: &[Lot]) -> Option<BigDecimal> {
    let zero = BigDecimal::from(0);
    let mut total_units = zero.clone();
    let mut total_cost = zero.clone();
    for lot in lots {
        total_units = py_decimal::add(&total_units, &lot.units);
        total_cost = py_decimal::add(&total_cost, &py_decimal::mul(&lot.units, &lot.cost));
    }
    (total_units != zero).then(|| py_decimal::div(&total_cost, &total_units))
}

/// Python `decimal` arithmetic in its default context (28 significant
/// digits, half-even), and its `str`, on `BigDecimal`.
mod py_decimal {
    use bigdecimal::num_bigint::BigInt;
    use bigdecimal::{BigDecimal, RoundingMode, Signed, Zero};
    use std::num::NonZeroU64;

    const PRECISION: u64 = 28;

    fn digits(x: &BigDecimal) -> u64 {
        let (int, _) = x.as_bigint_and_exponent();
        if int.is_zero() {
            1
        } else {
            int.abs().to_string().len() as u64
        }
    }

    /// A result rounded to the context's precision when it has more digits.
    fn round(x: BigDecimal) -> BigDecimal {
        // A half-even carry (999… to 1000…) can leave one digit too many.
        let mut x = x;
        while digits(&x) > PRECISION {
            x = x.with_precision_round(
                NonZeroU64::new(PRECISION).expect("28"),
                RoundingMode::HalfEven,
            );
        }
        x
    }

    /// A decimal literal, as `Decimal("...")` reads it.
    pub(super) fn parse(text: &str) -> Option<BigDecimal> {
        text.parse().ok()
    }

    fn scale(x: &BigDecimal) -> i64 {
        x.as_bigint_and_exponent().1
    }

    /// `a + b` at Python's exponent, the smaller of the two (`BigDecimal`
    /// drops it when an operand is zero: `0E-25 + -10.0` must stay at 25
    /// places).
    pub(super) fn add(a: &BigDecimal, b: &BigDecimal) -> BigDecimal {
        let places = scale(a).max(scale(b));
        round((a + b).with_scale(places))
    }

    /// `a * b` at Python's exponent, the sum of the two.
    pub(super) fn mul(a: &BigDecimal, b: &BigDecimal) -> BigDecimal {
        let places = scale(a) + scale(b);
        round((a * b).with_scale(places))
    }

    /// `a / b`: an exact quotient at the ideal exponent `exp(a) - exp(b)`
    /// where that is exact, else rounded to 28 digits.
    pub(super) fn div(a: &BigDecimal, b: &BigDecimal) -> BigDecimal {
        let (_, scale_a) = a.as_bigint_and_exponent();
        let (_, scale_b) = b.as_bigint_and_exponent();
        let ideal = scale_a - scale_b;
        let quotient = a / b;
        if &(&quotient * b) == a {
            let reduced = quotient.normalized();
            let (_, scale) = reduced.as_bigint_and_exponent();
            let exact = if scale < ideal {
                reduced.with_scale(ideal)
            } else {
                reduced
            };
            if digits(&exact) <= PRECISION {
                return exact;
            }
        }
        // Rounded once: a truncated quotient with enough digits and a sticky
        // digit for a non-zero remainder, so a tail like `…4999|7` cannot
        // become a tie and round twice.
        let (a_int, a_scale) = a.as_bigint_and_exponent();
        let (b_int, b_scale) = b.as_bigint_and_exponent();
        let extra = (31 + digits(b) as i64 - digits(a) as i64).max(0);
        let num = a_int * BigInt::from(10).pow(u32::try_from(extra).expect("small"));
        let mut q = &num / &b_int;
        let r = &num % &b_int;
        let mut places = a_scale - b_scale + extra;
        if !r.is_zero() {
            let sticky = if num.is_negative() == b_int.is_negative() {
                1
            } else {
                -1
            };
            q = q * BigInt::from(10) + BigInt::from(sticky);
            places += 1;
        }
        round(BigDecimal::new(q, places))
    }

    /// `str(Decimal)`: plain, or scientific when the exponent is positive
    /// or the number is smaller than 1E-6 (`1E-7`, `0E-25`).
    pub(super) fn to_str(x: &BigDecimal) -> String {
        let (int, scale) = x.as_bigint_and_exponent();
        let negative = int.is_negative();
        let coefficient = int.abs().to_string();
        let exponent = -scale;
        let adjusted = exponent + coefficient.len() as i64 - 1;
        let sign = if negative { "-" } else { "" };
        if exponent <= 0 && adjusted >= -6 {
            let point = coefficient.len() as i64 + exponent;
            if exponent == 0 {
                format!("{sign}{coefficient}")
            } else if point > 0 {
                let (head, tail) = coefficient.split_at(point as usize);
                format!("{sign}{head}.{tail}")
            } else {
                format!("{sign}0.{}{coefficient}", "0".repeat((-point) as usize))
            }
        } else {
            let (head, tail) = coefficient.split_at(1);
            let tail = if tail.is_empty() {
                String::new()
            } else {
                format!(".{tail}")
            };
            let exp_sign = if adjusted >= 0 { "+" } else { "" };
            format!("{sign}{head}{tail}E{exp_sign}{adjusted}")
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// Each against Python's `decimal` in its default context.
        #[test]
        fn arithmetic_and_str_follow_python_decimal() {
            let d = |s: &str| parse(s).unwrap();
            assert_eq!(
                to_str(&div(&d("250"), &d("15"))),
                "16.66666666666666666666666667"
            );
            assert_eq!(to_str(&div(&d("7"), &d("2"))), "3.5");
            assert_eq!(to_str(&div(&d("1.00"), &d("2"))), "0.50");
            assert_eq!(to_str(&div(&d("10"), &d("4"))), "2.5");
            assert_eq!(to_str(&d("0.0000001")), "1E-7");
            assert_eq!(to_str(&d("0.00000100")), "0.00000100");
            assert_eq!(to_str(&d("-6.50")), "-6.50");
            let third = div(&d("100"), &d("3"));
            assert_eq!(
                to_str(&mul(&d("3"), &third)),
                "99.99999999999999999999999999"
            );
            let zero = add(
                &d("-100.0000000000000000000000000"),
                &d("100.0000000000000000000000000"),
            );
            assert_eq!(to_str(&zero), "0E-25");
            assert_eq!(
                to_str(&add(&zero, &d("-10.0"))),
                "-10.0000000000000000000000000"
            );
            assert_eq!(to_str(&add(&d("0E-25"), &d("0"))), "0E-25");
        }
    }
}

impl RegularPlugin for CheckAverageCostPlugin {}

#[cfg(test)]
mod check_average_cost_tests {
    use super::*;
    use crate::types::*;

    fn open_with_none_booking(account: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "open".to_string(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: account.to_string(),
                currencies: vec![],
                booking: Some("NONE".to_string()),
                metadata: vec![],
            }),
        }
    }

    #[test]
    fn test_check_average_cost_matching() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }), // Matches average
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_check_average_cost_mismatch() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at wrong cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "90.00".to_string(),
                                }), // 10% different from avg
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("average cost"));
    }

    #[test]
    fn test_check_average_cost_multiple_buys() {
        let plugin = CheckAverageCostPlugin::new();

        // Buy 10 at $100, then 10 at $120 -> avg = $110
        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 120".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "120.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "110.00".to_string(),
                                }), // Matches average
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_non_none_booking_is_skipped() {
        // Regression test for issue #907: accounts opened with any booking
        // method other than NONE (including the default, an unspecified
        // booking, or explicit STRICT/FIFO/etc.) must be skipped entirely.
        // The booker is responsible for lot matching in those cases, so
        // re-checking here produces false positives like the reporter's
        // "500 USD vs. avg 566.67 USD" error.
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                // No booking specified (booking: None). Whatever the effective
                // default is — STRICT unless overridden by `option
                // "booking_method"` or a loader setting — it is NOT `NONE`,
                // so the plugin MUST skip this account.
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Broker".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at way-off cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                // 50% off the average — would fire for NONE,
                                // but must be silent for STRICT/default.
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "50.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert!(
            output.errors.is_empty(),
            "non-NONE accounts must be skipped; got errors: {:?}",
            output.errors
        );
    }
}
