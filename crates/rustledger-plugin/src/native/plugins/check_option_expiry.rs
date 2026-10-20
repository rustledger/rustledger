//! Error on option contracts still open after their expiry date.
//!
//! Option contracts are recognized by their OCC symbol with spaces removed:
//! a root of 1–6 characters, the expiry as `YYMMDD`, `C` or `P`, and the
//! strike × 1000 as 8 digits — e.g. `AAPL261016P00230000` is the AAPL
//! 2026-10-16 230 put. Every other commodity is ignored.
//!
//! "Today" is the date of the last directive in the ledger, not the system
//! clock, so the result is the same on every run. A contract is reported when
//! its net units in an account are non-zero and the ledger contains an entry
//! dated after its expiry. A close dated on the expiry day itself is fine.
//! Each entry's legs on one contract are netted before they apply, and an
//! entry that takes the position across zero opens a new one; the error
//! names the entry that opened the position still open.
//!
//! Same-day entries are taken in beancount's `entry_sortkey` order (date,
//! type, line number), so the entry named is the one `bean-check` names
//! even when same-day trades are split across included files. A position
//! whose net leaves `Decimal`'s range is not checked; booking rejects such
//! an inventory before the plugin runs, so only unbooked input gets there.
//!
//! The optional config `"{'as_of': 'YYYY-MM-DD'}"` sets "today" instead.
//! Entries dated after it are ignored, so a forecast or scheduled
//! transaction neither moves "today" forward nor closes a position early,
//! and a contract that expired before it is reported even when the ledger
//! has no later entry. The config is read by beancount-options' rules
//! (rustledger/beancount-options#2) so both report the same thing: see
//! [`parse_config`]. An invalid config gives one error and the plugin
//! skips.
//!
//! The plugin only reports: every directive is kept unchanged and nothing is
//! inserted, so a ledger stays complete without it.

use std::collections::BTreeMap;
use std::str::FromStr;

use rust_decimal::Decimal;

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::option_symbol::parse_occ;
use super::py_literal::{self, PyValue};

/// The whitespace stripped from around the config, spelled out as
/// beancount-options spells it: Rust's `trim()` and Python's `str.strip()`
/// both strip more (non-ASCII spaces; `\x1c`–`\x1f` in Python).
const BLANK: [char; 6] = [' ', '\t', '\n', '\r', '\x0c', '\x0b'];

/// The problem when the config is not a dict of the right shape.
const NOT_A_DICT: &str = "expected a dict such as {'as_of': '2026-10-16'}";

/// ` 'text'` when `text` is plain enough to quote back the same way in
/// every implementation (1–40 printable ASCII characters other than `'`,
/// `"` and `\`, beancount-options' `_QUOTABLE`), else nothing.
fn quoted(text: &str) -> String {
    let plain = (1..=40).contains(&text.len())
        && text
            .bytes()
            .all(|b| (b' '..=b'~').contains(&b) && !matches!(b, b'\'' | b'"' | b'\\'));
    if plain {
        format!(" '{text}'")
    } else {
        String::new()
    }
}

/// `text` as a date when it is exactly `[0-9]{4}-[0-9]{2}-[0-9]{2}` and a
/// real date in years 1 to 9999, as Python's `date.fromisoformat` reads it
/// after beancount-options' pattern check. jiff accepts year 0; Python
/// does not.
fn iso_date(text: &str) -> Option<String> {
    let [y1, y2, y3, y4, b'-', m1, m2, b'-', d1, d2] = text.as_bytes() else {
        return None;
    };
    if ![y1, y2, y3, y4, m1, m2, d1, d2]
        .iter()
        .all(|b| b.is_ascii_digit())
        || text.starts_with("0000")
    {
        return None;
    }
    text.parse::<jiff::civil::Date>().ok()?;
    Some(text.to_string())
}

/// Read the config the way beancount-options' `_parse_config` does.
///
/// `Ok(None)` is the default rule (no config, a blank one, or no `as_of`
/// key), `Ok(Some(date))` an `as_of` date as `YYYY-MM-DD`, and `Err` the
/// problem, checked in beancount-options' order: not a dict, a non-str
/// key, the first unknown key as written, a non-str `as_of`, then a bad
/// date. A repeated key keeps its first position and takes its last
/// value, as in a Python dict. Only `as_of`'s value is read, and a str key
/// equals only a str key, so taking its last value and scanning the keys
/// as written is that merge.
///
/// Deliberate divergences, all from what `py_literal` can read, on
/// configs nobody writes (listed in beancount-options'
/// `expiry_config.json` as `native_differs`): `literal_eval` fails on an
/// unhashable key or set element anywhere (`{[1]: 2}`, `{{}: 1}`), which
/// Python reports as not a dict, and `py_literal` has one kind for lists,
/// tuples and sets, so such a key is "keys must be strings" here and a
/// nested one is not noticed; and `py_literal` rejects `\N{...}` escapes
/// and complex numbers, which Python reads.
fn parse_config(config: Option<&str>) -> Result<Option<String>, String> {
    let Some(config) = config.map(|c| c.trim_matches(BLANK)) else {
        return Ok(None);
    };
    if config.is_empty() {
        return Ok(None);
    }
    let Ok(PyValue::Dict(entries)) = py_literal::parse(config) else {
        return Err(NOT_A_DICT.to_string());
    };
    let mut keys = Vec::with_capacity(entries.len());
    let mut as_of = None;
    for (key, value) in &entries {
        let PyValue::Str(key) = key else {
            return Err("keys must be strings".to_string());
        };
        keys.push(key.as_str());
        if key == "as_of" {
            as_of = Some(value);
        }
    }
    if let Some(unknown) = keys.into_iter().find(|k| *k != "as_of") {
        let quoted = quoted(unknown);
        return Err(if quoted.is_empty() {
            "an unknown key".to_string()
        } else {
            format!("unknown key{quoted}")
        });
    }
    let Some(value) = as_of else {
        return Ok(None);
    };
    let PyValue::Str(text) = value else {
        return Err("as_of must be a string".to_string());
    };
    iso_date(text).map(Some).ok_or_else(|| {
        format!(
            "as_of must be a date written YYYY-MM-DD{}",
            match quoted(text) {
                q if q.is_empty() => q,
                q => format!(", not{q}"),
            }
        )
    })
}

/// Net position of one contract in one account.
struct Position {
    expiry: String,
    net: Decimal,
    /// Index of the directive that opened the current position: the last one
    /// that moved it away from flat or across zero.
    opened_at: usize,
    /// The net left `Decimal`'s range; the position is no longer checked.
    overflowed: bool,
}

/// Plugin that reports option contracts left open past expiry.
pub struct CheckOptionExpiryPlugin;

impl NativePlugin for CheckOptionExpiryPlugin {
    fn name(&self) -> &'static str {
        "check_option_expiry"
    }

    fn description(&self) -> &'static str {
        "Error on option contracts still open after their expiry date"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut errors = Vec::new();
        let as_of = match parse_config(input.config.as_deref()) {
            Ok(as_of) => as_of,
            Err(problem) => {
                // Located as beancount's `check_commodity` locates its
                // config errors (`<check_option_expiry>:0`), as
                // beancount-options does.
                errors.push(
                    PluginError::error(format!(
                        "Invalid configuration for check_option_expiry plugin: {problem}; skipping."
                    ))
                    .at("<check_option_expiry>", 0),
                );
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors,
                };
            }
        };

        // Walk directives in beancount's `entry_sortkey` order (date, type,
        // line) without assuming the input is sorted. The loader keeps file
        // order for same-day entries; beancount does not.
        // With `as_of`, entries dated after it are not seen at all.
        let mut order: Vec<usize> = (0..input.directives.len())
            .filter(|&i| {
                as_of
                    .as_deref()
                    .is_none_or(|as_of| input.directives[i].date.as_str() <= as_of)
            })
            .collect();
        order.sort_by(|&a, &b| {
            input.directives[a]
                .sort_key()
                .cmp(&input.directives[b].sort_key())
        });

        let mut positions: BTreeMap<(String, String), Position> = BTreeMap::new();
        for &i in &order {
            let DirectiveData::Transaction(txn) = &input.directives[i].data else {
                continue;
            };
            // Net this entry's legs per (account, contract) first, so posting
            // order inside one entry doesn't matter and legs that cancel are a
            // no-op.
            // `None` once the entry's legs on a contract overflow.
            let mut deltas: BTreeMap<(&str, &str), (Option<Decimal>, String)> = BTreeMap::new();
            for posting in &txn.postings {
                let Some(units) = &posting.units else {
                    continue;
                };
                let Some(occ) = parse_occ(&units.currency) else {
                    continue;
                };
                let Ok(number) = Decimal::from_str(&units.number) else {
                    continue;
                };
                let delta = &mut deltas
                    .entry((posting.account.as_str(), units.currency.as_str()))
                    .or_insert((Some(Decimal::ZERO), occ.expiry))
                    .0;
                *delta = delta.and_then(|d| d.checked_add(number));
            }
            for ((account, symbol), (delta, expiry)) in deltas {
                let pos = positions
                    .entry((account.to_string(), symbol.to_string()))
                    .or_insert(Position {
                        expiry,
                        net: Decimal::ZERO,
                        opened_at: i,
                        overflowed: false,
                    });
                // Silent on purpose, unlike check_option_assignment's "not
                // checked" error: this net is the account's inventory of the
                // contract, and booking rejects an inventory past
                // `Decimal`'s range before plugins run, so through the loader
                // the check has already failed (see
                // `check_option_expiry_overflow_is_rejected_by_booking`).
                // Only unbooked input reaches this branch.
                let Some(new_net) = delta.and_then(|d| pos.net.checked_add(d)) else {
                    pos.overflowed = true;
                    continue;
                };
                // Opening from flat or crossing zero starts a new position;
                // going flat or growing one does not.
                if !new_net.is_zero() && new_net.cmp(&Decimal::ZERO) != pos.net.cmp(&Decimal::ZERO)
                {
                    pos.opened_at = i;
                }
                pos.net = new_net;
            }
        }

        // "Today": `as_of`, or the last directive's date. ISO dates compare
        // correctly as strings.
        let today = as_of
            .as_deref()
            .or_else(|| input.directives.iter().map(|d| d.date.as_str()).max());

        if let Some(today) = today {
            for ((account, symbol), pos) in &positions {
                if pos.overflowed || pos.net.is_zero() || pos.expiry.as_str() >= today {
                    continue;
                }
                let mut error = PluginError::error(format!(
                    "{symbol} expired {} but {} contract(s) remain open in {account}",
                    pos.expiry,
                    pos.net.normalize()
                ));
                let opened = &input.directives[pos.opened_at];
                if let (Some(file), Some(line)) = (&opened.filename, opened.lineno) {
                    error = error.at(file.clone(), line);
                }
                errors.push(error);
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for CheckOptionExpiryPlugin {}
