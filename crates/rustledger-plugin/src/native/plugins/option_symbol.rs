//! Shared helpers for option-contract plugins.
//!
//! Option contracts are recognized by their OCC symbol with spaces removed:
//! a root of 1–6 characters, the expiry as `YYMMDD`, `C` or `P`, and the
//! strike × 1000 as 8 digits — e.g. `AAPL261016P00230000` is the AAPL
//! 2026-10-16 230 put.

use std::str::FromStr;
use std::sync::LazyLock;

use regex::Regex;
use rust_decimal::Decimal;

/// OCC option symbol with spaces removed: root, `YYMMDD`, `C`/`P`, 8-digit strike.
/// `[0-9]`, not `\d`, so it accepts exactly what the Python counterpart accepts.
static OCC_SYMBOL_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^([A-Z][A-Z0-9.]{0,5})([0-9]{2})([0-9]{2})([0-9]{2})([CP])([0-9]{8})$")
        .expect("OCC symbol regex is valid")
});

/// Put or call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptionRight {
    /// Right to buy the underlying.
    Call,
    /// Right to sell the underlying.
    Put,
}

/// A parsed OCC option symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OccSymbol {
    /// Underlying root, e.g. `AAPL`.
    pub root: String,
    /// Expiry date as `YYYY-MM-DD`.
    pub expiry: String,
    /// Put or call.
    pub right: OptionRight,
    /// Strike price per share.
    pub strike: Decimal,
}

/// Parse `symbol` as an OCC option symbol. Returns `None` for anything that
/// is not one, including impossible dates such as month 13 or 2026-02-30.
pub fn parse_occ(symbol: &str) -> Option<OccSymbol> {
    let caps = OCC_SYMBOL_RE.captures(symbol)?;
    // OCC years are two digits; 20xx is deliberate and matches beancount-options.
    let year: i16 = 2000 + caps[2].parse::<i16>().ok()?;
    let month: i8 = caps[3].parse().ok()?;
    let day: i8 = caps[4].parse().ok()?;
    let date = jiff::civil::Date::new(year, month, day).ok()?;
    let right = if &caps[5] == "C" {
        OptionRight::Call
    } else {
        OptionRight::Put
    };
    let strike = Decimal::from_str(&caps[6]).ok()? / Decimal::from(1000);
    Some(OccSymbol {
        root: caps[1].to_string(),
        expiry: date.to_string(),
        right,
        strike: strike.normalize(),
    })
}

/// Whether a plugin was given a config: anything but ASCII whitespace,
/// which beancount-options strips (` \t\n\r\x0c\x0b`; not Unicode spaces).
pub fn config_is_set(config: Option<&str>) -> bool {
    config.is_some_and(|c| {
        !c.trim_matches([' ', '\t', '\n', '\r', '\x0c', '\x0b'])
            .is_empty()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_put_and_call() {
        let put = parse_occ("AAPL261016P00232500").unwrap();
        assert_eq!(put.root, "AAPL");
        assert_eq!(put.expiry, "2026-10-16");
        assert_eq!(put.right, OptionRight::Put);
        assert_eq!(put.strike, Decimal::from_str("232.5").unwrap());

        let call = parse_occ("SPXW261030C06800000").unwrap();
        assert_eq!(call.root, "SPXW");
        assert_eq!(call.right, OptionRight::Call);
        assert_eq!(call.strike, Decimal::from(6800));
    }

    #[test]
    fn rejects_non_occ() {
        for s in [
            "AAPL",
            "AAPL261316P00230000",
            "AAPL260230P00230000",
            "AAPL261016X00230000",
            "AAPL261016P0023000",
            "TOOLONGX261016P00230000",
            "ABCDEFG261016P00230000", // 7-character root
            "1ABC261016P00230000",    // root starts with a digit
            ".ABC261016P00230000",    // root starts with a dot
            // Arabic-Indic digits: `\d` would match them.
            "AAPL\u{662}\u{666}\u{661}\u{660}\u{661}\u{666}P00230000",
        ] {
            assert_eq!(parse_occ(s), None, "{s}");
        }
    }
}
