//! Canonical JSON wire codec for [`MetaValue`].
//!
//! Metadata values cross several wire boundaries — the CLI `query --format json`
//! output and the WASI FFI JSON-RPC surface. Each used to re-implement the same
//! `MetaValue` ↔ JSON match, so adding a variant meant editing every copy and
//! the copies could silently drift (the type tag in particular). This module is
//! the single source of that mapping.
//!
//! The WASM binding deliberately keeps `serde_json` a host-only dev-dependency
//! (it emits a typed enum instead), so it cannot call [`meta_value_to_json`] —
//! but it shares [`meta_value_type_tag`], which is `serde_json`-free, so the
//! drift-prone type tag stays single-sourced across *every* surface.
//!
//! The plugin (`MetaValueData`, `MessagePack`) and the Component-Model WIT
//! `meta-value` are separate, narrower wire contracts and are intentionally not
//! routed through this JSON codec.

use crate::MetaValue;

/// Canonical JSON form of a metadata value.
///
/// Numeric values are stringified (lossless for `Decimal`, and uniform with
/// `Int`). Typed references (`Account`/`Currency`/`Tag`/`Link`) lower to their
/// string form — matching bean-query, which has no first-class type for them on
/// the SQL/JSON surface.
#[must_use]
pub fn meta_value_to_json(value: &MetaValue) -> serde_json::Value {
    match value {
        MetaValue::String(s) => serde_json::Value::String(s.clone()),
        MetaValue::Account(a) => serde_json::Value::String(a.to_string()),
        MetaValue::Currency(c) => serde_json::Value::String(c.to_string()),
        MetaValue::Tag(t) => serde_json::Value::String(t.to_string()),
        MetaValue::Link(l) => serde_json::Value::String(l.to_string()),
        MetaValue::Date(d) => serde_json::Value::String(d.to_string()),
        MetaValue::Number(n) => serde_json::Value::String(n.to_string()),
        MetaValue::Int(i) => serde_json::Value::String(i.to_string()),
        MetaValue::Bool(b) => serde_json::Value::Bool(*b),
        MetaValue::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency.to_string(),
        }),
        MetaValue::None => serde_json::Value::Null,
    }
}

/// The wire type tag for a metadata value (`"string"`, `"int"`, `"amount"`, …).
///
/// Single source for the `type`/`value_type` discriminator emitted by the FFI
/// and WASM "typed value" forms. `serde_json`-free, so the WASM binding (which
/// avoids `serde_json`) shares it too.
#[must_use]
pub const fn meta_value_type_tag(value: &MetaValue) -> &'static str {
    match value {
        MetaValue::String(_) => "string",
        MetaValue::Account(_) => "account",
        MetaValue::Currency(_) => "currency",
        MetaValue::Tag(_) => "tag",
        MetaValue::Link(_) => "link",
        MetaValue::Date(_) => "date",
        MetaValue::Number(_) => "number",
        MetaValue::Int(_) => "int",
        MetaValue::Bool(_) => "bool",
        MetaValue::Amount(_) => "amount",
        MetaValue::None => "null",
    }
}

/// Parse a metadata value from its canonical JSON form (the inverse of
/// [`meta_value_to_json`] for the round-trippable cases).
///
/// A JSON integer becomes `Int`; an `{number, currency}` object becomes
/// `Amount`. Unparsable numbers and unrecognized shapes (arrays, foreign
/// objects) become `None` rather than coercing to zero or panicking — metadata
/// is informational, so "I saw something but couldn't interpret it" is the
/// honest result.
#[must_use]
pub fn json_to_meta_value(value: &serde_json::Value) -> MetaValue {
    use rust_decimal::Decimal;
    match value {
        serde_json::Value::String(s) => MetaValue::String(s.clone()),
        serde_json::Value::Bool(b) => MetaValue::Bool(*b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                MetaValue::Int(i)
            } else {
                // Parse the number's exact textual form rather than round-tripping
                // through f64 — that preserves `u64` values above `i64::MAX` and
                // high-precision decimals (within `Decimal`'s range).
                Decimal::from_str_exact(&n.to_string()).map_or(MetaValue::None, MetaValue::Number)
            }
        }
        serde_json::Value::Object(obj) => {
            if let (Some(number), Some(currency)) = (obj.get("number"), obj.get("currency"))
                && let (Some(n), Some(c)) = (number.as_str(), currency.as_str())
                && let Ok(number) = Decimal::from_str_exact(n)
            {
                return MetaValue::Amount(crate::Amount {
                    number,
                    currency: c.into(),
                });
            }
            MetaValue::None
        }
        serde_json::Value::Null | serde_json::Value::Array(_) => MetaValue::None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    /// Every variant maps to a non-degenerate tag + JSON, and the
    /// round-trippable ones survive `to_json -> json_to`. This is the fitness
    /// function: a new `MetaValue` variant forces a new arm in all three
    /// functions above (exhaustive match) and must be added here.
    #[test]
    fn codec_covers_every_variant() {
        let cases = [
            MetaValue::String("hi".into()),
            MetaValue::Account("Assets:Cash".into()),
            MetaValue::Currency("USD".into()),
            MetaValue::Tag("trip".into()),
            MetaValue::Link("inv-1".into()),
            MetaValue::Date(crate::naive_date(2024, 6, 15).unwrap()),
            MetaValue::Number(dec!(123.456)),
            MetaValue::Int(42),
            MetaValue::Bool(true),
            MetaValue::Amount(crate::Amount::new(dec!(99.99), "EUR")),
            MetaValue::None,
        ];
        for mv in &cases {
            // tag is non-empty for every variant
            assert!(!meta_value_type_tag(mv).is_empty());
            // to_json never panics and is well-formed
            let _ = meta_value_to_json(mv);
        }
        // Tags are exhaustive + distinct (one per variant).
        let tags: Vec<&str> = cases.iter().map(meta_value_type_tag).collect();
        let mut uniq = tags.clone();
        uniq.sort_unstable();
        uniq.dedup();
        assert_eq!(
            uniq.len(),
            tags.len(),
            "type tags must be distinct: {tags:?}"
        );
    }

    #[test]
    fn json_round_trip() {
        // Cases whose JSON form is faithfully invertible.
        assert_eq!(
            json_to_meta_value(&meta_value_to_json(&MetaValue::String("x".into()))),
            MetaValue::String("x".into())
        );
        assert_eq!(
            json_to_meta_value(&meta_value_to_json(&MetaValue::Bool(true))),
            MetaValue::Bool(true)
        );
        assert_eq!(
            json_to_meta_value(&meta_value_to_json(&MetaValue::None)),
            MetaValue::None
        );
        assert_eq!(
            json_to_meta_value(&meta_value_to_json(&MetaValue::Amount(crate::Amount::new(
                dec!(1.50),
                "USD"
            )))),
            MetaValue::Amount(crate::Amount::new(dec!(1.50), "USD"))
        );
        // Numbers are stringified on the wire, so they round-trip back as a
        // String (the wire form is intentionally lossy on numeric type — the
        // typed `meta_value_type_tag` carries the original type).
        assert_eq!(
            json_to_meta_value(&meta_value_to_json(&MetaValue::Int(7))),
            MetaValue::String("7".into())
        );
        // A real JSON integer (e.g. from a plugin) parses as Int.
        assert_eq!(json_to_meta_value(&serde_json::json!(7)), MetaValue::Int(7));
        // A u64 above i64::MAX is preserved exactly (not lost via an f64 hop).
        assert_eq!(
            json_to_meta_value(&serde_json::json!(18_446_744_073_709_551_615_u64)),
            MetaValue::Number(dec!(18446744073709551615))
        );
    }
}
