//! Control characters in imported text, neutralized (#2538).
//!
//! An importer copies text from a bank's file into the ledger: a CSV cell,
//! an OFX `<NAME>` or `<MEMO>`, what a WASM importer returns. Part of that
//! text is the merchant's to choose, and a control character in it would
//! travel into the ledger and from there to every terminal that shows it: an
//! escape sequence recolors or clears the screen, and a terminal honoring
//! OSC 52 lets it write the clipboard. Beancount strings have no escape
//! syntax for these characters, so `extract` replaces them before they are
//! written, and says where:
//!
//! - a tab, a newline (`\n`, `\r`) or a Unicode line or paragraph separator
//!   becomes a space, which is what it was standing for in the bank's text;
//! - any other character [`is_display_unsafe`] names (another C0 control,
//!   DEL, a C1 control, a bidirectional override) becomes U+FFFD, the
//!   replacement character, so the text shows that something was there.

use rustledger_core::format::is_display_unsafe;
use rustledger_core::{Directive, MetaValue, Metadata};

/// `text` with its control characters neutralized, or `None` when it has
/// none.
fn neutralize(text: &str) -> Option<String> {
    if !text.chars().any(is_display_unsafe) {
        return None;
    }
    Some(
        text.chars()
            .map(|c| match c {
                '\t' | '\n' | '\r' | '\u{2028}' | '\u{2029}' => ' ',
                c if is_display_unsafe(c) => char::REPLACEMENT_CHARACTER,
                c => c,
            })
            .collect(),
    )
}

/// Neutralize the string values of `meta`, naming each changed one in
/// `changed` as `<prefix>metadata "<key>"`.
fn neutralize_meta(meta: &mut Metadata, prefix: &str, changed: &mut Vec<String>) {
    let mut keys: Vec<String> = Vec::new();
    for (key, value) in meta.iter_mut() {
        if let MetaValue::String(s) = value
            && let Some(clean) = neutralize(s)
        {
            *s = clean;
            keys.push(key.clone());
        }
    }
    // The map's order is a hash order; the warning names keys in a stable one.
    keys.sort();
    changed.extend(
        keys.into_iter()
            .map(|key| format!("{prefix}metadata {key:?}")),
    );
}

/// Neutralize the imported text of `directive` in place, returning the names
/// of the fields that held a control character (empty when none did). The
/// caller names the row in its warning.
///
/// Covers what an importer writes as text: a transaction's payee, narration
/// and metadata (its postings' too), a note's comment, an event's value, and
/// any directive's string metadata. A document's path is a file name, not
/// text, and is left alone.
pub fn neutralize_directive(directive: &mut Directive) -> Vec<String> {
    let mut changed = Vec::new();
    match directive {
        Directive::Transaction(txn) => {
            if let Some(payee) = &txn.payee
                && let Some(clean) = neutralize(payee)
            {
                txn.payee = Some(clean.into());
                changed.push("payee".to_string());
            }
            if let Some(clean) = neutralize(&txn.narration) {
                txn.narration = clean.into();
                changed.push("narration".to_string());
            }
            if let Some(meta) = txn.meta.as_map_mut() {
                neutralize_meta(meta, "", &mut changed);
            }
            for posting in &mut txn.postings {
                let prefix = format!("posting {} ", posting.account);
                if let Some(meta) = posting.meta.as_map_mut() {
                    neutralize_meta(meta, &prefix, &mut changed);
                }
            }
        }
        Directive::Note(note) => {
            if let Some(clean) = neutralize(&note.comment) {
                note.comment = clean;
                changed.push("comment".to_string());
            }
            neutralize_meta(&mut note.meta, "", &mut changed);
        }
        Directive::Event(event) => {
            if let Some(clean) = neutralize(&event.value) {
                event.value = clean;
                changed.push("value".to_string());
            }
            neutralize_meta(&mut event.meta, "", &mut changed);
        }
        Directive::Balance(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Open(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Close(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Commodity(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Pad(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Document(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Query(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Price(d) => neutralize_meta(&mut d.meta, "", &mut changed),
        Directive::Custom(d) => neutralize_meta(&mut d.meta, "", &mut changed),
    }
    changed
}

/// The warning for a row whose `fields` were neutralized: `<row>: control
/// characters in <fields> replaced`.
pub fn warning(row: &str, fields: &[String]) -> String {
    format!(
        "{row}: control characters in {} replaced (a tab or newline with a space, \
         others with U+FFFD)",
        fields.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{Posting, Transaction, naive_date};

    #[test]
    fn neutralizes_controls_and_names_the_fields() {
        let mut txn = Transaction::new(naive_date(2024, 1, 2).unwrap(), "line\nbreak\ttab")
            .with_payee("SHOP\u{1b}]52;c;aGk=\u{7}\u{9b}31m\u{202e}");
        txn.meta.insert(
            "memo".to_string(),
            MetaValue::String("a\u{7f}b\r\nc".to_string()),
        );
        txn.meta
            .insert("clean".to_string(), MetaValue::String("fine".to_string()));
        let mut posting = Posting::auto("Expenses:Food");
        posting
            .meta
            .insert("note".to_string(), MetaValue::String("x\u{0}y".to_string()));
        let txn = txn.with_synthesized_posting(posting);
        let mut directive = Directive::Transaction(txn);

        let changed = neutralize_directive(&mut directive);
        assert_eq!(
            changed,
            [
                "payee",
                "narration",
                "metadata \"memo\"",
                "posting Expenses:Food metadata \"note\""
            ]
        );
        let Directive::Transaction(txn) = &directive else {
            unreachable!()
        };
        assert_eq!(txn.narration.as_str(), "line break tab");
        assert_eq!(
            txn.payee.as_deref(),
            Some("SHOP\u{fffd}]52;c;aGk=\u{fffd}\u{fffd}31m\u{fffd}")
        );
        assert_eq!(
            txn.meta.get("memo"),
            Some(&MetaValue::String("a\u{fffd}b  c".to_string()))
        );
        assert_eq!(
            txn.meta.get("clean"),
            Some(&MetaValue::String("fine".to_string()))
        );
        assert_eq!(
            txn.postings[0].meta.get("note"),
            Some(&MetaValue::String("x\u{fffd}y".to_string()))
        );

        // Clean text is not reported.
        let mut clean = Directive::Transaction(Transaction::new(
            naive_date(2024, 1, 2).unwrap(),
            "plain ünïcode",
        ));
        assert!(neutralize_directive(&mut clean).is_empty());
    }
}
