//! Payee rewriting: replace a bank's payee text with the name the ledger uses
//! (#2550).
//!
//! A bank writes `Hofer Dankt`, `AMZN Mktp DE*4Z81T` or `PAYPAL *SPOTIFY`;
//! the ledger says `Hofer`, `Amazon` and `Spotify`. A [`PayeeRules`] maps the
//! first onto the second. It runs on an importer's OUTPUT, so it applies the
//! same way to every importer (CSV, OFX, WASM), and `rledger extract` runs it
//! before ordering and `--existing` duplicate detection, so dedup compares
//! the canonical names a ledger holds.
//!
//! Rules match like `[importers.mappings]`: a pattern is a case-insensitive
//! substring, and a pattern written between slashes (`/^AMZN Mktp/`) is a
//! case-insensitive regular expression. Unlike mappings, which try the
//! longest pattern first, **the first rule that matches wins**, in the order
//! the rules are given: "most specific" has no meaning for a regex, and file
//! order is something the user can see and control.
//!
//! Only the payee changes. The narration keeps the bank's description, so
//! nothing the statement said is lost, and account categorization (which ran
//! inside the importer) has already matched the raw text.

use anyhow::{Result, anyhow};
use regex::RegexBuilder;
use rustledger_core::Directive;
use rustledger_ops::categorize::{Rule, RulePattern, RulesEngine};

/// An ordered list of payee rewrite rules. See the [module docs](self).
///
/// Matching is the categorization engine's own ([`RulesEngine`]), the one
/// `[importers.mappings]` goes through, with the canonical payee in place of
/// an account. Every rule has the same priority, and the engine keeps rules
/// of equal priority in the order they were added, so the first rule given
/// is the first tried.
#[derive(Debug, Default)]
pub struct PayeeRules {
    engine: RulesEngine,
    len: usize,
}

/// The regex body of a pattern written as `/.../`, or `None` for a substring.
///
/// A lone `/` is a substring: there is nothing between the delimiters.
fn regex_body(pattern: &str) -> Option<&str> {
    if pattern.len() >= 2 {
        pattern.strip_prefix('/')?.strip_suffix('/')
    } else {
        None
    }
}

impl PayeeRules {
    /// No rules: [`apply`](Self::apply) changes nothing.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            engine: RulesEngine::new(),
            len: 0,
        }
    }

    /// Append `(pattern, payee)` rules after the ones already held, so they
    /// are tried later. `source` names where the rules came from (an
    /// importer entry's `[importers.payees]`, the top-level `[payees]`) and
    /// leads every error, so a bad pattern points at the table it is in.
    ///
    /// # Errors
    ///
    /// A pattern between slashes that is not a valid regular expression, an
    /// empty pattern (it would match every transaction), or an empty payee.
    pub fn extend_from<'a>(
        &mut self,
        source: &str,
        rules: impl IntoIterator<Item = &'a (String, String)>,
    ) -> Result<()> {
        for (pattern, payee) in rules {
            if payee.trim().is_empty() {
                return Err(anyhow!(
                    "{source}: pattern \"{pattern}\" rewrites the payee to an empty string"
                ));
            }
            let compiled = match regex_body(pattern) {
                Some("") => None,
                Some(body) => Some(RulePattern::Regex(
                    RegexBuilder::new(body)
                        .case_insensitive(true)
                        .build()
                        .map_err(|e| {
                            anyhow!(
                                "{source}: \"{pattern}\" is not a valid regular expression: {e}"
                            )
                        })?,
                )),
                None if pattern.is_empty() => None,
                // Lowercased: the engine lowercases the text it matches.
                None => Some(RulePattern::Substring(pattern.to_lowercase())),
            };
            let Some(compiled) = compiled else {
                return Err(anyhow!(
                    "{source}: an empty pattern would rewrite every payee to \"{payee}\""
                ));
            };
            self.engine.add_rule(Rule {
                name: Some(pattern.clone()),
                pattern: compiled,
                account: payee.clone(),
                priority: 0,
            });
            self.len += 1;
        }
        Ok(())
    }

    /// Whether there are no rules.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The canonical payee for a transaction, or `None` when no rule matches.
    ///
    /// The text matched is the raw payee, or the narration when there is no
    /// payee (a statement without a payee column puts the counterparty in
    /// its description). A blank payee counts as none: the CSV importer
    /// already drops one, and a WASM importer may not. The first matching
    /// rule wins.
    #[must_use]
    pub fn rewrite(&self, payee: Option<&str>, narration: &str) -> Option<String> {
        let text = payee.filter(|p| !p.trim().is_empty()).unwrap_or(narration);
        // One text, not both: the engine would otherwise fall back to the
        // narration for a row whose payee no rule matches.
        self.engine.categorize(None, text).map(|m| m.account)
    }

    /// Rewrite the payee of every transaction a rule matches, leaving its
    /// narration and everything else as it was. Returns how many changed.
    pub fn apply(&self, directives: &mut [Directive]) -> usize {
        if self.is_empty() {
            return 0;
        }
        let mut changed = 0;
        for directive in directives {
            let Directive::Transaction(txn) = directive else {
                continue;
            };
            let Some(canonical) = self.rewrite(
                txn.payee.as_ref().map(rustledger_core::InternedStr::as_str),
                txn.narration.as_str(),
            ) else {
                continue;
            };
            if txn.payee.as_ref().map(rustledger_core::InternedStr::as_str)
                != Some(canonical.as_str())
            {
                txn.payee = Some(canonical.into());
                changed += 1;
            }
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{NaiveDate, Transaction};

    fn rules(pairs: &[(&str, &str)]) -> PayeeRules {
        let pairs: Vec<(String, String)> = pairs
            .iter()
            .map(|(p, a)| ((*p).to_string(), (*a).to_string()))
            .collect();
        let mut r = PayeeRules::new();
        r.extend_from("test", &pairs).unwrap();
        r
    }

    fn txn(payee: Option<&str>, narration: &str) -> Directive {
        let date = NaiveDate::new(2024, 1, 15).unwrap();
        let mut t = Transaction::new(date, narration);
        if let Some(p) = payee {
            t = t.with_payee(p);
        }
        Directive::Transaction(t)
    }

    fn payee_of(d: &Directive) -> Option<&str> {
        match d {
            Directive::Transaction(t) => t.payee.as_ref().map(rustledger_core::InternedStr::as_str),
            _ => None,
        }
    }

    #[test]
    fn substring_is_case_insensitive_and_keeps_the_narration() {
        let r = rules(&[("hofer dankt", "Hofer")]);
        let mut ds = vec![txn(Some("HOFER DANKT"), "Card 1234")];
        assert_eq!(r.apply(&mut ds), 1);
        assert_eq!(payee_of(&ds[0]), Some("Hofer"));
        let Directive::Transaction(t) = &ds[0] else {
            unreachable!()
        };
        assert_eq!(t.narration.as_str(), "Card 1234");
    }

    #[test]
    fn narration_is_matched_when_there_is_no_payee() {
        let r = rules(&[("Hofer Dankt", "Hofer")]);
        let mut ds = vec![txn(None, "HOFER DANKT 0815 Wien")];
        r.apply(&mut ds);
        assert_eq!(payee_of(&ds[0]), Some("Hofer"));
    }

    #[test]
    fn a_blank_payee_counts_as_none() {
        let r = rules(&[("hofer", "Hofer")]);
        // Set directly: the builder's `with_payee` may normalize a blank away.
        let mut ds = vec![txn(None, "HOFER DANKT")];
        if let Directive::Transaction(t) = &mut ds[0] {
            t.payee = Some("  ".into());
        }
        assert_eq!(r.apply(&mut ds), 1);
        assert_eq!(payee_of(&ds[0]), Some("Hofer"));
    }

    #[test]
    fn a_payee_is_matched_instead_of_the_narration() {
        // The narration would match, but the row has a payee: that is the
        // input, and it does not match.
        let r = rules(&[("Hofer", "Hofer")]);
        let mut ds = vec![txn(Some("Billa"), "paid near Hofer")];
        assert_eq!(r.apply(&mut ds), 0);
        assert_eq!(payee_of(&ds[0]), Some("Billa"));
    }

    #[test]
    fn regex_form_between_slashes() {
        let r = rules(&[("/^amzn mktp [a-z]{2}\\*/", "Amazon")]);
        let mut ds = vec![
            txn(Some("AMZN Mktp DE*4Z81T"), "x"),
            txn(Some("Not AMZN Mktp DE*1"), "x"),
        ];
        assert_eq!(r.apply(&mut ds), 1);
        assert_eq!(payee_of(&ds[0]), Some("Amazon"));
        assert_eq!(payee_of(&ds[1]), Some("Not AMZN Mktp DE*1"));
    }

    #[test]
    fn the_first_match_wins_not_the_longest() {
        // Mappings would pick the longer "amzn mktp"; payee rules take the
        // first one listed.
        let r = rules(&[("amzn", "Amazon"), ("amzn mktp", "Amazon Marketplace")]);
        assert_eq!(
            r.rewrite(Some("AMZN Mktp DE"), "").as_deref(),
            Some("Amazon")
        );
        let r = rules(&[("amzn mktp", "Amazon Marketplace"), ("amzn", "Amazon")]);
        assert_eq!(
            r.rewrite(Some("AMZN Mktp DE"), "").as_deref(),
            Some("Amazon Marketplace")
        );
    }

    #[test]
    fn a_lone_slash_is_a_substring() {
        let r = rules(&[("/", "Slash")]);
        assert_eq!(r.rewrite(Some("a/b"), "").as_deref(), Some("Slash"));
    }

    #[test]
    fn invalid_patterns_are_errors_naming_the_source() {
        let mut r = PayeeRules::new();
        let err = r
            .extend_from("importer 'bank'", &[("/(/".to_string(), "X".to_string())])
            .unwrap_err()
            .to_string();
        assert!(err.contains("importer 'bank'"), "{err}");
        assert!(
            err.contains("\"/(/\" is not a valid regular expression"),
            "{err}"
        );

        for pattern in ["", "//"] {
            let err = r
                .extend_from("s", &[(pattern.to_string(), "X".to_string())])
                .unwrap_err()
                .to_string();
            assert!(err.contains("empty pattern"), "{pattern:?}: {err}");
        }
        let err = r
            .extend_from("s", &[("x".to_string(), " ".to_string())])
            .unwrap_err()
            .to_string();
        assert!(err.contains("empty string"), "{err}");
    }
}
