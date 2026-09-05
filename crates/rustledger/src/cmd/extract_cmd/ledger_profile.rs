//! Importer profiles declared on `open` directives (#2257).
//!
//! An account's `open` directive already states the account and its currency,
//! which are two of the three things an importer needs. Repeating them in
//! `importers.toml` is the duplication this closes:
//!
//! ```beancount
//! 2024-01-01 open Liabilities:CreditCard USD
//!   importer: "ofx"
//!   importer-pattern: "*.qfx"
//! ```
//!
//! Deliberately a *selector*, not a second config format. `importer` names
//! either a built-in parser (`csv`, `ofx`) or an `importers.toml` entry whose
//! column mappings should be used; the ledger never carries column mappings
//! itself. Two reasons: a ledger is a record of what happened rather than a
//! configuration file, and a full second schema would need keeping in sync
//! with the TOML one forever.
//!
//! Opt-in via `--ledger`. Without it nothing here runs, so no existing
//! invocation changes behavior.

use anyhow::{Result, anyhow};
use rustledger_core::{Directive, MetaValue, Metadata};
use std::path::Path;

/// Metadata key naming the importer: a built-in (`csv`/`ofx`) or a TOML entry.
const KEY_IMPORTER: &str = "importer";
/// Metadata key holding the filename glob that selects this profile.
const KEY_PATTERN: &str = "importer-pattern";

/// A profile read off one `open` directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LedgerProfile {
    /// The account the directive opens. This is the whole point: it is stated
    /// once, where it is declared, rather than repeated in a config file.
    pub account: String,
    /// The `importer` value, verbatim. Resolved by the caller, which knows
    /// whether a name matches a built-in or a TOML entry.
    pub importer: String,
    /// The single currency the directive declares, if it declares exactly one.
    ///
    /// `open Assets:X USD` is unambiguous. `open Assets:X USD,EUR` is not, and
    /// guessing which one a statement is denominated in would be exactly the
    /// kind of silent wrong answer this codebase avoids, so it yields `None`
    /// and the caller falls back.
    pub currency: Option<String>,
}

/// Read every importer profile from a ledger.
///
/// Directives without an `importer` key are ignored, so this is safe to run
/// over any ledger. A directive that has `importer` but no `importer-pattern`
/// is an error rather than a silent skip: it can never match a file, so it is
/// a typo or an unfinished edit, and staying quiet about it is how a user ends
/// up believing their profile works.
pub(super) fn load_profiles(path: &Path) -> Result<Vec<(String, LedgerProfile)>> {
    let options = rustledger_loader::LoadOptions {
        run_plugins: false,
        validate: false,
        ..Default::default()
    };
    let ledger = rustledger_loader::load(path, &options)
        .map_err(|e| anyhow!("failed to load ledger {}: {e}", path.display()))?;

    let mut out = Vec::new();
    for spanned in &ledger.directives {
        let Directive::Open(open) = &spanned.value else {
            continue;
        };
        let Some(importer) = meta_string(&open.meta, KEY_IMPORTER) else {
            continue;
        };
        let account = open.account.to_string();
        let Some(pattern) = meta_string(&open.meta, KEY_PATTERN) else {
            return Err(anyhow!(
                "account {account} declares `{KEY_IMPORTER}: \"{importer}\"` but no \
                 `{KEY_PATTERN}`, so it can never match a file"
            ));
        };
        out.push((
            pattern,
            LedgerProfile {
                account,
                importer,
                currency: sole_currency(open),
            },
        ));
    }
    Ok(out)
}

/// The profile whose pattern matches `filename`.
///
/// Ambiguity is an error, matching how `importers.toml` resolves a file that
/// several entries claim: picking one silently would make which profile you
/// got depend on directive order in the ledger.
pub(super) fn match_profile(
    profiles: &[(String, LedgerProfile)],
    filename: &str,
) -> Result<Option<LedgerProfile>> {
    let matches: Vec<&LedgerProfile> = profiles
        .iter()
        .filter(|(pattern, _)| glob::Pattern::new(pattern).is_ok_and(|p| p.matches(filename)))
        .map(|(_, profile)| profile)
        .collect();

    match matches.as_slice() {
        [] => Ok(None),
        [only] => Ok(Some((*only).clone())),
        many => {
            let accounts: Vec<&str> = many.iter().map(|p| p.account.as_str()).collect();
            Err(anyhow!(
                "{} accounts declare an importer matching '{filename}': {}. \
                 Narrow one of their `{KEY_PATTERN}` globs.",
                many.len(),
                accounts.join(", ")
            ))
        }
    }
}

fn meta_string(meta: &Metadata, key: &str) -> Option<String> {
    match meta.get(key) {
        Some(MetaValue::String(s)) => Some(s.clone()),
        // A bare `ofx` parses as a currency, and `importer: USD` is not a
        // thing anyone means, so accept it as the string it looks like.
        Some(MetaValue::Currency(c)) => Some(c.to_string()),
        _ => None,
    }
}

/// The declared currency, only when there is exactly one.
fn sole_currency(open: &rustledger_core::Open) -> Option<String> {
    match open.currencies.as_slice() {
        [one] => Some(one.to_string()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn ledger(contents: &str) -> tempfile::NamedTempFile {
        let mut f = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        f.write_all(contents.as_bytes()).unwrap();
        f.flush().unwrap();
        f
    }

    #[test]
    fn reads_account_and_currency_from_the_open_directive() {
        let f = ledger(
            "2024-01-01 open Liabilities:CreditCard USD\n  \
             importer: \"ofx\"\n  importer-pattern: \"*.qfx\"\n",
        );
        let profiles = load_profiles(f.path()).unwrap();
        assert_eq!(profiles.len(), 1);
        let (pattern, p) = &profiles[0];
        assert_eq!(pattern, "*.qfx");
        assert_eq!(p.account, "Liabilities:CreditCard");
        assert_eq!(p.importer, "ofx");
        assert_eq!(p.currency.as_deref(), Some("USD"));
    }

    /// Running over an ordinary ledger must find nothing and complain about
    /// nothing — the feature is opt-in per account, not per file.
    #[test]
    fn accounts_without_importer_metadata_are_ignored() {
        let f = ledger(
            "2024-01-01 open Assets:Bank:Checking USD\n\
             2024-01-01 open Expenses:Food\n\
             2024-01-02 * \"Lunch\"\n  Expenses:Food  5.00 USD\n  Assets:Bank:Checking\n",
        );
        assert!(load_profiles(f.path()).unwrap().is_empty());
    }

    /// A profile that can never match a file is a typo, not a preference.
    #[test]
    fn importer_without_a_pattern_is_an_error() {
        let f = ledger("2024-01-01 open Liabilities:Card USD\n  importer: \"ofx\"\n");
        let err = load_profiles(f.path()).unwrap_err().to_string();
        assert!(err.contains("Liabilities:Card"), "got: {err}");
        assert!(err.contains("importer-pattern"), "got: {err}");
    }

    /// Two currencies cannot be narrowed to one, and guessing which a
    /// statement uses would be a silent wrong answer.
    #[test]
    fn currency_is_only_taken_when_the_account_declares_exactly_one() {
        let multi = ledger(
            "2024-01-01 open Assets:X USD,EUR\n  \
             importer: \"csv\"\n  importer-pattern: \"*.csv\"\n",
        );
        assert_eq!(load_profiles(multi.path()).unwrap()[0].1.currency, None);

        let none = ledger(
            "2024-01-01 open Assets:X\n  importer: \"csv\"\n  importer-pattern: \"*.csv\"\n",
        );
        assert_eq!(load_profiles(none.path()).unwrap()[0].1.currency, None);
    }

    #[test]
    fn match_profile_selects_by_glob() {
        let profiles = vec![
            (
                "*.qfx".to_string(),
                LedgerProfile {
                    account: "Liabilities:Card".into(),
                    importer: "ofx".into(),
                    currency: Some("USD".into()),
                },
            ),
            (
                "acme-*.csv".to_string(),
                LedgerProfile {
                    account: "Assets:Acme".into(),
                    importer: "acme".into(),
                    currency: None,
                },
            ),
        ];

        let hit = match_profile(&profiles, "statement.qfx").unwrap().unwrap();
        assert_eq!(hit.account, "Liabilities:Card");

        let hit = match_profile(&profiles, "acme-jan.csv").unwrap().unwrap();
        assert_eq!(hit.account, "Assets:Acme");

        assert!(match_profile(&profiles, "unrelated.ofx").unwrap().is_none());
    }

    /// Picking one silently would make the result depend on directive order.
    #[test]
    fn two_matching_profiles_are_an_error() {
        let profiles = vec![
            (
                "*.qfx".to_string(),
                LedgerProfile {
                    account: "Liabilities:A".into(),
                    importer: "ofx".into(),
                    currency: None,
                },
            ),
            (
                "card*".to_string(),
                LedgerProfile {
                    account: "Liabilities:B".into(),
                    importer: "ofx".into(),
                    currency: None,
                },
            ),
        ];
        let err = match_profile(&profiles, "card.qfx")
            .unwrap_err()
            .to_string();
        assert!(err.contains("Liabilities:A"), "got: {err}");
        assert!(err.contains("Liabilities:B"), "got: {err}");
    }
}
