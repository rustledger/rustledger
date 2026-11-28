//! A transaction beancount's grammar discards is left out of the loaded
//! ledger, so balances and checks agree with beancount's; its parse error
//! stays, and the display context still samples its numbers.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};

fn load_source(src: &str) -> rustledger_loader::Ledger {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("ledger.beancount");
    std::fs::write(&path, src).expect("write ledger");
    let options = LoadOptions {
        validate: true,
        ..LoadOptions::default()
    };
    load(&path, &options).expect("ledger loads")
}

fn transactions(ledger: &rustledger_loader::Ledger) -> Vec<String> {
    ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t.narration.to_string()),
            _ => None,
        })
        .collect()
}

#[test]
fn test_load_leaves_out_a_transaction_beancount_discards() {
    // parser-lima `SyntaxErrors.ErrorInPosting`: bean-check 3.2.3 reports the
    // invalid token and the balance failing (the transaction never happened).
    let ledger = load_source(
        "2013-05-01 open Assets:US:Cash\n\n\
         2013-05-02 * \"Dinner\"\n  \
           Expenses:Resta(urant              100 USD\n  \
           Assets:US:Cash                   -100 USD\n\n\
         2013-05-03 * \"Lunch\"\n  \
           Expenses:Food                     10 USD\n  \
           Assets:US:Cash                   -10 USD\n\n\
         2013-05-04 balance Assets:US:Cash  -100 USD\n",
    );
    assert_eq!(transactions(&ledger), ["Lunch"]);
    let codes: Vec<&str> = ledger.errors.iter().map(|e| e.code.as_str()).collect();
    assert!(codes.contains(&"E2001"), "{codes:?}");
}

#[test]
fn test_load_keeps_a_transaction_whose_error_beancount_builds() {
    // A repeated metadata key is beancount's builder's error, raised on a
    // transaction its grammar builds: the transaction is kept.
    let ledger = load_source(
        "2013-05-01 open Assets:A\n2013-05-01 open Assets:B\n\
         2013-05-02 * \"a\"\n  kk: 1\n  kk: 2\n  Assets:A  1 USD\n  Assets:B  -1 USD\n",
    );
    assert!(!ledger.errors.is_empty(), "the repeated key is reported");
    assert_eq!(transactions(&ledger), ["a"]);
}

#[test]
fn test_load_display_context_still_samples_a_discarded_transaction() {
    let ledger = load_source(
        "2013-05-01 open Assets:A\n2013-05-01 open Assets:B\n\
         2013-05-02 * \"x\"\n  Assets:A  1.12345 USD $\n  Assets:B\n",
    );
    assert!(transactions(&ledger).is_empty());
    let shown = ledger
        .display_context
        .format(rust_decimal::Decimal::new(1, 0), "USD");
    assert_eq!(shown, "1.00000");
}
