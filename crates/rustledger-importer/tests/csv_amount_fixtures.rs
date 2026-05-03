//! Regression for issue #972: sub-cent CSV amounts (e.g. `0.01`) used to silently parse as `0.1`.

use rust_decimal::Decimal;
use rustledger_importer::ImporterConfig;
use std::str::FromStr;

const FIXTURE: &str = "\
Date,Description,Amount
2024-10-20,Zero balance entry,0.00
2024-10-21,One cent interest,0.01
2024-10-22,Sub-cent FX residual,0.001
2024-10-23,Five cents,0.05
2024-10-24,Negative one cent,-0.01
2024-10-25,Negative sub-cent,-0.001
2024-10-26,Normal amount,1.00
2024-10-27,Normal with cents,1.23
2024-10-28,Larger amount,1234.56
";

#[test]
fn realistic_bank_export_parses_every_amount_correctly() {
    let config = ImporterConfig::csv()
        .account("Assets:Bank:Checking")
        .currency("USD")
        .date_column("Date")
        .narration_column("Description")
        .amount_column("Amount")
        .build()
        .unwrap();

    let result = config.extract_from_string(FIXTURE).unwrap();

    // The zero-amount row must parse cleanly (no warning). It's then dropped downstream
    // by the importer's intentional zero-skip — covered by csv_importer's own tests.
    assert!(
        result.warnings.is_empty(),
        "expected no parse warnings, got: {:?}",
        result.warnings
    );

    let expected = [
        ("One cent interest", "0.01"),
        ("Sub-cent FX residual", "0.001"),
        ("Five cents", "0.05"),
        ("Negative one cent", "-0.01"),
        ("Negative sub-cent", "-0.001"),
        ("Normal amount", "1.00"),
        ("Normal with cents", "1.23"),
        ("Larger amount", "1234.56"),
    ];
    assert_eq!(result.directives.len(), expected.len());

    for (directive, (narration, amount_str)) in result.directives.iter().zip(expected.iter()) {
        let txn = directive
            .as_transaction()
            .expect("directive should be a transaction");
        assert_eq!(txn.narration.as_str(), *narration);

        let bank_posting = txn
            .postings
            .iter()
            .find(|p| p.account.as_str() == "Assets:Bank:Checking")
            .expect("each transaction should have an Assets:Bank:Checking posting");
        let actual = bank_posting
            .amount()
            .expect("the bank posting should carry a complete amount")
            .number;
        let want = Decimal::from_str(amount_str).unwrap();
        assert_eq!(
            actual, want,
            "row {narration:?}: parsed {actual} but expected {want}"
        );
    }
}
