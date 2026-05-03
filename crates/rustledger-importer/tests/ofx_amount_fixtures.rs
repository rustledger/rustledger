//! Differential tests for OFX amount parsing.
//!
//! The OFX importer delegates number parsing to the third-party `ofxy` crate. These tests
//! construct OFX content with known amounts (sub-cent, negative, large) and assert that
//! every posting carries the exact `Decimal` value from the source — so that any silent
//! corruption by `ofxy` would surface here, the same way #972 surfaced for CSV.

use rust_decimal::Decimal;
use rustledger_importer::OfxImporter;
use std::str::FromStr;

fn ofx_with_transactions(txns: &str) -> String {
    format!(
        "OFXHEADER:100\nDATA:OFXSGML\nVERSION:102\nSECURITY:NONE\nENCODING:USASCII\n\
         CHARSET:1252\nCOMPRESSION:NONE\nOLDFILEUID:NONE\nNEWFILEUID:NONE\n\n\
         <OFX>\n<SIGNONMSGSRSV1>\n<SONRS>\n<STATUS>\n<CODE>0\n<SEVERITY>INFO\n</STATUS>\n\
         <DTSERVER>20240115120000\n<LANGUAGE>ENG\n</SONRS>\n</SIGNONMSGSRSV1>\n\
         <BANKMSGSRSV1>\n<STMTTRNRS>\n<TRNUID>1001\n<STATUS>\n<CODE>0\n<SEVERITY>INFO\n</STATUS>\n\
         <STMTRS>\n<CURDEF>USD\n\
         <BANKACCTFROM>\n<BANKID>123456789\n<ACCTID>987654321\n<ACCTTYPE>CHECKING\n</BANKACCTFROM>\n\
         <BANKTRANLIST>\n<DTSTART>20240101\n<DTEND>20240131\n{txns}\
         </BANKTRANLIST>\n\
         <LEDGERBAL>\n<BALAMT>5000.00\n<DTASOF>20240131\n</LEDGERBAL>\n\
         </STMTRS>\n</STMTTRNRS>\n</BANKMSGSRSV1>\n</OFX>"
    )
}

fn stmttrn(fitid: &str, amount: &str, name: &str) -> String {
    format!(
        "<STMTTRN>\n<TRNTYPE>OTHER\n<DTPOSTED>20240115\n<TRNAMT>{amount}\n<FITID>{fitid}\n<NAME>{name}\n</STMTTRN>\n"
    )
}

fn assert_ofx_amounts(amounts: &[&str]) {
    let txns: String = amounts
        .iter()
        .enumerate()
        .map(|(i, amt)| stmttrn(&format!("txn-{i:03}"), amt, &format!("Payee {i}")))
        .collect();
    let content = ofx_with_transactions(&txns);

    let importer = OfxImporter::new("Assets:Bank:Checking", "USD");
    let result = importer
        .extract_from_string(&content)
        .expect("OFX content should parse");

    assert!(
        result.warnings.is_empty(),
        "expected no warnings, got: {:?}",
        result.warnings
    );
    assert_eq!(
        result.directives.len(),
        amounts.len(),
        "every input row must produce a transaction"
    );

    for (directive, amount_str) in result.directives.iter().zip(amounts.iter()) {
        let txn = directive
            .as_transaction()
            .expect("directive should be a transaction");
        let bank_posting = txn
            .postings
            .iter()
            .find(|p| p.account.as_str() == "Assets:Bank:Checking")
            .expect("each transaction must have an Assets:Bank:Checking posting");
        let actual = bank_posting
            .amount()
            .expect("bank posting must have a complete amount")
            .number;
        let want = Decimal::from_str(amount_str).expect("test fixture amount must parse");
        assert_eq!(
            actual, want,
            "OFX amount {amount_str:?}: parsed {actual} but expected {want}"
        );
    }
}

#[test]
fn ofx_preserves_normal_amounts() {
    assert_ofx_amounts(&["1.00", "-50.00", "1500.00", "-25.50", "1234.56"]);
}

#[test]
fn ofx_preserves_sub_cent_amounts() {
    // The bug class from #972: any silent precision loss in `ofxy`'s amount parser
    // would corrupt these.
    assert_ofx_amounts(&["0.01", "-0.01", "0.05", "-0.05", "0.001", "-0.001"]);
}

#[test]
fn ofx_preserves_zero_amount() {
    // Non-zero is the common case but a $0.00 fee/marker line should still parse.
    let content = ofx_with_transactions(&stmttrn("txn-zero", "0.00", "Marker"));
    let importer = OfxImporter::new("Assets:Bank:Checking", "USD");
    let result = importer
        .extract_from_string(&content)
        .expect("OFX should parse");
    assert!(
        result.warnings.is_empty(),
        "warnings: {:?}",
        result.warnings
    );
    assert_eq!(result.directives.len(), 1);
    let posting = result.directives[0]
        .as_transaction()
        .unwrap()
        .postings
        .iter()
        .find(|p| p.account.as_str() == "Assets:Bank:Checking")
        .unwrap();
    assert_eq!(posting.amount().unwrap().number, Decimal::ZERO);
}

#[test]
fn ofx_negative_routes_to_expenses_positive_to_income() {
    let txns = format!(
        "{}{}",
        stmttrn("dr", "-12.34", "Outflow"),
        stmttrn("cr", "98.76", "Inflow"),
    );
    let content = ofx_with_transactions(&txns);
    let importer = OfxImporter::new("Assets:Bank:Checking", "USD");
    let result = importer.extract_from_string(&content).unwrap();
    assert_eq!(result.directives.len(), 2);

    let txn0 = result.directives[0].as_transaction().unwrap();
    let contra0 = txn0
        .postings
        .iter()
        .find(|p| p.account.as_str() != "Assets:Bank:Checking")
        .unwrap();
    assert_eq!(contra0.account.as_str(), "Expenses:Unknown");

    let txn1 = result.directives[1].as_transaction().unwrap();
    let contra1 = txn1
        .postings
        .iter()
        .find(|p| p.account.as_str() != "Assets:Bank:Checking")
        .unwrap();
    assert_eq!(contra1.account.as_str(), "Income:Unknown");
}
