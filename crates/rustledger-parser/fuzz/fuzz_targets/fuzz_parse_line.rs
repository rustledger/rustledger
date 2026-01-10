#![no_main]
//! Fuzz target for parsing individual directive lines.
//!
//! This fuzzer generates structured inputs that look more like
//! valid beancount syntax to explore deeper parser paths.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rustledger_parser::parse;

#[derive(Arbitrary, Debug)]
struct FuzzInput {
    date_year: u16,
    date_month: u8,
    date_day: u8,
    directive_type: u8,
    account: String,
    amount: i64,
    currency: String,
    narration: String,
}

impl FuzzInput {
    fn to_beancount(&self) -> String {
        let date = format!(
            "{:04}-{:02}-{:02}",
            self.date_year % 3000,
            (self.date_month % 12) + 1,
            (self.date_day % 28) + 1
        );

        // Sanitize account name - only allow valid account characters
        let account: String = self
            .account
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == ':')
            .take(50)
            .collect();
        let account = if account.is_empty() {
            "Assets:Test".to_string()
        } else if !account.starts_with(|c: char| c.is_ascii_uppercase()) {
            format!("Assets:{}", account)
        } else {
            account
        };

        // Sanitize currency - only uppercase letters
        let currency: String = self
            .currency
            .chars()
            .filter(|c| c.is_ascii_uppercase())
            .take(10)
            .collect();
        let currency = if currency.is_empty() {
            "USD".to_string()
        } else {
            currency
        };

        // Sanitize narration - remove quotes
        let narration: String = self
            .narration
            .chars()
            .filter(|c| *c != '"' && *c != '\n' && *c != '\r')
            .take(100)
            .collect();

        match self.directive_type % 10 {
            0 => format!("{} open {}", date, account),
            1 => format!("{} close {}", date, account),
            2 => format!(
                "{} * \"{}\"
  {}  {} {}
  Assets:Other",
                date, narration, account, self.amount, currency
            ),
            3 => format!("{} balance {} {} {}", date, account, self.amount, currency),
            4 => format!("{} pad {} Equity:Opening", date, account),
            5 => format!("{} note {} \"{}\"", date, account, narration),
            6 => format!("{} event \"test\" \"{}\"", date, narration),
            7 => format!("{} price {} {} {}", date, currency, self.amount, "USD"),
            8 => format!("option \"title\" \"{}\"", narration),
            9 => format!("{} commodity {}", date, currency),
            _ => String::new(),
        }
    }
}

fuzz_target!(|input: FuzzInput| {
    let beancount = input.to_beancount();
    // The parser should handle any generated input without panicking
    let _ = parse(&beancount);
});
