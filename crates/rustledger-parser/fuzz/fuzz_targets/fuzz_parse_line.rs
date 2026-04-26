#![no_main]
//! Fuzz target for parsing individual directive lines.
//!
//! This fuzzer generates structured inputs that look more like
//! valid beancount syntax to explore deeper parser paths.
//!
//! Covers all 12 directive types plus edge cases:
//! - Transaction with costs, prices, tags, links, metadata
//! - Balance with tolerance
//! - Open with currencies and booking method
//! - Document, Query, Custom directives
//! - Unicode in strings
//! - Edge case amounts

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rustledger_parser::parse;

/// Maximum cents value for generating amounts (10000 cents = $100.00 max)
const MAX_AMOUNT_CENTS: i64 = 10000;
/// Divisor to convert cents to decimal (100 cents = $1.00)
const CENTS_DIVISOR: f64 = 100.0;

/// Transaction flag types
#[derive(Arbitrary, Debug, Clone, Copy)]
enum TxnFlag {
    Complete,   // *
    Incomplete, // !
    Pending,    // P
    Transfer,   // T
    Conversion, // C
}

impl TxnFlag {
    fn as_char(&self) -> char {
        match self {
            Self::Complete => '*',
            Self::Incomplete => '!',
            Self::Pending => 'P',
            Self::Transfer => 'T',
            Self::Conversion => 'C',
        }
    }
}

/// Price annotation type
#[derive(Arbitrary, Debug, Clone, Copy)]
enum PriceType {
    None,
    Unit,  // @
    Total, // @@
}

/// Cost specification type
#[derive(Arbitrary, Debug, Clone, Copy)]
enum CostType {
    None,
    Simple,    // {100 USD}
    WithDate,  // {100 USD, 2024-01-01}
    WithLabel, // {100 USD, "lot1"}
    Empty,     // {}
}

/// Booking method
#[derive(Arbitrary, Debug, Clone, Copy)]
enum BookingMethod {
    Fifo,
    Lifo,
    Hifo,
    Strict,
    Average,
    None,
}

impl BookingMethod {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Fifo => "FIFO",
            Self::Lifo => "LIFO",
            Self::Hifo => "HIFO",
            Self::Strict => "STRICT",
            Self::Average => "AVERAGE",
            Self::None => "NONE",
        }
    }
}

#[derive(Arbitrary, Debug)]
struct FuzzInput {
    // Date components
    date_year: u16,
    date_month: u8,
    date_day: u8,

    // Directive selection (0-15 for extended coverage)
    directive_type: u8,

    // Account name parts
    account_type: u8,
    account_sub: String,

    // Amount components
    amount_integer: i32,
    amount_decimal: u8,
    amount_negative: bool,

    // Currency
    currency_chars: [u8; 4],

    // Strings
    narration: String,
    payee: String,

    // Transaction extras
    txn_flag: TxnFlag,
    has_payee: bool,
    num_postings: u8,
    has_tags: bool,
    has_links: bool,
    tag_name: String,
    link_name: String,

    // Posting extras
    price_type: PriceType,
    cost_type: CostType,
    price_amount: i32,

    // Open extras
    has_currencies: bool,
    has_booking: bool,
    booking_method: BookingMethod,

    // Balance extras
    has_tolerance: bool,
    tolerance: u8,

    // Document/Query/Custom
    document_path: String,
    query_string: String,
    custom_type: String,

    // Metadata
    has_metadata: bool,
    meta_key: String,
    meta_value: String,

    // Second account for transactions
    second_account_type: u8,
    second_account_sub: String,
}

impl FuzzInput {
    fn format_date(&self) -> String {
        format!(
            "{:04}-{:02}-{:02}",
            2000 + (self.date_year % 100),
            (self.date_month % 12) + 1,
            (self.date_day % 28) + 1
        )
    }

    /// Format a price amount with 2 decimal places in range 0.00-99.99
    fn format_price_amount(&self) -> f64 {
        // Widen to i64 *before* taking the absolute value so that
        // `price_amount == i32::MIN` can't panic / wrap. `i32::MIN` widened
        // to i64 is well within i64's range, so `.abs()` on it is safe.
        // The result is then reduced mod MAX_AMOUNT_CENTS (also i64), and
        // only reaches `f64` after the math is done.
        (i64::from(self.price_amount).abs() % MAX_AMOUNT_CENTS) as f64 / CENTS_DIVISOR
    }

    fn format_account(&self, account_type: u8, sub: &str) -> String {
        let prefix = match account_type % 5 {
            0 => "Assets",
            1 => "Liabilities",
            2 => "Equity",
            3 => "Income",
            4 => "Expenses",
            _ => "Assets",
        };

        let sub_clean: String = sub
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '-')
            .take(20)
            .collect();

        let sub_part = if sub_clean.is_empty() {
            "Bank"
        } else {
            &sub_clean
        };

        format!("{}:{}", prefix, sub_part)
    }

    fn format_currency(&self) -> String {
        let chars: String = self
            .currency_chars
            .iter()
            .map(|b| (b'A' + (b % 26)) as char)
            .collect();

        if chars.len() >= 3 {
            chars[..3].to_string()
        } else {
            "USD".to_string()
        }
    }

    fn format_amount(&self) -> String {
        let sign = if self.amount_negative { "-" } else { "" };
        let decimal = self.amount_decimal % 100;
        // Widen before abs — see comment on format_price_amount for why.
        format!(
            "{}{}.{:02}",
            sign,
            i64::from(self.amount_integer).abs() % 1_000_000,
            decimal
        )
    }

    fn sanitize_string(&self, s: &str, max_len: usize) -> String {
        s.chars()
            .filter(|c| *c != '"' && *c != '\n' && *c != '\r' && *c != '\\')
            .take(max_len)
            .collect()
    }

    fn sanitize_identifier(&self, s: &str) -> String {
        s.chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '-' || *c == '_')
            .take(20)
            .collect()
    }

    fn format_cost(&self) -> String {
        match self.cost_type {
            CostType::None => String::new(),
            CostType::Simple => {
                format!(" {{{} {}}}", self.format_amount(), self.format_currency())
            }
            CostType::WithDate => format!(
                " {{{} {}, {}}}",
                self.format_amount(),
                self.format_currency(),
                self.format_date()
            ),
            CostType::WithLabel => format!(
                " {{{} {}, \"lot1\"}}",
                self.format_amount(),
                self.format_currency()
            ),
            CostType::Empty => " {}".to_string(),
        }
    }

    fn format_price(&self) -> String {
        match self.price_type {
            PriceType::None => String::new(),
            PriceType::Unit => format!(
                " @ {} {}",
                self.format_price_amount(),
                self.format_currency()
            ),
            PriceType::Total => format!(
                " @@ {} {}",
                self.format_price_amount(),
                self.format_currency()
            ),
        }
    }

    fn format_metadata(&self) -> String {
        if !self.has_metadata {
            return String::new();
        }
        let key = self.sanitize_identifier(&self.meta_key);
        let key = if key.is_empty() { "note" } else { &key };
        let value = self.sanitize_string(&self.meta_value, 50);
        format!("\n  {}: \"{}\"", key, value)
    }

    fn to_beancount(&self) -> String {
        let date = self.format_date();
        let account = self.format_account(self.account_type, &self.account_sub);
        let currency = self.format_currency();
        let amount = self.format_amount();
        let narration = self.sanitize_string(&self.narration, 100);

        match self.directive_type % 16 {
            // === Open directive ===
            0 => {
                let mut s = format!("{} open {}", date, account);
                if self.has_currencies {
                    s.push_str(&format!(" {}", currency));
                }
                if self.has_booking {
                    s.push_str(&format!(" \"{}\"", self.booking_method.as_str()));
                }
                s.push_str(&self.format_metadata());
                s
            }

            // === Close directive ===
            1 => {
                let mut s = format!("{} close {}", date, account);
                s.push_str(&self.format_metadata());
                s
            }

            // === Transaction - simple ===
            2 => {
                let flag = self.txn_flag.as_char();
                let second_account =
                    self.format_account(self.second_account_type, &self.second_account_sub);

                let mut s = format!("{} {} ", date, flag);

                if self.has_payee {
                    let payee = self.sanitize_string(&self.payee, 50);
                    s.push_str(&format!("\"{}\" ", payee));
                }
                s.push_str(&format!("\"{}\"", narration));

                if self.has_tags {
                    let tag = self.sanitize_identifier(&self.tag_name);
                    let tag = if tag.is_empty() { "tag" } else { &tag };
                    s.push_str(&format!(" #{}", tag));
                }
                if self.has_links {
                    let link = self.sanitize_identifier(&self.link_name);
                    let link = if link.is_empty() { "link" } else { &link };
                    s.push_str(&format!(" ^{}", link));
                }

                s.push_str(&self.format_metadata());

                // First posting with amount
                s.push_str(&format!("\n  {}  {} {}", account, amount, currency));
                s.push_str(&self.format_cost());
                s.push_str(&self.format_price());

                // Second posting (auto-balanced)
                s.push_str(&format!("\n  {}", second_account));

                s
            }

            // === Transaction - with multiple postings ===
            3 => {
                let flag = self.txn_flag.as_char();
                let num = (self.num_postings % 3) + 2; // 2-4 postings

                let mut s = format!("{} {} \"{}\"", date, flag, narration);
                s.push_str(&self.format_metadata());

                for i in 0..num {
                    // `wrapping_add` because both operands are `u8` and the
                    // fuzzer can legally produce `account_type` near 255 with
                    // `i` up to 3; we only care about the value mod 5 anyway.
                    let acc = self.format_account(
                        self.account_type.wrapping_add(i) % 5,
                        &format!("Sub{}", i),
                    );
                    if i == num - 1 {
                        // Last posting auto-balanced
                        s.push_str(&format!("\n  {}", acc));
                    } else {
                        // Widen before abs — see comment on format_price_amount.
                        let amt = (i64::from(self.amount_integer).abs() / i64::from(num))
                            % MAX_AMOUNT_CENTS;
                        s.push_str(&format!("\n  {}  {}.00 {}", acc, amt, currency));
                    }
                }
                s
            }

            // === Balance directive ===
            4 => {
                let mut s = format!("{} balance {} {} {}", date, account, amount, currency);
                if self.has_tolerance {
                    s.push_str(&format!(" ~ 0.{:02}", self.tolerance % 100));
                }
                s.push_str(&self.format_metadata());
                s
            }

            // === Pad directive ===
            5 => {
                let source = self.format_account(2, "Opening-Balances"); // Equity
                let mut s = format!("{} pad {} {}", date, account, source);
                s.push_str(&self.format_metadata());
                s
            }

            // === Note directive ===
            6 => {
                let mut s = format!("{} note {} \"{}\"", date, account, narration);
                s.push_str(&self.format_metadata());
                s
            }

            // === Event directive ===
            7 => {
                let event_type = self.sanitize_identifier(&self.custom_type);
                let event_type = if event_type.is_empty() {
                    "location"
                } else {
                    &event_type
                };
                let mut s = format!("{} event \"{}\" \"{}\"", date, event_type, narration);
                s.push_str(&self.format_metadata());
                s
            }

            // === Price directive ===
            8 => {
                let price_currency = self.format_currency();
                let base_currency = "USD";
                let mut s = format!(
                    "{} price {} {} {}",
                    date, price_currency, amount, base_currency
                );
                s.push_str(&self.format_metadata());
                s
            }

            // === Commodity directive ===
            9 => {
                let mut s = format!("{} commodity {}", date, currency);
                s.push_str(&self.format_metadata());
                s
            }

            // === Document directive ===
            10 => {
                let path = self.sanitize_string(&self.document_path, 100);
                let path = if path.is_empty() {
                    "/documents/receipt.pdf"
                } else {
                    &path
                };
                let mut s = format!("{} document {} \"{}\"", date, account, path);
                if self.has_tags {
                    let tag = self.sanitize_identifier(&self.tag_name);
                    let tag = if tag.is_empty() { "receipt" } else { &tag };
                    s.push_str(&format!(" #{}", tag));
                }
                s.push_str(&self.format_metadata());
                s
            }

            // === Query directive ===
            11 => {
                let query_name = self.sanitize_identifier(&self.query_string);
                let query_name = if query_name.is_empty() {
                    "my-query"
                } else {
                    &query_name
                };
                let query = "SELECT account, sum(position) GROUP BY account";
                let mut s = format!("{} query \"{}\" \"{}\"", date, query_name, query);
                s.push_str(&self.format_metadata());
                s
            }

            // === Custom directive ===
            12 => {
                let custom_type = self.sanitize_identifier(&self.custom_type);
                let custom_type = if custom_type.is_empty() {
                    "budget"
                } else {
                    &custom_type
                };
                let mut s = format!("{} custom \"{}\" \"{}\"", date, custom_type, narration);
                s.push_str(&self.format_metadata());
                s
            }

            // === Option directive ===
            13 => {
                let opt_name = match self.directive_type % 5 {
                    0 => "title",
                    1 => "operating_currency",
                    2 => "booking_method",
                    3 => "account_previous_balances",
                    _ => "name_assets",
                };
                let opt_value = if opt_name == "operating_currency" {
                    currency.clone()
                } else {
                    narration.clone()
                };
                format!("option \"{}\" \"{}\"", opt_name, opt_value)
            }

            // === Plugin directive ===
            14 => {
                let plugin_name = self.sanitize_identifier(&self.custom_type);
                let plugin_name = if plugin_name.is_empty() {
                    "auto_accounts"
                } else {
                    &plugin_name
                };
                format!("plugin \"{}\"", plugin_name)
            }

            // === Include directive ===
            15 => {
                let path = self.sanitize_string(&self.document_path, 50);
                let path = if path.is_empty() {
                    "other.beancount"
                } else {
                    &path
                };
                format!("include \"{}\"", path)
            }

            _ => String::new(),
        }
    }
}

fuzz_target!(|input: FuzzInput| {
    let beancount = input.to_beancount();
    // The parser should handle any generated input without panicking
    let _ = parse(&beancount);
});
