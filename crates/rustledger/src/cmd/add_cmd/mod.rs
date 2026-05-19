//! Add transactions to beancount files.
//!
//! Provides interactive and quick modes for adding transactions:
//!
//! - **Interactive mode**: Prompts for date, payee, accounts, amounts with tab completion
//! - **Quick mode**: One-liner for scripting and automation
//!
//! # Usage
//!
//! ```bash
//! # Interactive mode (default)
//! rledger add ledger.beancount
//!
//! # Quick mode
//! rledger add -q "Coffee Shop" "Morning coffee" Expenses:Food 4.50USD Assets:Checking
//!
//! # Dry run (preview without appending)
//! rledger add -n -q "Store" "Groceries" Expenses:Food 25USD Assets:Cash
//!
//! # Skip confirmation prompt
//! rledger add -y -q "Coffee" "" Expenses:Food 5USD Assets:Checking
//! ```
//!
//! # Options
//!
//! - `-d, --date <DATE>`: Transaction date (YYYY-MM-DD, "today", "yesterday", "+1", "-1")
//! - `-n, --dry-run`: Preview transaction without appending to file
//! - `-y, --yes`: Skip confirmation prompt
//! - `-q, --quick <ARGS>`: Quick mode with inline arguments
//! - `--no-completion`: Disable account tab completion in interactive mode

pub(crate) mod parsing;

use anyhow::{Context, Result, bail};
use clap::Parser;
use parsing::{calculate_balance, parse_amount, parse_date};
use rustledger_core::NaiveDate;
use rustledger_core::format::{FormatConfig, format_directive};
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_parser::parse;
use rustyline::completion::{Completer, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::Validator;
use rustyline::{Editor, Helper};
use std::borrow::Cow;
use std::fs::{self, File, OpenOptions};
use std::io::{Read as IoRead, Seek, SeekFrom, Write};
use std::path::PathBuf;
#[cfg(test)]
use {rust_decimal::Decimal, std::str::FromStr};

/// Add transactions to beancount files.
#[derive(Parser, Debug)]
#[command(name = "add")]
pub struct Args {
    /// File to append transaction to.
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Transaction date (YYYY-MM-DD, "today", "yesterday", "+1", "-1").
    #[arg(short, long)]
    pub date: Option<String>,

    /// Print transaction without appending.
    #[arg(short = 'n', long)]
    pub dry_run: bool,

    /// Skip confirmation prompt.
    #[arg(short, long)]
    pub yes: bool,

    /// Quick mode: payee narration account amount \[account \[amount\]\]...
    #[arg(short, long, num_args = 4.., value_name = "ARGS")]
    pub quick: Option<Vec<String>>,

    /// Disable account tab completion.
    #[arg(long)]
    pub no_completion: bool,
}

/// Account completer for interactive mode.
///
/// Provides tab completion for account names extracted from the ledger file.
struct AccountCompleter {
    accounts: Vec<String>,
}

impl AccountCompleter {
    /// Create a new completer with the given list of accounts.
    const fn new(accounts: Vec<String>) -> Self {
        Self { accounts }
    }

    /// Create an empty completer (no completion).
    const fn empty() -> Self {
        Self {
            accounts: Vec::new(),
        }
    }
}

impl Completer for AccountCompleter {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &rustyline::Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        let prefix = &line[..pos];

        // Find matches - both prefix and substring matches
        let mut matches: Vec<Pair> = self
            .accounts
            .iter()
            .filter(|a| a.starts_with(prefix) || a.to_lowercase().contains(&prefix.to_lowercase()))
            .map(|a| Pair {
                display: a.clone(),
                replacement: a.clone(),
            })
            .collect();

        // Sort: prefix matches first, then alphabetically
        matches.sort_by(|a, b| {
            let a_prefix = a.replacement.starts_with(prefix);
            let b_prefix = b.replacement.starts_with(prefix);
            match (a_prefix, b_prefix) {
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
                _ => a.replacement.cmp(&b.replacement),
            }
        });

        Ok((0, matches))
    }
}

/// Helper for rustyline editor with account completion.
struct AddHelper {
    completer: AccountCompleter,
}

impl AddHelper {
    const fn new(completer: AccountCompleter) -> Self {
        Self { completer }
    }
}

impl Helper for AddHelper {}

impl Completer for AddHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        ctx: &rustyline::Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        self.completer.complete(line, pos, ctx)
    }
}

impl Hinter for AddHelper {
    type Hint = String;

    fn hint(&self, _line: &str, _pos: usize, _ctx: &rustyline::Context<'_>) -> Option<String> {
        None
    }
}

impl Highlighter for AddHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        Cow::Borrowed(line)
    }

    fn highlight_char(&self, _line: &str, _pos: usize, _kind: CmdKind) -> bool {
        false
    }
}

impl Validator for AddHelper {}

/// Run the add command in quick mode.
fn run_quick_mode(args: &Args, file: &PathBuf, date: NaiveDate) -> Result<()> {
    let quick_args = args.quick.as_ref().expect("quick mode args");

    if quick_args.len() < 4 {
        bail!("Quick mode requires at least: payee narration account amount");
    }

    let payee = &quick_args[0];
    let narration = &quick_args[1];

    // Parse account/amount pairs
    let mut postings: Vec<Posting> = Vec::new();
    let mut amounts: Vec<Amount> = Vec::new();
    let mut i = 2;

    while i < quick_args.len() {
        let account = &quick_args[i];
        i += 1;

        if i < quick_args.len() {
            // Try to parse as amount
            if let Ok(amount) = parse_amount(&quick_args[i]) {
                postings.push(Posting::new(account.as_str(), amount.clone()));
                amounts.push(amount);
                i += 1;
            } else {
                // No amount for this account - will be auto-balanced
                postings.push(Posting::auto(account.as_str()));
            }
        } else {
            // Last account with no amount - auto-balance
            postings.push(Posting::auto(account.as_str()));
        }
    }

    // Validate postings
    if postings.len() < 2 {
        bail!(
            "Quick mode requires at least two postings (accounts), but only {} provided.",
            postings.len()
        );
    }

    // Check that at most one posting lacks units, and it must be the last one
    let missing_units: Vec<usize> = postings
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.has_units())
        .map(|(idx, _)| idx)
        .collect();

    if missing_units.len() > 1 {
        bail!(
            "Quick mode supports at most one posting without an explicit amount, \
             but {} postings lack amounts.",
            missing_units.len()
        );
    }

    if let Some(&idx) = missing_units.first()
        && idx != postings.len() - 1
    {
        bail!(
            "A posting without an amount must be the last posting, \
             but posting {} (of {}) lacks an amount.",
            idx + 1,
            postings.len()
        );
    }

    // If the last posting has no amount, calculate and set it
    if let Some(last) = postings.last_mut()
        && !last.has_units()
    {
        if amounts.is_empty() {
            bail!("Cannot auto-balance: no explicit amounts were provided for any posting.");
        }
        let balance = calculate_balance(&amounts)?;
        *last = Posting::new(last.account.as_str(), balance);
    }

    // Build the transaction
    let mut txn = Transaction::new(date, narration.as_str()).with_flag('*');

    if !payee.is_empty() {
        txn = txn.with_payee(payee.as_str());
    }

    for posting in postings {
        txn = txn.with_synthesized_posting(posting);
    }

    // Format and display
    let config = FormatConfig::default();
    let directive = Directive::Transaction(txn);
    let formatted = format_directive(&directive, &config);

    if args.dry_run {
        println!("{formatted}");
        return Ok(());
    }

    // Show preview and confirm
    if !args.yes {
        println!("Preview:");
        println!("{formatted}");
        print!("Append to {}? [Y/n] ", file.display());
        std::io::stdout().flush()?;

        let mut response = String::new();
        std::io::stdin().read_line(&mut response)?;
        let response = response.trim().to_lowercase();

        if !response.is_empty() && response != "y" && response != "yes" {
            println!("Cancelled.");
            return Ok(());
        }
    }

    // Append to file
    append_transaction(file, &formatted)?;

    println!("Transaction appended to {}", file.display());
    Ok(())
}

/// Extract all account names from a beancount file.
///
/// Parses the file and extracts accounts from Open, Close, Balance,
/// Pad, and Transaction directives.
fn extract_accounts(file: &PathBuf) -> Vec<String> {
    if !file.exists() {
        return Vec::new();
    }

    let content = match fs::read_to_string(file) {
        Ok(c) => c,
        Err(_) => return Vec::new(),
    };

    let parse_result = parse(&content);
    let mut accounts = Vec::new();

    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                accounts.push(open.account.to_string());
            }
            Directive::Close(close) => {
                accounts.push(close.account.to_string());
            }
            Directive::Balance(bal) => {
                accounts.push(bal.account.to_string());
            }
            Directive::Pad(pad) => {
                accounts.push(pad.account.to_string());
                accounts.push(pad.source_account.to_string());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.push(posting.account.to_string());
                }
            }
            _ => {}
        }
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Prompt for input with a default value.
///
/// Returns the trimmed input, or the default if input is empty.
fn prompt_with_default(
    rl: &mut Editor<AddHelper, DefaultHistory>,
    prompt: &str,
    default: &str,
) -> Result<String> {
    let full_prompt = if default.is_empty() {
        format!("{prompt}: ")
    } else {
        format!("{prompt} [{default}]: ")
    };

    match rl.readline(&full_prompt) {
        Ok(line) => {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                Ok(default.to_string())
            } else {
                Ok(trimmed.to_string())
            }
        }
        Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
            bail!("Cancelled.");
        }
        Err(e) => Err(e.into()),
    }
}

/// Run the add command in interactive mode.
fn run_interactive_mode(args: &Args, file: &PathBuf, date: NaiveDate) -> Result<()> {
    // Set up completer with accounts from the ledger file
    let completer = if args.no_completion {
        AccountCompleter::empty()
    } else {
        let accounts = extract_accounts(file);
        AccountCompleter::new(accounts)
    };

    let helper = AddHelper::new(completer);
    let mut rl: Editor<AddHelper, DefaultHistory> = Editor::new()?;
    rl.set_helper(Some(helper));

    // Prompt for date
    let date_default = date.to_string();
    let date_input = prompt_with_default(&mut rl, "Date", &date_default)?;
    let transaction_date = parse_date(&date_input)?;

    // Prompt for payee
    let payee = prompt_with_default(&mut rl, "Payee", "")?;

    // Prompt for narration
    let narration = prompt_with_default(&mut rl, "Narration", "")?;

    // Collect postings
    let mut postings: Vec<Posting> = Vec::new();
    let mut amounts: Vec<Amount> = Vec::new();
    let mut posting_num = 1;

    loop {
        // Prompt for account
        let account_prompt = format!("Account {posting_num}");
        let account = match rl.readline(&format!("{account_prompt}: ")) {
            Ok(line) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    if posting_num == 1 {
                        bail!("At least one account is required.");
                    }
                    break;
                }
                trimmed.to_string()
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                if posting_num == 1 {
                    bail!("Cancelled.");
                }
                break;
            }
            Err(e) => return Err(e.into()),
        };

        // Calculate auto-balance suggestion for display
        let balance_hint = if amounts.is_empty() {
            String::new()
        } else {
            match calculate_balance(&amounts) {
                Ok(bal) => format!("auto: {} {}", bal.number, bal.currency),
                Err(_) => String::new(),
            }
        };

        // Prompt for amount
        let amount_prompt = format!("Amount {posting_num}");
        let amount_default = if posting_num > 1 && !balance_hint.is_empty() {
            balance_hint
        } else {
            String::new()
        };

        let amount_input = prompt_with_default(&mut rl, &amount_prompt, &amount_default)?;

        if amount_input.is_empty() || amount_input == "none" {
            // No amount - will be auto-balanced by beancount
            postings.push(Posting::auto(&account));
        } else if amount_input.starts_with("auto:") {
            // User accepted auto-balance
            let balance = calculate_balance(&amounts)?;
            postings.push(Posting::new(&account, balance));
        } else {
            // Parse the amount
            let amount = parse_amount(&amount_input)?;
            postings.push(Posting::new(&account, amount.clone()));
            amounts.push(amount);
        }

        posting_num += 1;

        // Ask if user wants to add another posting
        if posting_num > 2 {
            let more = prompt_with_default(&mut rl, "Add another posting?", "n")?;
            if more.to_lowercase() != "y" && more.to_lowercase() != "yes" {
                break;
            }
        }
    }

    // Validate we have at least 2 postings for a balanced transaction
    if postings.len() < 2 {
        bail!(
            "At least two postings are required for a balanced transaction, but only {} provided.",
            postings.len()
        );
    }

    // If we have amounts and the last posting has no units, auto-balance it
    if let Some(last) = postings.last_mut()
        && !last.has_units()
        && !amounts.is_empty()
    {
        let balance = calculate_balance(&amounts)?;
        *last = Posting::new(last.account.as_str(), balance);
    }

    // Build the transaction
    let mut txn = Transaction::new(transaction_date, &narration).with_flag('*');

    if !payee.is_empty() {
        txn = txn.with_payee(&payee);
    }

    for posting in postings {
        txn = txn.with_synthesized_posting(posting);
    }

    // Format and display preview
    let config = FormatConfig::default();
    let directive = Directive::Transaction(txn);
    let formatted = format_directive(&directive, &config);

    if args.dry_run {
        println!("\n{formatted}");
        return Ok(());
    }

    // Show preview and confirm
    println!("\nPreview:");
    println!("{formatted}");

    if !args.yes {
        print!("Append to {}? [Y/n] ", file.display());
        std::io::stdout().flush()?;

        let mut response = String::new();
        std::io::stdin().read_line(&mut response)?;
        let response = response.trim().to_lowercase();

        if !response.is_empty() && response != "y" && response != "yes" {
            println!("Cancelled.");
            return Ok(());
        }
    }

    // Append to file
    append_transaction(file, &formatted)?;

    println!("Transaction appended to {}", file.display());
    Ok(())
}

/// Read the last N bytes of a file, or fewer if the file is smaller.
fn read_file_tail(file: &PathBuf, n: u64) -> Result<Vec<u8>> {
    let mut f = File::open(file).with_context(|| format!("Failed to open {}", file.display()))?;
    let len = f.metadata()?.len();

    if len == 0 {
        return Ok(Vec::new());
    }

    let read_len = len.min(n);
    let seek_pos = len.saturating_sub(n);

    f.seek(SeekFrom::Start(seek_pos))?;
    let mut buf = vec![0u8; read_len as usize];
    f.read_exact(&mut buf)?;

    Ok(buf)
}

/// Append a formatted transaction to a file.
fn append_transaction(file: &PathBuf, formatted: &str) -> Result<()> {
    // Check if file exists
    if !file.exists() {
        // Create the file with just the transaction
        fs::write(file, formatted)
            .with_context(|| format!("Failed to create {}", file.display()))?;
        return Ok(());
    }

    // Read only the last 2 bytes to check for trailing newlines
    let tail = read_file_tail(file, 2)?;

    let mut f = OpenOptions::new()
        .append(true)
        .open(file)
        .with_context(|| format!("Failed to open {} for appending", file.display()))?;

    // Add blank line separator based on file ending
    // Skip separator for empty files
    if !tail.is_empty() {
        let ends_with_newline = tail.last() == Some(&b'\n');
        let ends_with_double_newline =
            tail.len() >= 2 && tail[tail.len() - 2] == b'\n' && tail[tail.len() - 1] == b'\n';

        if !ends_with_double_newline {
            writeln!(f)?;
            if !ends_with_newline {
                writeln!(f)?;
            }
        }
    }

    write!(f, "{formatted}")?;

    Ok(())
}

/// Run the add command.
pub fn run(args: &Args, file: &PathBuf) -> Result<()> {
    // Parse the date
    let date = if let Some(ref d) = args.date {
        parse_date(d)?
    } else {
        jiff::Zoned::now().date()
    };

    // Check if file exists, offer to create if not
    if !file.exists() && !args.dry_run {
        if !args.yes {
            print!("File {} does not exist. Create it? [y/N] ", file.display());
            std::io::stdout().flush()?;

            let mut response = String::new();
            std::io::stdin().read_line(&mut response)?;
            let response = response.trim().to_lowercase();

            if response != "y" && response != "yes" {
                bail!("File does not exist: {}", file.display());
            }
        }
        // Create parent directories if needed
        if let Some(parent) = file.parent()
            && !parent.exists()
        {
            fs::create_dir_all(parent)
                .with_context(|| format!("Failed to create directory: {}", parent.display()))?;
        }
    }

    // Dispatch to appropriate mode
    if args.quick.is_some() {
        run_quick_mode(args, file, date)
    } else {
        run_interactive_mode(args, file, date)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_date_today() {
        let today = jiff::Zoned::now().date();
        assert_eq!(parse_date("today").unwrap(), today);
        assert_eq!(parse_date("").unwrap(), today);
        assert_eq!(parse_date("TODAY").unwrap(), today);
    }

    #[test]
    fn test_parse_date_yesterday() {
        let yesterday = jiff::Zoned::now().date().yesterday().ok().unwrap();
        assert_eq!(parse_date("yesterday").unwrap(), yesterday);
        assert_eq!(parse_date("YESTERDAY").unwrap(), yesterday);
    }

    #[test]
    fn test_parse_date_relative() {
        let today = jiff::Zoned::now().date();
        let tomorrow = today.tomorrow().ok().unwrap();
        let yesterday = today.yesterday().ok().unwrap();

        assert_eq!(parse_date("+1").unwrap(), tomorrow);
        assert_eq!(parse_date("-1").unwrap(), yesterday);
        assert_eq!(
            parse_date("+7").unwrap(),
            today.checked_add(jiff::ToSpan::days(7)).ok().unwrap()
        );
    }

    #[test]
    fn test_parse_date_explicit() {
        assert_eq!(
            parse_date("2026-03-21").unwrap(),
            rustledger_core::naive_date(2026, 3, 21).unwrap()
        );
        assert_eq!(
            parse_date("2024-01-01").unwrap(),
            rustledger_core::naive_date(2024, 1, 1).unwrap()
        );
    }

    #[test]
    fn test_parse_date_invalid() {
        assert!(parse_date("not-a-date").is_err());
        assert!(parse_date("2026/03/21").is_err());
        assert!(parse_date("03-21-2026").is_err());
    }

    #[test]
    fn test_parse_amount_with_space() {
        let amt = parse_amount("123.45 USD").unwrap();
        assert_eq!(amt.number, Decimal::from_str("123.45").unwrap());
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn test_parse_amount_no_space() {
        let amt = parse_amount("123.45USD").unwrap();
        assert_eq!(amt.number, Decimal::from_str("123.45").unwrap());
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn test_parse_amount_negative() {
        let amt = parse_amount("-50.00 EUR").unwrap();
        assert_eq!(amt.number, Decimal::from_str("-50.00").unwrap());
        assert_eq!(amt.currency.as_str(), "EUR");
    }

    #[test]
    fn test_parse_amount_integer() {
        let amt = parse_amount("100 BTC").unwrap();
        assert_eq!(amt.number, Decimal::from_str("100").unwrap());
        assert_eq!(amt.currency.as_str(), "BTC");
    }

    #[test]
    fn test_parse_amount_invalid() {
        assert!(parse_amount("123.45").is_err()); // No currency
        assert!(parse_amount("USD").is_err()); // No number
        assert!(parse_amount("abc USD").is_err()); // Invalid number
    }

    #[test]
    fn test_calculate_balance_simple() {
        let amounts = vec![Amount::new(Decimal::from_str("100.00").unwrap(), "USD")];
        let balance = calculate_balance(&amounts).unwrap();
        assert_eq!(balance.number, Decimal::from_str("-100.00").unwrap());
        assert_eq!(balance.currency.as_str(), "USD");
    }

    #[test]
    fn test_calculate_balance_multiple() {
        let amounts = vec![
            Amount::new(Decimal::from_str("50.00").unwrap(), "USD"),
            Amount::new(Decimal::from_str("25.00").unwrap(), "USD"),
        ];
        let balance = calculate_balance(&amounts).unwrap();
        assert_eq!(balance.number, Decimal::from_str("-75.00").unwrap());
    }

    #[test]
    fn test_calculate_balance_mixed_currencies() {
        let amounts = vec![
            Amount::new(Decimal::from_str("100.00").unwrap(), "USD"),
            Amount::new(Decimal::from_str("50.00").unwrap(), "EUR"),
        ];
        assert!(calculate_balance(&amounts).is_err());
    }

    #[test]
    fn test_calculate_balance_empty() {
        let amounts: Vec<Amount> = vec![];
        assert!(calculate_balance(&amounts).is_err());
    }

    #[test]
    fn test_account_completer_prefix_match() {
        let completer = AccountCompleter::new(vec![
            "Assets:Bank:Checking".to_string(),
            "Assets:Bank:Savings".to_string(),
            "Assets:Cash".to_string(),
            "Expenses:Food".to_string(),
            "Expenses:Transport".to_string(),
        ]);

        // Test prefix matching
        let history = rustyline::history::DefaultHistory::new();
        let ctx = rustyline::Context::new(&history);
        let (start, matches) = completer.complete("Assets", 6, &ctx).unwrap();
        assert_eq!(start, 0);
        assert_eq!(matches.len(), 3);
        assert!(matches.iter().any(|p| p.display == "Assets:Bank:Checking"));
        assert!(matches.iter().any(|p| p.display == "Assets:Bank:Savings"));
        assert!(matches.iter().any(|p| p.display == "Assets:Cash"));
    }

    #[test]
    fn test_account_completer_substring_match() {
        let completer = AccountCompleter::new(vec![
            "Assets:Bank:Checking".to_string(),
            "Expenses:Food".to_string(),
            "Liabilities:CreditCard".to_string(),
        ]);

        // Test substring matching (case insensitive)
        let history = rustyline::history::DefaultHistory::new();
        let ctx = rustyline::Context::new(&history);
        let (start, matches) = completer.complete("bank", 4, &ctx).unwrap();
        assert_eq!(start, 0);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].display, "Assets:Bank:Checking");
    }

    #[test]
    fn test_account_completer_empty() {
        let completer = AccountCompleter::empty();

        let history = rustyline::history::DefaultHistory::new();
        let ctx = rustyline::Context::new(&history);
        let (start, matches) = completer.complete("Assets", 6, &ctx).unwrap();
        assert_eq!(start, 0);
        assert!(matches.is_empty());
    }

    #[test]
    fn test_extract_accounts_from_string() {
        // Create a temporary file with beancount content
        let content = r#"
2024-01-01 open Assets:Checking
2024-01-01 open Expenses:Food
2024-01-02 * "Store" "Groceries"
  Expenses:Food  50.00 USD
  Assets:Checking
"#;
        let temp_file = unique_temp_file("extract_accounts");
        std::fs::write(&temp_file, content).unwrap();

        let accounts = extract_accounts(&temp_file);
        assert!(accounts.contains(&"Assets:Checking".to_string()));
        assert!(accounts.contains(&"Expenses:Food".to_string()));

        // Clean up
        std::fs::remove_file(&temp_file).ok();
    }

    #[test]
    fn test_extract_accounts_nonexistent_file() {
        let nonexistent = PathBuf::from("/nonexistent/file.beancount");
        let accounts = extract_accounts(&nonexistent);
        assert!(accounts.is_empty());
    }

    #[test]
    fn test_parse_amount_stock_ticker() {
        // Test stock tickers with dots like BRK.B
        let amt = parse_amount("10 BRK.B").unwrap();
        assert_eq!(amt.number, Decimal::from_str("10").unwrap());
        assert_eq!(amt.currency.as_str(), "BRK.B");
    }

    #[test]
    fn test_parse_amount_futures_contract() {
        // Test futures contracts with / prefix
        let amt = parse_amount("5 /ESM24").unwrap();
        assert_eq!(amt.number, Decimal::from_str("5").unwrap());
        assert_eq!(amt.currency.as_str(), "/ESM24");
    }

    #[test]
    fn test_parse_amount_no_space_complex() {
        // Test no-space format with complex currency
        let amt = parse_amount("100.5BRK.B").unwrap();
        assert_eq!(amt.number, Decimal::from_str("100.5").unwrap());
        assert_eq!(amt.currency.as_str(), "BRK.B");
    }

    /// Generate a unique temp file path to avoid race conditions in parallel tests.
    fn unique_temp_file(name: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = std::env::temp_dir();
        temp_dir.join(format!(
            "rustledger_test_{}_{}_{}.beancount",
            name,
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ))
    }

    #[test]
    fn test_append_transaction_new_file() {
        let temp_file = unique_temp_file("append_new");

        // Clean up any existing file
        std::fs::remove_file(&temp_file).ok();

        let txn = "2024-01-01 * \"Test\"\n  Assets:Cash  100 USD\n  Expenses:Test\n";
        append_transaction(&temp_file, txn).unwrap();

        let content = std::fs::read_to_string(&temp_file).unwrap();
        assert_eq!(content, txn);

        std::fs::remove_file(&temp_file).ok();
    }

    #[test]
    fn test_append_transaction_empty_file() {
        let temp_file = unique_temp_file("append_empty");

        // Create empty file
        std::fs::write(&temp_file, "").unwrap();

        let txn = "2024-01-01 * \"Test\"\n  Assets:Cash  100 USD\n";
        append_transaction(&temp_file, txn).unwrap();

        let content = std::fs::read_to_string(&temp_file).unwrap();
        // Empty file should not get separator
        assert_eq!(content, txn);

        std::fs::remove_file(&temp_file).ok();
    }

    #[test]
    fn test_append_transaction_with_newline() {
        let temp_file = unique_temp_file("append_newline");

        // File ending with single newline
        std::fs::write(&temp_file, "2024-01-01 open Assets:Cash\n").unwrap();

        let txn = "2024-01-02 * \"Test\"\n  Assets:Cash  100 USD\n";
        append_transaction(&temp_file, txn).unwrap();

        let content = std::fs::read_to_string(&temp_file).unwrap();
        // Should add one more newline for blank line separator
        assert!(content.contains("\n\n2024-01-02"));

        std::fs::remove_file(&temp_file).ok();
    }

    #[test]
    fn test_append_transaction_with_double_newline() {
        let temp_file = unique_temp_file("append_double_newline");

        // File already ending with double newline
        std::fs::write(&temp_file, "2024-01-01 open Assets:Cash\n\n").unwrap();

        let txn = "2024-01-02 * \"Test\"\n";
        append_transaction(&temp_file, txn).unwrap();

        let content = std::fs::read_to_string(&temp_file).unwrap();
        // Should not add extra newlines
        assert!(!content.contains("\n\n\n"));

        std::fs::remove_file(&temp_file).ok();
    }
}
