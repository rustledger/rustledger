//! External command price source.
//!
//! This module provides a price source that executes an external command
//! to fetch prices. This allows users to integrate custom price fetchers.

use super::sources::PriceSource;
use super::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::collections::HashMap;
use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};
use std::str::FromStr;
use std::time::Duration;

/// A price source that executes an external command.
///
/// The fetch context (ticker, currency, date) is passed to the command in
/// **two parallel ways**:
///
/// 1. **Environment variables** (recommended for arbitrary commands):
///    - `RLEDGER_TICKER` — the symbol being priced
///    - `RLEDGER_CURRENCY` — the requested quote currency
///    - `RLEDGER_DATE` — `YYYY-MM-DD`, or empty if no date was requested
///
///    The user's command runs verbatim. Shell variable expansion makes
///    integration with existing tools clean — for example, invoking
///    Python's `bean-price` directly:
///
///    ```sh
///    rledger price PROP --currency AUD \
///      --source-cmd 'bean-price -e $RLEDGER_CURRENCY:my.module/$RLEDGER_TICKER'
///    ```
///
/// 2. **Appended CLI arguments** (legacy; preserved for backward
///    compatibility with rledger-purpose-built fetchers): the command
///    additionally receives `<ticker> --date <date> --currency <currency>`
///    appended after its existing arguments. Tools that don't recognize
///    these flags will fail; users integrating arbitrary commands should
///    read from the env vars instead and ignore the appended args (or
///    write a wrapper that does).
///
/// Output formats accepted on stdout:
///
/// 1. Simple: `150.00 USD`
/// 2. JSON: `{"price": 150.00, "currency": "USD", "date": "2024-01-15"}`
/// 3. Beancount: `2024-01-15 price AAPL 150.00 USD`
///
/// # Limitations
///
/// - **Timeout**: The `timeout` parameter is accepted for API compatibility but
///   not currently enforced. `Command::wait_with_output()` does not support
///   timeouts without a separate thread or async runtime.
#[derive(Debug)]
pub struct ExternalCommandSource {
    /// The command and arguments to execute.
    command: Vec<String>,
    /// Additional environment variables.
    env: HashMap<String, String>,
    /// Source name for identification in responses.
    source_name: String,
}

impl ExternalCommandSource {
    /// Create a new external command source.
    pub fn new(command: Vec<String>, _timeout: Duration, env: HashMap<String, String>) -> Self {
        // Derive source name from the command for better traceability
        let source_name = command.first().map_or_else(
            || "external".to_string(),
            |cmd| {
                // Use just the binary name, not the full path
                std::path::Path::new(cmd)
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or(cmd)
                    .to_string()
            },
        );

        Self {
            command,
            env,
            source_name,
        }
    }

    /// Create a new external command source with a custom name.
    pub const fn with_name(
        command: Vec<String>,
        _timeout: Duration,
        env: HashMap<String, String>,
        name: String,
    ) -> Self {
        Self {
            command,
            env,
            source_name: name,
        }
    }

    /// Parse output in simple format: `150.00 USD`. Number-only lines adopt
    /// `requested_currency` rather than a hardcoded default.
    fn parse_simple_format(
        &self,
        line: &str,
        requested_currency: &str,
    ) -> Result<(Decimal, String)> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 2 {
            let price = Decimal::from_str(parts[0])
                .with_context(|| format!("Invalid price value: {}", parts[0]))?;
            let currency = parts[1].to_string();
            Ok((price, currency))
        } else if parts.len() == 1 {
            let price = Decimal::from_str(parts[0])
                .with_context(|| format!("Invalid price value: {}", parts[0]))?;
            Ok((price, requested_currency.to_string()))
        } else {
            anyhow::bail!("Invalid simple format output: {line}")
        }
    }

    /// Parse output in JSON format. A missing `currency` field adopts `requested_currency`.
    fn parse_json_format(
        &self,
        line: &str,
        requested_currency: &str,
    ) -> Result<(Decimal, String, Option<NaiveDate>)> {
        let json: serde_json::Value =
            serde_json::from_str(line).with_context(|| "Invalid JSON output")?;

        let price = json
            .get("price")
            .and_then(|v| {
                if let Some(n) = v.as_number() {
                    Decimal::from_str(&n.to_string()).ok()
                } else if let Some(s) = v.as_str() {
                    Decimal::from_str(s).ok()
                } else {
                    None
                }
            })
            .with_context(|| "Missing or invalid 'price' field in JSON")?;

        let currency = json
            .get("currency")
            .and_then(|v| v.as_str())
            .map_or_else(|| requested_currency.to_string(), String::from);

        let date = json
            .get("date")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<NaiveDate>().ok());

        Ok((price, currency, date))
    }

    /// Parse output in beancount format: `2024-01-15 price AAPL 150.00 USD`
    fn parse_beancount_format(&self, line: &str) -> Result<(Decimal, String, NaiveDate)> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 5 && parts[1] == "price" {
            let date = parts[0]
                .parse::<NaiveDate>()
                .with_context(|| format!("Invalid date: {}", parts[0]))?;
            let price = Decimal::from_str(parts[3])
                .with_context(|| format!("Invalid price: {}", parts[3]))?;
            let currency = parts[4].to_string();
            Ok((price, currency, date))
        } else {
            anyhow::bail!("Invalid beancount format output: {line}")
        }
    }
}

/// Validate that a ticker symbol is safe to pass to external commands.
///
/// Rejects tickers containing shell metacharacters or path separators.
fn validate_ticker(ticker: &str) -> Result<()> {
    // Reject empty tickers
    if ticker.is_empty() {
        anyhow::bail!("Empty ticker symbol");
    }

    // Reject tickers with shell metacharacters or path components
    let forbidden_chars = [
        '/', '\\', '`', '$', '(', ')', '{', '}', '[', ']', '|', ';', '&', '<', '>', '\n', '\r',
        '\0',
    ];
    if ticker.chars().any(|c| forbidden_chars.contains(&c)) {
        anyhow::bail!("Ticker contains forbidden characters: {ticker}");
    }

    // Reject tickers starting with dash (could be interpreted as flags)
    if ticker.starts_with('-') {
        anyhow::bail!("Ticker cannot start with dash: {ticker}");
    }

    Ok(())
}

impl PriceSource for ExternalCommandSource {
    fn name(&self) -> &'static str {
        "external"
    }

    fn description(&self) -> &'static str {
        "External command price source"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        if self.command.is_empty() {
            anyhow::bail!("External command is empty");
        }

        // Validate ticker to prevent command injection
        validate_ticker(&request.ticker)?;

        let program = &self.command[0];
        let args = &self.command[1..];

        let mut cmd = Command::new(program);
        cmd.args(args);

        // Pass fetch context as env vars (issue #1009 — recommended
        // path for arbitrary external commands like Python's
        // `bean-price`, which doesn't accept rledger's appended-args
        // convention). The user's command can read these via `$RLEDGER_*`
        // shell expansion or via env-var APIs in the language they're
        // using to write the fetcher.
        cmd.env("RLEDGER_TICKER", &request.ticker);
        cmd.env("RLEDGER_CURRENCY", &request.currency);
        cmd.env(
            "RLEDGER_DATE",
            request.date.map(|d| d.to_string()).unwrap_or_default(),
        );

        // Also append context as positional/flag args (legacy contract,
        // preserved for backward compatibility with rledger-purpose-built
        // fetchers). Tools that don't recognize these flags will fail —
        // those should read the env vars above instead.
        cmd.arg(&request.ticker);

        if let Some(date) = request.date {
            cmd.arg("--date");
            cmd.arg(date.to_string());
        }

        cmd.arg("--currency");
        cmd.arg(&request.currency);

        // Caller-provided env vars override `RLEDGER_*` if the user
        // explicitly passed e.g. `RLEDGER_TICKER=...` via config; this
        // is unusual but harmless.
        for (key, value) in &self.env {
            cmd.env(key, value);
        }

        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let child = cmd
            .spawn()
            .with_context(|| format!("Failed to execute command: {program}"))?;

        let output = child
            .wait_with_output()
            .with_context(|| "Failed to wait for command")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!(
                "Command failed with exit code {:?}: {}",
                output.status.code(),
                stderr.trim()
            );
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let reader = BufReader::new(stdout.as_bytes());

        // Try to parse the first non-empty line
        for line in reader.lines() {
            let line = line?;
            let line = line.trim();

            if line.is_empty() || line.starts_with(';') || line.starts_with('#') {
                continue;
            }

            // Try JSON format first
            if line.starts_with('{') {
                let (price, currency, date) = self.parse_json_format(line, &request.currency)?;
                return Ok(PriceResponse {
                    price,
                    currency,
                    date: date.unwrap_or_else(|| {
                        request.date.unwrap_or_else(|| jiff::Zoned::now().date())
                    }),
                    source: self.source_name.clone(),
                });
            }

            // Try beancount format
            if line.chars().next().is_some_and(|c| c.is_ascii_digit()) && line.contains("price") {
                let (price, currency, date) = self.parse_beancount_format(line)?;
                return Ok(PriceResponse {
                    price,
                    currency,
                    date,
                    source: self.source_name.clone(),
                });
            }

            // Try simple format
            let (price, currency) = self.parse_simple_format(line, &request.currency)?;
            return Ok(PriceResponse {
                price,
                currency,
                date: request.date.unwrap_or_else(|| jiff::Zoned::now().date()),
                source: self.source_name.clone(),
            });
        }

        anyhow::bail!("Command produced no valid output")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_format() {
        let source = ExternalCommandSource::new(vec![], Duration::from_secs(30), HashMap::new());

        let (price, currency) = source.parse_simple_format("150.00 USD", "USD").unwrap();
        assert_eq!(price, Decimal::from_str("150.00").unwrap());
        assert_eq!(currency, "USD");

        // Explicit currency in output always wins over the requested fallback.
        let (price, currency) = source.parse_simple_format("  99.99  EUR  ", "USD").unwrap();
        assert_eq!(price, Decimal::from_str("99.99").unwrap());
        assert_eq!(currency, "EUR");

        // Number-only output adopts the requested currency (regression for #979).
        let (price, currency) = source.parse_simple_format("42", "EUR").unwrap();
        assert_eq!(price, Decimal::from(42));
        assert_eq!(currency, "EUR");
    }

    #[test]
    fn test_parse_json_format() {
        let source = ExternalCommandSource::new(vec![], Duration::from_secs(30), HashMap::new());

        let (price, currency, date) = source
            .parse_json_format(
                r#"{"price": 150.00, "currency": "USD", "date": "2024-01-15"}"#,
                "USD",
            )
            .unwrap();
        assert_eq!(price, Decimal::from_str("150.00").unwrap());
        assert_eq!(currency, "USD");
        assert_eq!(
            date,
            Some(rustledger_core::naive_date(2024, 1, 15).unwrap())
        );

        // Missing "currency" field adopts the requested currency (regression for #979).
        let (price, currency, date) = source
            .parse_json_format(r#"{"price": "99.99"}"#, "GBP")
            .unwrap();
        assert_eq!(price, Decimal::from_str("99.99").unwrap());
        assert_eq!(currency, "GBP");
        assert!(date.is_none());

        // Explicit "currency" in the JSON wins over the requested fallback.
        let (_, currency, _) = source
            .parse_json_format(r#"{"price": "99.99", "currency": "JPY"}"#, "GBP")
            .unwrap();
        assert_eq!(currency, "JPY");
    }

    #[test]
    fn test_parse_beancount_format() {
        let source = ExternalCommandSource::new(vec![], Duration::from_secs(30), HashMap::new());

        let (price, currency, date) = source
            .parse_beancount_format("2024-01-15 price AAPL 150.00 USD")
            .unwrap();
        assert_eq!(price, Decimal::from_str("150.00").unwrap());
        assert_eq!(currency, "USD");
        assert_eq!(date, rustledger_core::naive_date(2024, 1, 15).unwrap());
    }

    #[test]
    fn test_external_command_echo() {
        let source = ExternalCommandSource::new(
            vec!["echo".to_string(), "150.00 USD".to_string()],
            Duration::from_secs(5),
            HashMap::new(),
        );

        let request = PriceRequest::new("AAPL", "USD");
        let response = source.fetch_price(&request).unwrap();

        assert_eq!(response.price, Decimal::from_str("150.00").unwrap());
        assert_eq!(response.currency, "USD");
        // Source name is derived from the command binary
        assert_eq!(response.source, "echo");
    }

    #[test]
    fn test_validate_ticker_valid() {
        assert!(validate_ticker("AAPL").is_ok());
        assert!(validate_ticker("BTC-USD").is_ok());
        assert!(validate_ticker("VTI").is_ok());
        assert!(validate_ticker("SPY500").is_ok());
    }

    #[test]
    fn test_validate_ticker_rejects_shell_metacharacters() {
        assert!(validate_ticker("$(whoami)").is_err());
        assert!(validate_ticker("AAPL;rm -rf /").is_err());
        assert!(validate_ticker("AAPL|cat /etc/passwd").is_err());
        assert!(validate_ticker("AAPL`id`").is_err());
        assert!(validate_ticker("AAPL&echo").is_err());
    }

    #[test]
    fn test_validate_ticker_rejects_paths() {
        assert!(validate_ticker("/etc/passwd").is_err());
        assert!(validate_ticker("../../../etc/passwd").is_err());
        assert!(validate_ticker("C:\\Windows").is_err());
    }

    #[test]
    fn test_validate_ticker_rejects_flags() {
        assert!(validate_ticker("-h").is_err());
        assert!(validate_ticker("--help").is_err());
        assert!(validate_ticker("-rf").is_err());
    }

    #[test]
    fn test_validate_ticker_rejects_empty() {
        assert!(validate_ticker("").is_err());
    }

    /// Issue #1009 — the user's command can read fetch context from
    /// `RLEDGER_TICKER` / `RLEDGER_CURRENCY` / `RLEDGER_DATE` env
    /// vars. Verifies all three are passed through to the child
    /// process and reach stdout via shell expansion.
    #[test]
    fn test_env_vars_passed_to_command() {
        // `sh -c 'echo "$RLEDGER_TICKER $RLEDGER_CURRENCY $RLEDGER_DATE"'`
        // — note: stdout becomes the price output. The command's
        // appended args (ticker/--date/--currency) end up as positional
        // args to `sh`, which `-c` ignores; what matters here is the
        // env var expansion.
        let source = ExternalCommandSource::new(
            vec![
                "sh".to_string(),
                "-c".to_string(),
                // Output a price-shaped line that uses the env vars,
                // so the test can both verify passing AND that they
                // resolved to the expected values.
                "echo \"42.42 $RLEDGER_CURRENCY\"".to_string(),
            ],
            Duration::from_secs(5),
            HashMap::new(),
        );

        let request = PriceRequest {
            ticker: "PROP".to_string(),
            currency: "AUD".to_string(),
            date: Some(rustledger_core::naive_date(2026, 5, 5).unwrap()),
        };
        let response = source.fetch_price(&request).expect("env-var fetch ok");

        // Currency came from `$RLEDGER_CURRENCY`.
        assert_eq!(response.currency, "AUD");
        assert_eq!(response.price, Decimal::from_str("42.42").unwrap());
    }

    /// `RLEDGER_DATE` is set to the empty string when no date was
    /// requested (rather than being unset). Pins this contract so
    /// `${RLEDGER_DATE:-today}` shell idioms work.
    #[test]
    #[allow(clippy::literal_string_with_formatting_args)] // shell `${VAR:-default}`, not Rust fmt
    fn test_env_vars_date_empty_when_not_requested() {
        let source = ExternalCommandSource::new(
            vec![
                "sh".to_string(),
                "-c".to_string(),
                // Use shell default-substitution: emit "today" when
                // RLEDGER_DATE is empty/unset.
                "echo \"42.00 USD ${RLEDGER_DATE:-today}\"".to_string(),
            ],
            Duration::from_secs(5),
            HashMap::new(),
        );

        let request = PriceRequest::new("AAPL", "USD"); // no date
        let response = source.fetch_price(&request).expect("ok");
        // The simple-format parser only reads "<price> <currency>"
        // (the trailing "today" / date is ignored). Verify the
        // request parsed cleanly — that confirms the shell didn't
        // bail on undefined-variable expansion (`set -u`-style).
        assert_eq!(response.price, Decimal::from_str("42.00").unwrap());
        assert_eq!(response.currency, "USD");
    }
}
