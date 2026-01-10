//! REST API server for rustledger.
//!
//! Provides a JSON REST API for accessing ledger data, balances,
//! and reports. Compatible with web UIs and external tools.

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::get,
};
use clap::Parser;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_loader::Loader;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::ExitCode;
use tower_http::cors::{Any, CorsLayer};

/// REST API server for rustledger.
#[derive(Parser, Debug)]
#[command(name = "web", about = "Start the REST API server")]
pub struct Args {
    /// Generate shell completions for the specified shell.
    #[arg(long, value_name = "SHELL")]
    generate_completions: Option<ShellType>,

    /// Beancount file to serve.
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

    /// Port to listen on.
    #[arg(short, long, default_value = "8080")]
    port: u16,

    /// Host to bind to.
    #[arg(long, default_value = "127.0.0.1")]
    host: String,

    /// Enable CORS for all origins.
    #[arg(long)]
    cors: bool,
}

/// Shared application state.
#[derive(Clone)]
struct AppState {
    ledger_path: PathBuf,
}

// API Response types

#[derive(Serialize)]
struct ApiError {
    error: String,
}

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    version: String,
}

#[derive(Serialize)]
struct AccountsResponse {
    accounts: Vec<AccountInfo>,
}

#[derive(Serialize)]
struct AccountInfo {
    name: String,
    open_date: Option<String>,
    close_date: Option<String>,
    currencies: Vec<String>,
}

#[derive(Serialize)]
struct BalancesResponse {
    balances: HashMap<String, Vec<BalanceEntry>>,
}

#[derive(Serialize)]
struct BalanceEntry {
    currency: String,
    amount: String,
}

#[derive(Serialize)]
struct TransactionsResponse {
    transactions: Vec<TransactionInfo>,
    count: usize,
}

#[derive(Serialize)]
struct TransactionInfo {
    date: String,
    flag: String,
    payee: Option<String>,
    narration: String,
    postings: Vec<PostingInfo>,
    tags: Vec<String>,
}

#[derive(Serialize)]
struct PostingInfo {
    account: String,
    units: Option<String>,
    cost: Option<String>,
}

#[derive(Serialize)]
struct CommoditiesResponse {
    commodities: Vec<String>,
}

#[derive(Serialize)]
struct PricesResponse {
    prices: Vec<PriceInfo>,
}

#[derive(Serialize)]
struct PriceInfo {
    date: String,
    currency: String,
    amount: String,
    quote_currency: String,
}

#[derive(Deserialize)]
struct QueryParams {
    account: Option<String>,
    from: Option<String>,
    to: Option<String>,
    limit: Option<usize>,
}

/// Main entry point for the web command.
pub fn main() -> ExitCode {
    main_with_name("rledger-web")
}

/// Main entry point with custom binary name.
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // File is required when not generating completions
    let Some(file) = args.file.clone() else {
        eprintln!("error: FILE is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    // Verify the file exists
    if !file.exists() {
        eprintln!("error: file not found: {}", file.display());
        return ExitCode::from(1);
    }

    // Run the async server
    match run_server(args, file) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

#[tokio::main]
async fn run_server(args: Args, ledger_path: PathBuf) -> Result<()> {
    let state = AppState { ledger_path };

    // Build router
    let mut app = Router::new()
        .route("/health", get(health))
        .route("/api/v1/accounts", get(get_accounts))
        .route(
            "/api/v1/accounts/:account/balance",
            get(get_account_balance),
        )
        .route("/api/v1/balances", get(get_balances))
        .route("/api/v1/transactions", get(get_transactions))
        .route("/api/v1/commodities", get(get_commodities))
        .route("/api/v1/prices", get(get_prices))
        .with_state(state);

    // Add CORS if requested
    if args.cors {
        let cors = CorsLayer::new()
            .allow_origin(Any)
            .allow_methods(Any)
            .allow_headers(Any);
        app = app.layer(cors);
    }

    let addr: SocketAddr = format!("{}:{}", args.host, args.port)
        .parse()
        .with_context(|| format!("Invalid address: {}:{}", args.host, args.port))?;

    eprintln!("Starting server at http://{}", addr);
    eprintln!("Press Ctrl+C to stop");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .with_context(|| format!("Failed to bind to {}", addr))?;

    axum::serve(listener, app)
        .await
        .with_context(|| "Server error")?;

    Ok(())
}

// API Handlers

async fn health() -> impl IntoResponse {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

fn load_ledger(
    path: &PathBuf,
) -> Result<rustledger_loader::LoadResult, (StatusCode, Json<ApiError>)> {
    let mut loader = Loader::new();
    loader.load(path).map_err(|e| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ApiError {
                error: format!("Failed to load ledger: {}", e),
            }),
        )
    })
}

async fn get_accounts(
    State(state): State<AppState>,
) -> Result<Json<AccountsResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut accounts = Vec::new();
    for spanned in &ledger.directives {
        if let Directive::Open(open) = &spanned.value {
            accounts.push(AccountInfo {
                name: open.account.to_string(),
                open_date: Some(open.date.to_string()),
                close_date: None,
                currencies: open.currencies.iter().map(|c| c.to_string()).collect(),
            });
        }
    }

    Ok(Json(AccountsResponse { accounts }))
}

async fn get_account_balance(
    State(state): State<AppState>,
    Path(account): Path<String>,
) -> Result<Json<BalancesResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    // Compute balance by summing all postings to this account
    let mut amounts: HashMap<String, Decimal> = HashMap::new();
    for spanned in &ledger.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                if posting.account.as_str() == account {
                    if let Some(rustledger_core::IncompleteAmount::Complete(units)) = &posting.units
                    {
                        *amounts.entry(units.currency.to_string()).or_default() += units.number;
                    }
                }
            }
        }
    }

    let balances: Vec<BalanceEntry> = amounts
        .into_iter()
        .filter(|(_, amount)| *amount != Decimal::ZERO)
        .map(|(currency, amount)| BalanceEntry {
            currency,
            amount: amount.to_string(),
        })
        .collect();

    Ok(Json(BalancesResponse {
        balances: [(account, balances)].into_iter().collect(),
    }))
}

async fn get_balances(
    State(state): State<AppState>,
    Query(params): Query<QueryParams>,
) -> Result<Json<BalancesResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    // Compute balances for all accounts: account -> currency -> amount
    let mut account_amounts: HashMap<String, HashMap<String, Decimal>> = HashMap::new();

    for spanned in &ledger.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                let account = posting.account.as_str();

                // Filter by account prefix if specified
                if let Some(ref filter) = params.account {
                    if !account.starts_with(filter.as_str()) {
                        continue;
                    }
                }

                if let Some(rustledger_core::IncompleteAmount::Complete(units)) = &posting.units {
                    *account_amounts
                        .entry(account.to_string())
                        .or_default()
                        .entry(units.currency.to_string())
                        .or_default() += units.number;
                }
            }
        }
    }

    // Convert to response format
    let mut balances: HashMap<String, Vec<BalanceEntry>> = HashMap::new();

    for (account, currency_amounts) in account_amounts {
        let account_balances: Vec<BalanceEntry> = currency_amounts
            .into_iter()
            .filter(|(_, amount)| *amount != Decimal::ZERO)
            .map(|(currency, amount)| BalanceEntry {
                currency,
                amount: amount.to_string(),
            })
            .collect();

        if !account_balances.is_empty() {
            balances.insert(account, account_balances);
        }
    }

    Ok(Json(BalancesResponse { balances }))
}

async fn get_transactions(
    State(state): State<AppState>,
    Query(params): Query<QueryParams>,
) -> Result<Json<TransactionsResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut transactions = Vec::new();
    let mut count = 0;
    let limit = params.limit.unwrap_or(100);

    for spanned in ledger.directives.iter().rev() {
        if let Directive::Transaction(txn) = &spanned.value {
            // Filter by account if specified
            if let Some(ref account_filter) = params.account {
                let matches = txn
                    .postings
                    .iter()
                    .any(|p| p.account.as_str().starts_with(account_filter.as_str()));
                if !matches {
                    continue;
                }
            }

            // Filter by date range
            if let Some(ref from) = params.from {
                if txn.date.to_string() < *from {
                    continue;
                }
            }
            if let Some(ref to) = params.to {
                if txn.date.to_string() > *to {
                    continue;
                }
            }

            let postings: Vec<PostingInfo> = txn
                .postings
                .iter()
                .map(|p| {
                    let units = p.units.as_ref().and_then(|u| {
                        if let rustledger_core::IncompleteAmount::Complete(amt) = u {
                            Some(format!("{} {}", amt.number, amt.currency))
                        } else {
                            None
                        }
                    });
                    PostingInfo {
                        account: p.account.to_string(),
                        units,
                        cost: p.cost.as_ref().map(|c| format!("{:?}", c)),
                    }
                })
                .collect();

            transactions.push(TransactionInfo {
                date: txn.date.to_string(),
                flag: txn.flag.to_string(),
                payee: txn.payee.as_ref().map(|s| s.to_string()),
                narration: txn.narration.to_string(),
                postings,
                tags: txn.tags.iter().map(|t| t.to_string()).collect(),
            });

            count += 1;
            if count >= limit {
                break;
            }
        }
    }

    Ok(Json(TransactionsResponse {
        transactions,
        count,
    }))
}

async fn get_commodities(
    State(state): State<AppState>,
) -> Result<Json<CommoditiesResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut commodities = Vec::new();
    for spanned in &ledger.directives {
        if let Directive::Commodity(comm) = &spanned.value {
            commodities.push(comm.currency.to_string());
        }
    }

    commodities.sort();
    commodities.dedup();

    Ok(Json(CommoditiesResponse { commodities }))
}

async fn get_prices(
    State(state): State<AppState>,
) -> Result<Json<PricesResponse>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut prices = Vec::new();
    for spanned in &ledger.directives {
        if let Directive::Price(price) = &spanned.value {
            prices.push(PriceInfo {
                date: price.date.to_string(),
                currency: price.currency.to_string(),
                amount: price.amount.number.to_string(),
                quote_currency: price.amount.currency.to_string(),
            });
        }
    }

    // Sort by date descending
    prices.sort_by(|a, b| b.date.cmp(&a.date));

    Ok(Json(PricesResponse { prices }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_args_parsing() {
        let args = Args::parse_from(["web", "ledger.beancount"]);
        assert_eq!(args.file, Some(PathBuf::from("ledger.beancount")));
        assert_eq!(args.port, 8080);
        assert!(!args.cors);
    }

    #[test]
    fn test_args_with_options() {
        let args = Args::parse_from([
            "web",
            "-p",
            "3000",
            "--cors",
            "--host",
            "0.0.0.0",
            "ledger.beancount",
        ]);
        assert_eq!(args.port, 3000);
        assert_eq!(args.host, "0.0.0.0");
        assert!(args.cors);
    }
}
