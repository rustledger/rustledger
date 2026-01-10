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
use chrono::Datelike;
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

// ============================================================================
// Fava-compatible API types
// ============================================================================

/// Fava ledger_data response - main ledger state
#[derive(Serialize)]
struct FavaLedgerData {
    accounts: Vec<String>,
    account_types: HashMap<String, String>,
    base_url: String,
    currencies: Vec<String>,
    errors: Vec<FavaError>,
    fava_options: FavaOptions,
    have_extension: bool,
    incognito: bool,
    links: Vec<String>,
    options: FavaBeancountOptions,
    payees: Vec<String>,
    tags: Vec<String>,
    years: Vec<i32>,
}

#[derive(Serialize)]
struct FavaError {
    message: String,
    source: Option<FavaErrorSource>,
}

#[derive(Serialize)]
struct FavaErrorSource {
    filename: String,
    lineno: u32,
}

#[derive(Serialize)]
struct FavaOptions {
    auto_reload: bool,
    currency_column: u32,
    indent: u32,
    locale: Option<String>,
    collapse_pattern: Vec<String>,
}

#[derive(Serialize)]
struct FavaBeancountOptions {
    title: String,
    name_assets: String,
    name_liabilities: String,
    name_equity: String,
    name_income: String,
    name_expenses: String,
    operating_currency: Vec<String>,
}

/// Fava balance_sheet response
#[derive(Serialize)]
struct FavaBalanceSheet {
    assets: FavaAccountTree,
    liabilities: FavaAccountTree,
    equity: FavaAccountTree,
    net_worth: HashMap<String, String>,
}

/// Fava income_statement response
#[derive(Serialize)]
struct FavaIncomeStatement {
    income: FavaAccountTree,
    expenses: FavaAccountTree,
    net_income: HashMap<String, String>,
}

#[derive(Serialize)]
struct FavaAccountTree {
    account: String,
    balance: HashMap<String, String>,
    children: Vec<FavaAccountTree>,
}

/// Fava journal entry
#[derive(Serialize)]
struct FavaJournalEntry {
    #[serde(rename = "type")]
    entry_type: String,
    date: String,
    flag: Option<String>,
    payee: Option<String>,
    narration: Option<String>,
    account: Option<String>,
    tags: Vec<String>,
    links: Vec<String>,
    postings: Vec<FavaPosting>,
    meta: HashMap<String, String>,
}

#[derive(Serialize)]
struct FavaPosting {
    account: String,
    units: Option<FavaAmount>,
    cost: Option<FavaCost>,
    price: Option<FavaAmount>,
}

#[derive(Serialize)]
struct FavaAmount {
    number: String,
    currency: String,
}

#[derive(Serialize)]
struct FavaCost {
    number: String,
    currency: String,
    date: Option<String>,
    label: Option<String>,
}

/// Fava commodities response
#[derive(Serialize)]
struct FavaCommodity {
    currency: String,
    base: String,
    prices: Vec<FavaPricePoint>,
}

#[derive(Serialize)]
struct FavaPricePoint {
    date: String,
    price: String,
}

/// Fava query response
#[derive(Serialize)]
struct FavaQueryResult {
    #[serde(rename = "type")]
    result_type: String,
    columns: Vec<String>,
    rows: Vec<Vec<serde_json::Value>>,
}

#[derive(Deserialize)]
struct FavaQueryParams {
    query_string: Option<String>,
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

    // Build router with both rustledger v1 API and Fava-compatible API
    let mut app = Router::new()
        // Health check
        .route("/health", get(health))
        // Rustledger v1 API
        .route("/api/v1/accounts", get(get_accounts))
        .route(
            "/api/v1/accounts/:account/balance",
            get(get_account_balance),
        )
        .route("/api/v1/balances", get(get_balances))
        .route("/api/v1/transactions", get(get_transactions))
        .route("/api/v1/commodities", get(get_commodities))
        .route("/api/v1/prices", get(get_prices))
        // Fava-compatible API endpoints
        .route("/api/ledger_data", get(fava_ledger_data))
        .route("/api/balance_sheet", get(fava_balance_sheet))
        .route("/api/income_statement", get(fava_income_statement))
        .route("/api/journal", get(fava_journal))
        .route("/api/commodities", get(fava_commodities))
        .route("/api/query", get(fava_query))
        .route("/api/events", get(fava_events))
        .route("/api/errors", get(fava_errors))
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

// ============================================================================
// Fava-compatible API handlers
// ============================================================================

/// Fava ledger_data endpoint - returns main ledger state
async fn fava_ledger_data(
    State(state): State<AppState>,
) -> Result<Json<FavaLedgerData>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut accounts = Vec::new();
    let mut account_types: HashMap<String, String> = HashMap::new();
    let mut currencies = Vec::new();
    let mut payees = Vec::new();
    let mut tags = Vec::new();
    let mut links = Vec::new();
    let mut years = std::collections::HashSet::new();

    for spanned in &ledger.directives {
        match &spanned.value {
            Directive::Open(open) => {
                let name = open.account.to_string();
                // Determine account type from first component
                let account_type = name.split(':').next().unwrap_or("Unknown").to_string();
                account_types.insert(name.clone(), account_type);
                accounts.push(name);
            }
            Directive::Commodity(comm) => {
                currencies.push(comm.currency.to_string());
            }
            Directive::Transaction(txn) => {
                years.insert(txn.date.year());
                if let Some(ref p) = txn.payee {
                    if !payees.contains(&p.to_string()) {
                        payees.push(p.to_string());
                    }
                }
                for tag in &txn.tags {
                    let t = tag.to_string();
                    if !tags.contains(&t) {
                        tags.push(t);
                    }
                }
                for link in &txn.links {
                    let l = link.to_string();
                    if !links.contains(&l) {
                        links.push(l);
                    }
                }
            }
            _ => {}
        }
    }

    accounts.sort();
    currencies.sort();
    currencies.dedup();
    payees.sort();
    tags.sort();
    links.sort();
    let mut years: Vec<i32> = years.into_iter().collect();
    years.sort();

    Ok(Json(FavaLedgerData {
        accounts,
        account_types,
        base_url: "/".to_string(),
        currencies,
        errors: Vec::new(),
        fava_options: FavaOptions {
            auto_reload: true,
            currency_column: 61,
            indent: 2,
            locale: None,
            collapse_pattern: Vec::new(),
        },
        have_extension: false,
        incognito: false,
        links,
        options: FavaBeancountOptions {
            title: "rustledger".to_string(),
            name_assets: "Assets".to_string(),
            name_liabilities: "Liabilities".to_string(),
            name_equity: "Equity".to_string(),
            name_income: "Income".to_string(),
            name_expenses: "Expenses".to_string(),
            operating_currency: vec!["USD".to_string()],
        },
        payees,
        tags,
        years,
    }))
}

/// Build account tree from flat account balances
fn build_account_tree(
    prefix: &str,
    account_balances: &HashMap<String, HashMap<String, Decimal>>,
) -> FavaAccountTree {
    let mut children = Vec::new();
    let mut balance: HashMap<String, String> = HashMap::new();

    // Find direct children
    let mut child_prefixes: Vec<String> = account_balances
        .keys()
        .filter(|a| a.starts_with(prefix) && a.as_str() != prefix)
        .filter_map(|a| {
            let rest = a.strip_prefix(prefix)?.strip_prefix(':')?;
            let child_name = rest.split(':').next()?;
            Some(format!("{}:{}", prefix, child_name))
        })
        .collect();
    child_prefixes.sort();
    child_prefixes.dedup();

    for child_prefix in child_prefixes {
        let child_tree = build_account_tree(&child_prefix, account_balances);
        // Add child balance to parent
        for (curr, amt) in &child_tree.balance {
            let existing: Decimal = balance
                .get(curr)
                .and_then(|s| s.parse().ok())
                .unwrap_or_default();
            let child_amt: Decimal = amt.parse().unwrap_or_default();
            balance.insert(curr.clone(), (existing + child_amt).to_string());
        }
        children.push(child_tree);
    }

    // Add own balance if this account has direct entries
    if let Some(own_balance) = account_balances.get(prefix) {
        for (curr, amt) in own_balance {
            let existing: Decimal = balance
                .get(curr)
                .and_then(|s| s.parse().ok())
                .unwrap_or_default();
            balance.insert(curr.clone(), (existing + amt).to_string());
        }
    }

    FavaAccountTree {
        account: prefix.to_string(),
        balance,
        children,
    }
}

/// Fava balance_sheet endpoint
async fn fava_balance_sheet(
    State(state): State<AppState>,
) -> Result<Json<FavaBalanceSheet>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    // Compute balances for all accounts
    let mut account_balances: HashMap<String, HashMap<String, Decimal>> = HashMap::new();

    for spanned in &ledger.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                if let Some(rustledger_core::IncompleteAmount::Complete(units)) = &posting.units {
                    *account_balances
                        .entry(posting.account.to_string())
                        .or_default()
                        .entry(units.currency.to_string())
                        .or_default() += units.number;
                }
            }
        }
    }

    let assets = build_account_tree("Assets", &account_balances);
    let liabilities = build_account_tree("Liabilities", &account_balances);
    let equity = build_account_tree("Equity", &account_balances);

    // Calculate net worth (assets - liabilities)
    let mut net_worth: HashMap<String, String> = HashMap::new();
    for (curr, amt) in &assets.balance {
        let asset_val: Decimal = amt.parse().unwrap_or_default();
        let liab_val: Decimal = liabilities
            .balance
            .get(curr)
            .and_then(|s| s.parse().ok())
            .unwrap_or_default();
        net_worth.insert(curr.clone(), (asset_val + liab_val).to_string());
    }

    Ok(Json(FavaBalanceSheet {
        assets,
        liabilities,
        equity,
        net_worth,
    }))
}

/// Fava income_statement endpoint
async fn fava_income_statement(
    State(state): State<AppState>,
) -> Result<Json<FavaIncomeStatement>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    // Compute balances for income/expense accounts
    let mut account_balances: HashMap<String, HashMap<String, Decimal>> = HashMap::new();

    for spanned in &ledger.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                let account = posting.account.as_str();
                if account.starts_with("Income") || account.starts_with("Expenses") {
                    if let Some(rustledger_core::IncompleteAmount::Complete(units)) = &posting.units
                    {
                        *account_balances
                            .entry(account.to_string())
                            .or_default()
                            .entry(units.currency.to_string())
                            .or_default() += units.number;
                    }
                }
            }
        }
    }

    let income = build_account_tree("Income", &account_balances);
    let expenses = build_account_tree("Expenses", &account_balances);

    // Net income = income - expenses (income is negative in double-entry)
    let mut net_income: HashMap<String, String> = HashMap::new();
    for (curr, amt) in &income.balance {
        let income_val: Decimal = amt.parse().unwrap_or_default();
        let expense_val: Decimal = expenses
            .balance
            .get(curr)
            .and_then(|s| s.parse().ok())
            .unwrap_or_default();
        // Income is negative (credit), expenses positive (debit)
        // Net income = -income - expenses
        net_income.insert(curr.clone(), (-income_val - expense_val).to_string());
    }

    Ok(Json(FavaIncomeStatement {
        income,
        expenses,
        net_income,
    }))
}

/// Fava journal endpoint
async fn fava_journal(
    State(state): State<AppState>,
    Query(params): Query<QueryParams>,
) -> Result<Json<Vec<FavaJournalEntry>>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut entries = Vec::new();
    let limit = params.limit.unwrap_or(500);

    for spanned in ledger.directives.iter().rev() {
        if entries.len() >= limit {
            break;
        }

        let entry = match &spanned.value {
            Directive::Transaction(txn) => {
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

                let postings: Vec<FavaPosting> = txn
                    .postings
                    .iter()
                    .map(|p| {
                        let units = p.units.as_ref().and_then(|u| {
                            if let rustledger_core::IncompleteAmount::Complete(amt) = u {
                                Some(FavaAmount {
                                    number: amt.number.to_string(),
                                    currency: amt.currency.to_string(),
                                })
                            } else {
                                None
                            }
                        });
                        FavaPosting {
                            account: p.account.to_string(),
                            units,
                            cost: None,
                            price: None,
                        }
                    })
                    .collect();

                FavaJournalEntry {
                    entry_type: "Transaction".to_string(),
                    date: txn.date.to_string(),
                    flag: Some(txn.flag.to_string()),
                    payee: txn.payee.as_ref().map(|s| s.to_string()),
                    narration: Some(txn.narration.to_string()),
                    account: None,
                    tags: txn.tags.iter().map(|t| t.to_string()).collect(),
                    links: txn.links.iter().map(|l| l.to_string()).collect(),
                    postings,
                    meta: HashMap::new(),
                }
            }
            Directive::Balance(bal) => FavaJournalEntry {
                entry_type: "Balance".to_string(),
                date: bal.date.to_string(),
                flag: None,
                payee: None,
                narration: None,
                account: Some(bal.account.to_string()),
                tags: Vec::new(),
                links: Vec::new(),
                postings: Vec::new(),
                meta: HashMap::new(),
            },
            Directive::Open(open) => FavaJournalEntry {
                entry_type: "Open".to_string(),
                date: open.date.to_string(),
                flag: None,
                payee: None,
                narration: None,
                account: Some(open.account.to_string()),
                tags: Vec::new(),
                links: Vec::new(),
                postings: Vec::new(),
                meta: HashMap::new(),
            },
            Directive::Close(close) => FavaJournalEntry {
                entry_type: "Close".to_string(),
                date: close.date.to_string(),
                flag: None,
                payee: None,
                narration: None,
                account: Some(close.account.to_string()),
                tags: Vec::new(),
                links: Vec::new(),
                postings: Vec::new(),
                meta: HashMap::new(),
            },
            _ => continue,
        };

        entries.push(entry);
    }

    Ok(Json(entries))
}

/// Fava commodities endpoint with price history
async fn fava_commodities(
    State(state): State<AppState>,
) -> Result<Json<Vec<FavaCommodity>>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    // Collect all prices grouped by currency pair
    let mut price_map: HashMap<(String, String), Vec<(String, String)>> = HashMap::new();

    for spanned in &ledger.directives {
        if let Directive::Price(price) = &spanned.value {
            let key = (
                price.currency.to_string(),
                price.amount.currency.to_string(),
            );
            price_map
                .entry(key)
                .or_default()
                .push((price.date.to_string(), price.amount.number.to_string()));
        }
    }

    let mut commodities: Vec<FavaCommodity> = price_map
        .into_iter()
        .map(|((currency, base), mut prices)| {
            prices.sort_by(|a, b| a.0.cmp(&b.0));
            FavaCommodity {
                currency,
                base,
                prices: prices
                    .into_iter()
                    .map(|(date, price)| FavaPricePoint { date, price })
                    .collect(),
            }
        })
        .collect();

    commodities.sort_by(|a, b| a.currency.cmp(&b.currency));
    Ok(Json(commodities))
}

/// Fava query endpoint (simplified - returns basic SELECT results)
async fn fava_query(
    State(state): State<AppState>,
    Query(params): Query<FavaQueryParams>,
) -> Result<Json<FavaQueryResult>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let query = params.query_string.unwrap_or_default();

    // Simplified query support - just balances for now
    if query.to_lowercase().contains("balances") {
        let mut account_balances: HashMap<String, HashMap<String, Decimal>> = HashMap::new();

        for spanned in &ledger.directives {
            if let Directive::Transaction(txn) = &spanned.value {
                for posting in &txn.postings {
                    if let Some(rustledger_core::IncompleteAmount::Complete(units)) = &posting.units
                    {
                        *account_balances
                            .entry(posting.account.to_string())
                            .or_default()
                            .entry(units.currency.to_string())
                            .or_default() += units.number;
                    }
                }
            }
        }

        let mut rows: Vec<Vec<serde_json::Value>> = Vec::new();
        for (account, balances) in account_balances {
            for (currency, amount) in balances {
                if amount != Decimal::ZERO {
                    rows.push(vec![
                        serde_json::Value::String(account.clone()),
                        serde_json::Value::String(format!("{} {}", amount, currency)),
                    ]);
                }
            }
        }

        return Ok(Json(FavaQueryResult {
            result_type: "table".to_string(),
            columns: vec!["account".to_string(), "balance".to_string()],
            rows,
        }));
    }

    // Default: return empty result
    Ok(Json(FavaQueryResult {
        result_type: "table".to_string(),
        columns: Vec::new(),
        rows: Vec::new(),
    }))
}

/// Fava events endpoint
async fn fava_events(
    State(state): State<AppState>,
) -> Result<Json<Vec<serde_json::Value>>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let mut events = Vec::new();
    for spanned in &ledger.directives {
        if let Directive::Event(event) = &spanned.value {
            events.push(serde_json::json!({
                "date": event.date.to_string(),
                "type": event.event_type.clone(),
                "description": event.value.to_string(),
            }));
        }
    }

    Ok(Json(events))
}

/// Fava errors endpoint
async fn fava_errors(
    State(state): State<AppState>,
) -> Result<Json<Vec<FavaError>>, (StatusCode, Json<ApiError>)> {
    let ledger = load_ledger(&state.ledger_path)?;

    let errors: Vec<FavaError> = ledger
        .errors
        .iter()
        .map(|e| {
            // LoadError is an enum - extract path when available
            let (message, filename) = match e {
                rustledger_loader::LoadError::Io { path, .. } => {
                    (e.to_string(), Some(path.to_string_lossy().to_string()))
                }
                rustledger_loader::LoadError::ParseErrors { path, .. } => {
                    (e.to_string(), Some(path.to_string_lossy().to_string()))
                }
                rustledger_loader::LoadError::PathTraversal { .. } => (e.to_string(), None),
                rustledger_loader::LoadError::IncludeCycle { .. } => (e.to_string(), None),
            };
            FavaError {
                message,
                source: filename.map(|f| FavaErrorSource {
                    filename: f,
                    lineno: 0,
                }),
            }
        })
        .collect();

    Ok(Json(errors))
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
