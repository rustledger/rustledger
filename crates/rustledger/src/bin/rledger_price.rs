//! rledger-price - Fetch current prices for commodities.
//!
//! Primary binary for fetching commodity prices from online sources.

fn main() -> std::process::ExitCode {
    rustledger::cmd::price_cmd::main()
}
