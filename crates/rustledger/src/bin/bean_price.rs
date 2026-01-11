//! bean-price - Fetch current prices for commodities.
//!
//! Compatibility binary for Python beancount users.

fn main() -> std::process::ExitCode {
    rustledger::cmd::price_cmd::main_with_name("bean-price")
}
