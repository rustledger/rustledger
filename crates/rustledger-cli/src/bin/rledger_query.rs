//! rledger-query - Query beancount files with BQL.
fn main() -> std::process::ExitCode {
    rustledger_cli::cmd::query::main()
}
