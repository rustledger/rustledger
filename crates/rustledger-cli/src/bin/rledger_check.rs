//! rledger-check - Validate beancount files.
fn main() -> std::process::ExitCode {
    rustledger_cli::cmd::check::main()
}
