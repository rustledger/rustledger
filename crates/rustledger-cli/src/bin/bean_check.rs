//! bean-check - Validate beancount files (Python beancount compatibility).
fn main() -> std::process::ExitCode {
    rustledger_cli::cmd::check::main()
}
