//! rledger-check - Validate beancount files.
fn main() -> std::process::ExitCode {
    rustledger::cmd::check::main()
}
