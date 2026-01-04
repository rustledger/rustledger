//! rledger-doctor - Debugging tools for beancount files.
fn main() -> std::process::ExitCode {
    rustledger_cli::cmd::doctor::main()
}
