//! rledger-report - Generate reports from beancount files.
fn main() -> std::process::ExitCode {
    rustledger_cli::cmd::report_cmd::main()
}
