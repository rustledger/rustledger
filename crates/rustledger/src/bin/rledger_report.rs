//! rledger-report - Generate reports from beancount files.
fn main() -> std::process::ExitCode {
    rustledger::cmd::report_cmd::main()
}
