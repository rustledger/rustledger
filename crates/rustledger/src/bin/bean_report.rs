//! bean-report - Generate reports from beancount files (Python beancount compatibility).
fn main() -> std::process::ExitCode {
    rustledger::cmd::report_cmd::main()
}
