//! bean-check - Validate beancount files (Python beancount compatibility).
fn main() -> std::process::ExitCode {
    rustledger::cmd::check::main_with_name("bean-check")
}
