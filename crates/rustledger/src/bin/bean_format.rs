//! bean-format - Format beancount files (Python beancount compatibility).
fn main() -> std::process::ExitCode {
    rustledger::cmd::format::main_with_name("bean-format")
}
