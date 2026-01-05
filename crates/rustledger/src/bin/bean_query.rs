//! bean-query - Query beancount files with BQL (Python beancount compatibility).
fn main() -> std::process::ExitCode {
    rustledger::cmd::query::main_with_name("bean-query")
}
