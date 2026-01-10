//! bean-extract - Python beancount compatibility wrapper.
//!
//! This binary provides backwards compatibility with bean-extract from Python beancount.
//! It delegates to the rledger-extract implementation.

fn main() -> std::process::ExitCode {
    rustledger::cmd::extract_cmd::main_with_name("bean-extract")
}
