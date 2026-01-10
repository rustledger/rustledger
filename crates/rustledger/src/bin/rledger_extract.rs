//! rledger-extract - Extract transactions from bank files.
//!
//! Primary binary for extracting transactions from CSV and other bank files.

fn main() -> std::process::ExitCode {
    rustledger::cmd::extract_cmd::main()
}
