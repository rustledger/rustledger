//! rledger-web - REST API server for rustledger.
//!
//! Provides JSON API access to ledger data.

fn main() -> std::process::ExitCode {
    rustledger::cmd::web_cmd::main()
}
