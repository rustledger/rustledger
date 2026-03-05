//! Beancount Language Server.
//!
//! Usage:
//!   rledger-lsp              # Start LSP server (stdio)
//!   rledger-lsp --version    # Print version
//!   rledger-lsp --help       # Print help

use std::process::ExitCode;

fn main() -> ExitCode {
    // Parse simple args (no clap needed for LSP server)
    let args: Vec<String> = std::env::args().collect();

    if args.iter().any(|a| a == "--version" || a == "-V") {
        println!("rledger-lsp {}", rustledger_lsp::VERSION);
        return ExitCode::SUCCESS;
    }

    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("Beancount Language Server");
        println!();
        println!("Usage: rledger-lsp [OPTIONS]");
        println!();
        println!("Options:");
        println!("  -h, --help     Print help");
        println!("  -V, --version  Print version");
        println!();
        println!("The server communicates via stdio using the Language Server Protocol.");
        println!();
        println!("Environment variables:");
        println!("  RUST_LOG       Set log level (e.g., RUST_LOG=rledger_lsp=debug)");
        return ExitCode::SUCCESS;
    }

    // Initialize tracing (logs to stderr, not stdout which is for LSP)
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("rledger_lsp=info".parse().unwrap())
                .add_directive("rustledger_lsp=info".parse().unwrap()),
        )
        .with_writer(std::io::stderr)
        .init();

    // Run the server
    match rustledger_lsp::start_stdio() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            tracing::error!("Server error: {}", e);
            ExitCode::FAILURE
        }
    }
}
