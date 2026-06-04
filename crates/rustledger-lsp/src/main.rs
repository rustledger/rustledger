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
                .add_directive("rledger_lsp=info".parse().unwrap()),
        )
        .with_writer(std::io::stderr)
        .init();

    // Run the server. `start_stdio` drains the writer thread before
    // returning, so by the time we convert the code into an ExitCode
    // the client has already received the shutdown response.
    // `process::exit` would still work, but returning ExitCode lets
    // Rust's main runtime do any final cleanup it has.
    match rustledger_lsp::start_stdio() {
        Ok(0) => ExitCode::SUCCESS,
        Ok(code) => {
            // `code` is the exit code the client requested via the
            // `exit` notification (1 = exit without prior shutdown,
            // per LSP spec). Truncating to u8 mirrors what process::exit
            // would do — exit codes outside 0..=255 are not portable.
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            ExitCode::from(code as u8)
        }
        Err(e) => {
            tracing::error!("Server error: {}", e);
            ExitCode::FAILURE
        }
    }
}
