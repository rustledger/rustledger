//! `ag-rledger` - agent-native CLI for rustledger (#1291). DRAFT / SPIKE.
//!
//! This is a minimal skeleton whose purpose is to prove that the
//! `agcli` + `tokio` integration builds in the rustledger workspace and
//! passes the supply-chain gates (`cargo deny`, `cargo vet`, clippy).
//!
//! The full agent-native surface - wiring `check` / `query` / `report` /
//! `doctor` / etc. through `agcli` envelopes and typed exit codes - is
//! the next step; the reference implementation is the contributor's
//! `agledger` binary (matthiasdebernardini/agledger, #1291). It keeps
//! the synchronous `rledger` binary untouched and exposes the agent CLI
//! as this separate async binary.

use agcli::{AgentCli, Command, CommandOutput, NextAction};
use serde_json::json;

#[tokio::main]
async fn main() {
    let cli = AgentCli::new("ag-rledger", "Agent-native plain-text accounting CLI")
        .version(env!("CARGO_PKG_VERSION"))
        .command(
            Command::new("ping", "Liveness check (skeleton)")
                .usage("ag-rledger ping")
                .handler(|_req, _ctx| {
                    Box::pin(async move {
                        Ok(CommandOutput::new(json!({ "pong": true })).next_action(
                            NextAction::new("ag-rledger ping", "Re-run the liveness check"),
                        ))
                    })
                }),
        );

    let run = cli.run_env().await;
    println!("{}", run.to_json());
    std::process::exit(run.exit_code());
}
