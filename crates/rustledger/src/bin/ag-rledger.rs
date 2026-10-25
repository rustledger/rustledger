//! `ag-rledger` - agent-native CLI for the rustledger workspace (#1291).
//!
//! This binary is intentionally additive: `rledger` remains the upstream-style
//! clap CLI, while `ag-rledger` exposes the same accounting commands through
//! `agcli` JSON envelopes for agents. Every command buffers the underlying
//! `cmd::*` output, wraps it in a structured result (with a typed exit code and
//! a HATEOAS `next_action`), and emits a single JSON envelope.
//!
//! The command surface and wiring are adapted from the contributor's
//! `agledger` binary (matthiasdebernardini/agledger, #1291), which targeted
//! `agcli 0.10.2`. This branch targets `agcli 0.13.0`: the `CommandRequest` /
//! `CommandOutput` / `CommandError` / `ExitCode` shapes are the same, but each
//! command opts out of the 0.13 unknown-flag / extra-positional rejection
//! (`allow_unknown_flags` / `allow_extra_args`) because these handlers forward
//! arbitrary flags through to the rustledger `cmd::*` argument structs rather
//! than re-declaring every flag in the usage string. A flag the handler does
//! not read is still refused, by `Req::reject_unread` rather than by agcli,
//! so nothing is silently ignored. The naming is `ag-rledger` (mirroring
//! `rledger`), not `agledger`.

use agcli::{
    ActionParam, AgentCli, Command, CommandError, CommandOutput, ExecutionContext, NextAction,
};
use rustledger::cmd::report_cmd::{CollectedDiagnostics, Diagnostic};
use rustledger::cmd::restructure::{self, Check, Outcome, Step, merge, split};
use rustledger::config::Config;
use rustledger::plugin_budget::PluginBudgetArgs;
use serde_json::{Value, json};
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::ExitCode as ProcessExitCode;
use std::sync::OnceLock;

const SCHEMA_VERSION: &str = "ag-rledger.v1";

#[tokio::main]
async fn main() {
    let args = expand_config_aliases(std::env::args().collect());
    let cli = build_cli();
    let mut ctx = ExecutionContext::default();
    let run = cli.run_argv_with_context(args, &mut ctx).await;
    // The envelope's records carry ledger strings: DEL, C1, bidi controls
    // and line separators are written as `\uXXXX`, the same JSON value, so
    // whoever reads the envelope raw is not acted on (#2714).
    println!(
        "{}",
        rustledger::cmd::escape_display_unsafe_in_json(&run.to_json())
    );
    std::process::exit(run.exit_code());
}

/// The `rledger` commands `ag-rledger` deliberately does not offer, each
/// with why. Listed in the root envelope (`unsupported_commands`), and each
/// refused by name with code `UNSUPPORTED`, so an agent learns it is not
/// available rather than meeting an unknown command.
///
/// The drift guard in `tests/ag_rledger_test.rs` fails when `rledger` has a
/// command that is neither offered here nor listed in this table (#2567).
const UNSUPPORTED_COMMANDS: &[(&str, &str)] = &[(
    "completions",
    "it writes a shell completion script, which is for an interactive shell, not an agent",
)];

fn build_cli() -> AgentCli {
    let mut cli = AgentCli::new("ag-rledger", "Agent-native plain-text accounting CLI")
        .version(env!("CARGO_PKG_VERSION"))
        .schema_version(SCHEMA_VERSION)
        .root_field(
            "compatibility",
            json!({
                "engine": "rustledger",
                "syntax": "beancount",
                "upstream_binary": "rledger",
                "attribution": "command surface adapted from matthiasdebernardini/agledger (#1291)"
            }),
        )
        .command(check_command("check", "Validate beancount files"))
        .command(check_command("c", "Alias for check"))
        .command(query_command("query", "Query beancount files with BQL"))
        .command(query_command("q", "Alias for query"))
        .command(format_command("format", "Format beancount files"))
        .command(format_command("fmt", "Alias for format"))
        .command(report_command("report", "Generate financial reports"))
        .command(report_command("r", "Alias for report"))
        .command(doctor_command(
            "doctor",
            "Debug and inspect beancount files",
        ))
        .command(doctor_command("d", "Alias for doctor"))
        .command(extract_command(
            "extract",
            "Extract transactions from bank files",
        ))
        .command(extract_command("x", "Alias for extract"))
        .command(price_command("price", "Fetch commodity prices"))
        .command(price_command("p", "Alias for price"))
        .command(config_command("config", "Manage rledger configuration"))
        .command(config_command("cfg", "Alias for config"))
        .command(add_command("add", "Add a transaction in quick mode"))
        .command(add_command("a", "Alias for add"))
        .command(compat_command())
        .command(explain_command())
        .command(lint_command())
        .command(split_command())
        .command(merge_command())
        .root_field(
            "unsupported_commands",
            json!(
                UNSUPPORTED_COMMANDS
                    .iter()
                    .map(|(name, why)| json!({"command": name, "reason": why}))
                    .collect::<Vec<_>>()
            ),
        );
    for (name, why) in UNSUPPORTED_COMMANDS {
        cli = cli.command(unsupported_command(name, why));
    }

    debug_assert!(
        cli.audit().is_clean(),
        "ag-rledger command tree should be agent-auditable: {:?}",
        cli.audit()
    );
    cli
}

/// A command `rledger` has and `ag-rledger` does not offer (see
/// [`UNSUPPORTED_COMMANDS`]): refused by name, saying why.
fn unsupported_command(name: &'static str, why: &'static str) -> Command {
    Command::new(
        name,
        "Not offered by ag-rledger (see `unsupported_commands`)",
    )
    .usage("ag-rledger <command> (not offered; use rledger)")
    .allow_unknown_flags()
    .allow_extra_args()
    .default_next_action(NextAction::new(
        "ag-rledger",
        "List the commands ag-rledger offers",
    ))
    .handler(move |_req, _ctx| {
        Box::pin(async move {
            Err(CommandError::new(
                format!("`{name}` is not offered by ag-rledger: {why}"),
                "UNSUPPORTED",
                format!("Run `rledger {name}` instead."),
            )
            .exit_code(agcli::ExitCode::USAGE))
        })
    })
}

fn check_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger check [<file>] [--format <format>] [--json] [--verbose] [-v] [--quiet] \
             [-q] [--no-cache] [-C] [--auto] [-a] [--native-plugin <name>] [--lint <name>]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger check <file> --format=json",
            "Validate a ledger and return diagnostics as JSON",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("check", req, build_check_args);
            Box::pin(async move {
                let (mut args, globals) = parsed?;
                let config = load_config(&globals.budget)?;
                if args.file.is_none() {
                    args.file = default_file(&config, globals.profile.as_deref());
                }
                run_buffered_with_stderr("check", |out, err| {
                    rustledger::cmd::check::run_with_writer(&args, out, err).map(exit_code_to_i32)
                })
            })
        })
}

fn query_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger query [<file>] <query...> [--file <file>] [--query-file <file>] \
             [--output <file>] [--format <format>] [--numberify] [-m] [--no-errors] [-q] \
             [--verbose] [-v]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(
            NextAction::new(
                "ag-rledger query <file> \"SELECT account, sum(position) GROUP BY account\" --format=json",
                "Run a structured balance query",
            )
            .with_param("file", ActionParam::new().required(true))
            .with_param("query", ActionParam::new().required(true)),
        )
        .handler(|req, _ctx| {
            let parsed = parse_request("query", req, build_query_args);
            Box::pin(async move {
                let (mut args, globals) = parsed?;
                let config = load_config(&globals.budget)?;
                if args.file.is_none() {
                    args.file = default_file(&config, globals.profile.as_deref());
                }
                if args.format.is_none()
                    && let Some(fmt) = config.commands.query.output.format.as_deref()
                {
                    args.format = rustledger::cmd::query::OutputFormat::from_str_config(fmt);
                }
                if args.query.is_empty() && args.query_file.is_none() {
                    return Err(CommandError::new(
                        "query text is required for ag-rledger query",
                        "MISSING_QUERY",
                        "Pass a BQL query as positional text or use --query-file. Use rledger query for the interactive REPL.",
                    )
                    .exit_code(agcli::ExitCode::USAGE));
                }
                run_buffered_with_warnings("query", |out, warnings, err| {
                    rustledger::cmd::query::run_with_writer(&args, out, Some(warnings), err)
                        .map(|()| 0)
                })
            })
        })
}

fn format_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger format [<file>...] [--output <file>] [--in-place] [-i] [--check] [--diff] \
             [--ledger <root>] [--no-ledger] [--verbose] [-v]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger format <file> --check",
            "Check whether a ledger is in canonical format",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("format", req, build_format_args);
            Box::pin(async move {
                let (mut args, globals) = parsed?;
                let config = load_config(&globals.budget)?;
                if args.files.is_empty()
                    && let Some(file) = default_file(&config, globals.profile.as_deref())
                {
                    args.files.push(file);
                }
                run_buffered_with_stderr("format", |out, err| {
                    rustledger::cmd::format::run_with_writer(&args, out, err).map(exit_code_to_i32)
                })
            })
        })
}

/// One report-specific flag, as `rledger` defines it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ReportFlag {
    long: String,
    short: Option<char>,
    /// The value it takes (`ACCOUNT`), or `None` for a boolean switch.
    value: Option<String>,
}

/// Each report and the report-specific flags it reads, taken from `rledger`'s
/// own clap definition of `report` (`cmd::report_cmd::Report`).
///
/// One definition, used to build the usage string, to reject a flag that
/// does not apply, and to list the valid report names. They disagreed
/// before: the usage string advertised the UNION for every report,
/// `allow_unknown_flags` removed the safety net, and `build_report` read only
/// the flags its variant had a field for — so `report income --from
/// 2015-01-01` returned the whole-history figure with `"ok": true` (#2280).
/// A hand-kept table here fixed that, and then had to be kept in step with
/// `rledger` by hand; reading the clap definition means a flag `rledger`
/// gains is in the table the moment it exists, and the drift guard
/// (`ag_rledger_reads_every_rledger_flag_or_refuses_it`) fails until
/// `build_report` reads it (#2567).
///
/// Flags handled for every report — `--file`, `--format`, `--verbose`,
/// `--no-cache`, `--select`, `--compact`, `--profile` — are `report`'s own
/// (global) flags, not a report's, so they are absent here.
fn report_flags() -> &'static [(String, Vec<ReportFlag>)] {
    static FLAGS: OnceLock<Vec<(String, Vec<ReportFlag>)>> = OnceLock::new();
    FLAGS.get_or_init(|| {
        use clap::Args as _;
        let report = rustledger::cmd::report_cmd::Args::augment_args(clap::Command::new("report"));
        report
            .get_subcommands()
            .map(|sub| {
                let flags = sub
                    .get_arguments()
                    .filter(|arg| !arg.is_positional())
                    .filter_map(|arg| {
                        let long = arg.get_long()?;
                        (long != "help").then(|| ReportFlag {
                            long: long.to_string(),
                            short: arg.get_short(),
                            value: arg.get_action().takes_values().then(|| {
                                arg.get_value_names()
                                    .and_then(|names| names.first())
                                    .map_or_else(
                                        || long.to_ascii_uppercase().replace('-', "_"),
                                        ToString::to_string,
                                    )
                            }),
                        })
                    })
                    .collect();
                (sub.get_name().to_string(), flags)
            })
            .collect()
    })
}

/// The report-specific flags `report` reads, or `None` for an unknown
/// report.
fn flags_of(report: &str) -> Option<&'static [ReportFlag]> {
    report_flags()
        .iter()
        .find(|(name, _)| name == report)
        .map(|(_, flags)| flags.as_slice())
}

/// The report-specific flags, grouped by report, for the usage string.
///
/// Built from [`report_flags`] so the usage text cannot promise a flag the
/// handler ignores. Bracketed as agcli reads a usage string: a flag without
/// a `<VALUE>` is a boolean switch, so `--irr ledger.beancount` does not take
/// the file as the switch's value.
fn report_flag_usage() -> String {
    report_flags()
        .iter()
        .filter(|(_, flags)| !flags.is_empty())
        .map(|(report, flags)| {
            let rendered: Vec<String> = flags
                .iter()
                .map(|f| {
                    let mut spelled = format!("--{}", f.long);
                    if let Some(short) = f.short {
                        spelled.push_str(&format!("/-{short}"));
                    }
                    match &f.value {
                        Some(value) => format!("[{spelled} <{value}>]"),
                        None => format!("[{spelled}]"),
                    }
                })
                .collect();
            format!("{report}: {}", rendered.join(" "))
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// Reject a report-specific flag that the named report does not read.
///
/// Native `rledger` already rejects these (`error: unexpected argument
/// '--from' found`). The agent surface accepted them and returned an
/// unfiltered figure with a success envelope, which is the worse of the two
/// failures: nothing downstream can notice (#2280).
fn reject_inapplicable_flags(report_name: &str, req: &Req<'_>) -> Result<(), CommandError> {
    let Some(canonical) = parse_report_name(report_name) else {
        // An unknown report name is reported by `build_report`, with the list
        // of valid ones. Saying it twice, differently, would be worse.
        return Ok(());
    };
    let Some(applicable) = flags_of(&canonical) else {
        return Ok(());
    };
    let applies = |long: &str| applicable.iter().any(|f| f.long == long);
    // A short form this report reads is its own, whichever other report's
    // flag shares the letter: `-c` is `prices --commodity` and `networth
    // --currency`, and must not be refused on `prices` as the currency.
    let short_applies = |short: char| applicable.iter().any(|f| f.short == Some(short));

    // Every report-specific flag known to any report; anything outside this set
    // is a global flag or a genuine unknown, neither of which is ours to judge.
    // Deduplicated: `account` appears in several entries, and listing it
    // several times in the error would be its own small confusion.
    //
    // Long and short spellings are judged apart: a report can read a flag's
    // long form without its short one. `journal` reads `--year` (the shared
    // date window) but not `capgains`'s `-y`, so `journal -y 2024` must be
    // refused, not dropped because the long name applies.
    let mut supplied: Vec<String> = report_flags()
        .iter()
        .flat_map(|(_, flags)| flags.iter())
        .filter_map(|f| {
            let short = f.short.filter(|s| !short_applies(*s));
            if !applies(&f.long) && flag_was_supplied(req, &f.long, None) {
                Some(match f.short {
                    Some(s) => format!("--{}/-{s}", f.long),
                    None => format!("--{}", f.long),
                })
            } else if let Some(short) = short
                && flag_was_supplied(req, "", Some(short))
            {
                Some(format!("--{}/-{short}", f.long))
            } else {
                None
            }
        })
        .collect();
    supplied.sort_unstable();
    supplied.dedup();

    if supplied.is_empty() {
        return Ok(());
    }

    let hint = if applicable.is_empty() {
        format!("`{canonical}` takes no report-specific flags.")
    } else {
        let ok: Vec<String> = applicable.iter().map(|f| format!("--{}", f.long)).collect();
        format!("`{canonical}` accepts: {}.", ok.join(", "))
    };
    // A distinct code, not a generic usage error: an agent that asked for a
    // date window needs to tell "the window was refused" apart from "the file
    // was wrong", and act on it.
    Err(CommandError::new(
        format!(
            "report `{canonical}` does not accept {}",
            supplied.join(", ")
        ),
        "INAPPLICABLE_FLAG",
        hint,
    )
    .exit_code(agcli::ExitCode::USAGE))
}

/// Whether `--flag` (or `--flag=value`) appears in the raw invocation.
///
/// Read from the raw args rather than the parsed flags because a flag the
/// handler never reads leaves no other trace — which is precisely how these
/// went unnoticed.
fn flag_was_supplied(req: &Req<'_>, long: &str, short: Option<char>) -> bool {
    let mut spellings = Vec::new();
    if !long.is_empty() {
        spellings.push(format!("--{long}"));
        spellings.push(format!("--{long}="));
    }
    if let Some(short) = short {
        spellings.push(format!("-{short}"));
        spellings.push(format!("-{short}="));
    }
    req.invocation().raw_args().iter().any(|arg| {
        spellings.iter().any(|s| {
            if s.ends_with('=') {
                arg.starts_with(s)
            } else {
                arg == s
            }
        })
    })
}

/// The usage string, built once.
///
/// `Command::usage` wants a `&'static str` and the report-specific part is
/// computed from [`report_flags`]. Leaking a fresh `Box` per call would leak
/// once for `report` and again for the `r` alias, in a binary that may be
/// driven as a long-running agent process. A `OnceLock` gives the same
/// `'static` lifetime with one allocation for the life of the process.
fn report_usage() -> &'static str {
    static USAGE: OnceLock<String> = OnceLock::new();
    USAGE
        .get_or_init(|| {
            format!(
                "ag-rledger report [<file>] <report> [--file <file>] [--format <format>] \
             [--verbose] [-v] [--no-cache]  |  report-specific flags \u{2014} {}",
                report_flag_usage()
            )
        })
        .as_str()
}

/// A command's usage string, with the flags `rledger` takes on every
/// command appended. The plugin-budget part is generated from
/// [`PluginBudgetArgs`], the definition both binaries parse.
fn with_globals(base: &str) -> String {
    let mut usage = format!("{base} [--profile <name>] [-P <name>]");
    for (long, value) in PluginBudgetArgs::flags() {
        usage.push_str(&format!(" [--{long} <{}>]", value.to_ascii_lowercase()));
    }
    usage
}

fn report_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(report_usage()))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger report <file> balances --format=json",
            "Get balances as JSON",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("report", req, build_report_args);
            Box::pin(async move {
                let (args, globals) = parsed?;
                let config = load_config(&globals.budget)?;
                let file = args
                    .file
                    .or_else(|| default_file(&config, globals.profile.as_deref()))
                    .ok_or_else(|| missing_file_error("report"))?;
                let format = match args.format {
                    Some(format) => format,
                    None => report_format(
                        config
                            .commands
                            .report
                            .output
                            .format
                            .as_deref()
                            .unwrap_or("text"),
                    )?,
                };
                run_buffered_with_warnings("report", |out, warnings, err| {
                    rustledger::cmd::report_cmd::run_with_writer(
                        &file,
                        &args.report,
                        args.verbose,
                        args.no_cache,
                        &format,
                        out,
                        warnings,
                        err,
                    )
                    .map(|()| 0)
                })
            })
        })
}

fn doctor_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger doctor <subcommand> [args...] [--verbose] [-v] [--conversion <value>] \
             [--output <dir>] [--count <n>] [--seed <n>] [--skip-validation] [--manifest] \
             [--edge-cases-only]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger doctor <subcommand> [args...]",
            "Run a doctor subcommand",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("doctor", req, build_doctor_command);
            Box::pin(async move {
                let (command, globals) = parsed?;
                // Read for its errors and the plugin budget, as `rledger`
                // does for every command but `config`.
                load_config(&globals.budget)?;
                run_buffered("doctor", |out| {
                    rustledger::cmd::doctor::run_with_writer(command, out).map(|()| 0)
                })
            })
        })
}

fn extract_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger extract [<file>] [--file <file>] [--list-importers] [--importer <name>] \
             [--config <file>] [--account <account>] [--currency <currency>] [--auto] \
             [--invert-sign] [--include-zero-amounts] [--no-header] \
             [--output <file>] [--existing <file>] [--suggest-categories] [--balance <amount>]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger extract <file> --account=<account>",
            "Convert a bank file to beancount directives",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("extract", req, build_extract_args);
            Box::pin(async move {
                let (args, globals) = parsed?;
                // A WASM importer runs under the plugin budget.
                load_config(&globals.budget)?;
                if args.list_importers {
                    return run_buffered_with_warnings(
                        "extract list-importers",
                        |out, warnings, err| {
                            rustledger::cmd::extract_cmd::list_importers_with_writer(
                                &args,
                                out,
                                Some(warnings),
                                err,
                            )
                            .map(|()| 0)
                        },
                    );
                }
                // Do NOT fall back to `default.file`: that is the ledger
                // path, whereas `extract` reads a *bank statement* to import.
                // Defaulting to the ledger would try to parse it as a
                // statement. Require an explicit input (positional or --file).
                let file = args
                    .file
                    .clone()
                    .ok_or_else(|| missing_file_error("extract"))?;
                run_buffered_with_warnings("extract", |out, warnings, err| {
                    rustledger::cmd::extract_cmd::run_with_writer(
                        &args,
                        &file,
                        out,
                        Some(warnings),
                        err,
                    )
                    .map(|()| 0)
                })
            })
        })
}

fn price_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger price [<symbol>...] [--file <file>] [--currency <currency>] [--date <date>] \
             [--beancount] [-b] [--verbose] [-v] [--mapping <from:to>] [--source <source>] \
             [--source-cmd <cmd>] [--list-sources] [--clear-cache] [--inactive] \
             [--undeclared] [--all-commodities] [-n] [--clobber] [-C]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .handles_dry_run()
        .default_next_action(NextAction::new(
            "ag-rledger price --file <file> --dry-run",
            "Preview price fetches without network calls",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("price", req, build_price_args);
            Box::pin(async move {
                let (args, globals) = parsed?;
                let config = load_config(&globals.budget)?;
                run_buffered_with_warnings("price", |out, warnings, err| {
                    rustledger::cmd::price_cmd::run_with_writer(
                        &args,
                        &config.price,
                        out,
                        Some(warnings),
                        err,
                    )
                    .map(|()| 0)
                })
            })
        })
}

fn config_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger config <show|path|edit|init|aliases> [--raw] [--format <format>] \
             [--project] [--system] [--force] [-f]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger config <subcommand> [--format=<format>]",
            "Run a configuration subcommand",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("config", req, build_config_args);
            Box::pin(async move {
                // No `load_config` here: `config` is how a broken file is
                // shown and fixed, so it must run when the file does not
                // load (as in `rledger`, #1306).
                let (args, _globals) = parsed?;
                run_buffered("config", |out| {
                    rustledger::cmd::config_cmd::run_with_writer(&args, out).map(|()| 0)
                })
            })
        })
}

fn add_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(with_globals(
            "ag-rledger add [<file>] --quick <payee> <narration> <account> <amount> <account> \
             [--file <file>] [--date <date>] [--no-completion] [-n] [-y]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .handles_dry_run()
        .default_next_action(NextAction::new(
            "ag-rledger add <file> --quick <payee> <narration> <account> <amount> <account> --dry-run",
            "Preview a transaction without editing the ledger",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("add", req, build_add_args);
            Box::pin(async move {
                let (args, globals) = parsed?;
                // The agent path never prompts on stdin. Mutating the ledger
                // without an explicit confirmation (and silently defaulting to
                // "yes" on EOF) is unsafe, so require `--yes`/`--dry-run`
                // up front and return a clean USAGE error otherwise (M3).
                if !args.yes && !args.dry_run {
                    return Err(CommandError::new(
                        "ag-rledger add needs explicit confirmation",
                        "CONFIRMATION_REQUIRED",
                        "Pass --yes to append the transaction, or --dry-run to preview it without modifying the ledger.",
                    )
                    .exit_code(agcli::ExitCode::USAGE));
                }
                let config = load_config(&globals.budget)?;
                let file = args
                    .file
                    .clone()
                    .or_else(|| default_file(&config, globals.profile.as_deref()))
                    .ok_or_else(|| missing_file_error("add"))?;
                run_buffered("add", |out| {
                    rustledger::cmd::add_cmd::run_quick_with_writer(&args, &file, out).map(|()| 0)
                })
            })
        })
}

fn compat_command() -> Command {
    Command::new(
        "compat",
        "Install or uninstall bean-* compatibility wrappers",
    )
    .usage(with_globals(
        "ag-rledger compat <install|uninstall> [--prefix <dir>]",
    ))
    .allow_unknown_flags()
    .allow_extra_args()
    .default_next_action(NextAction::new(
        "ag-rledger compat <action> [--prefix=<dir>]",
        "Install or uninstall bean-* wrappers",
    ))
    .handler(|req, _ctx| {
        let parsed = parse_request("compat", req, |req| {
            Ok((
                req.arg(0).map(str::to_string),
                path_flag(req, "prefix", None),
            ))
        });
        Box::pin(async move {
            let ((action, prefix), globals) = parsed?;
            load_config(&globals.budget)?;
            let action = action.ok_or_else(|| {
                CommandError::new(
                    "compat action is required",
                    "MISSING_ACTION",
                    "Use `install` or `uninstall`.",
                )
                .exit_code(agcli::ExitCode::USAGE)
            })?;
            match action.as_str() {
                "install" => run_buffered_with_stderr("compat install", |out, err| {
                    rustledger::cmd::compat::install_with_writer(prefix.as_deref(), out, err)
                        .map(|()| 0)
                }),
                "uninstall" => run_buffered_with_stderr("compat uninstall", |out, err| {
                    rustledger::cmd::compat::uninstall_with_writer(prefix.as_deref(), out, err)
                        .map(|()| 0)
                }),
                _ => Err(CommandError::new(
                    format!("unknown compat action: {action}"),
                    "UNKNOWN_ACTION",
                    "Use `install` or `uninstall`.",
                )
                .exit_code(agcli::ExitCode::USAGE)),
            }
        })
    })
}

fn explain_command() -> Command {
    Command::new(
        "explain",
        "Explain a validation error code (e.g. E2001), or list all codes",
    )
    .usage(with_globals("ag-rledger explain [<code>]"))
    .allow_unknown_flags()
    .allow_extra_args()
    .default_next_action(NextAction::new(
        "ag-rledger explain <code>",
        "Explain what a validation error code means and how to fix it",
    ))
    .handler(|req, _ctx| {
        let parsed = parse_request("explain", req, build_explain_args);
        Box::pin(async move {
            let (args, globals) = parsed?;
            // Read for its errors, as `rledger` does for every command but
            // `config`.
            load_config(&globals.budget)?;
            run_buffered("explain", |out| {
                // Exit status 1 for a code that does not exist, as in
                // `rledger`; the text saying so is in `result.stdout`.
                rustledger::cmd::explain::run_with_writer(&args, out).map(i32::from)
            })
        })
    })
}

fn build_explain_args(req: &Req<'_>) -> Result<rustledger::cmd::explain::Args, CommandError> {
    if req.positionals().len() > 1 {
        return Err(CommandError::new(
            "explain takes at most one error code",
            "INVALID_ARGS",
            "Pass one code (e.g. E2001), or none to list them all.",
        )
        .exit_code(agcli::ExitCode::USAGE));
    }
    Ok(rustledger::cmd::explain::Args {
        code: req.arg(0).map(str::to_string),
    })
}

fn lint_command() -> Command {
    Command::new("lint", "Run non-fatal advisory passes")
        .usage(with_globals(
            "ag-rledger lint <transfers|closed-nonempty|control-chars> <file>... [--format <format>]  |  \
             transfers: [--min-confidence <n>] [--date-window <days>] \
             [--amount-tolerance <amount>] [--apply]",
        ))
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger lint <lint> <file> [--format=<format>]",
            "Run an advisory lint",
        ))
        .handler(|req, _ctx| {
            let parsed = parse_request("lint", req, build_lint_args);
            Box::pin(async move {
                let (args, globals) = parsed?;
                load_config(&globals.budget)?;
                run_buffered("lint", |out| {
                    rustledger::cmd::lint::run_with_writer(&args, out).map(exit_code_to_i32)
                })
            })
        })
}

/// `rledger split`'s own clap definition, which the flags, the usage string
/// and the drift guard are all read from.
fn split_definition() -> clap::Command {
    use clap::Args as _;
    split::Args::augment_args(clap::Command::new("split"))
}

/// `rledger merge`'s own clap definition. See [`split_definition`].
fn merge_definition() -> clap::Command {
    use clap::Args as _;
    merge::Args::augment_args(clap::Command::new("merge"))
}

/// The usage string for a command whose flags are `definition`'s, plus the
/// confirmation `ag-rledger` adds.
///
/// Built from `rledger`'s clap definition, so the usage cannot promise a
/// flag the handler does not read, or omit one `rledger` gains. A switch is
/// written `[--keep-included]` and its short form separately as `[-n]`,
/// which is how agcli knows neither takes the next argument as its value:
/// `--dry-run ledger.beancount` must keep the file as the positional.
fn clap_usage(command: &str, definition: &clap::Command) -> String {
    let mut parts = vec![format!("ag-rledger {command}")];
    for arg in definition.get_arguments() {
        let value = arg
            .get_value_names()
            .and_then(|names| names.first())
            .map_or_else(
                || arg.get_id().as_str().to_ascii_uppercase(),
                ToString::to_string,
            );
        if arg.is_positional() {
            parts.push(format!("[<{}>]", value.to_ascii_lowercase()));
            continue;
        }
        let Some(long) = arg.get_long() else { continue };
        if long == "help" {
            continue;
        }
        if arg.get_action().takes_values() {
            let choices: Vec<String> = arg
                .get_possible_values()
                .iter()
                .map(|v| v.get_name().to_string())
                .collect();
            let placeholder = if choices.is_empty() {
                value
            } else {
                choices.join("|")
            };
            if arg.is_required_set() {
                parts.push(format!("--{long} <{placeholder}>"));
            } else {
                parts.push(format!("[--{long} <{placeholder}>]"));
            }
            // Spelled on its own, so agcli sees `-o` as a declared flag.
            if let Some(short) = arg.get_short() {
                parts.push(format!("[-{short} <{placeholder}>]"));
            }
        } else {
            // agcli already reads `--dry-run` as a switch; declaring a
            // reserved flag again is an audit warning.
            if !RESERVED_SWITCHES.contains(&long) {
                parts.push(format!("[--{long}]"));
            }
            if let Some(short) = arg.get_short() {
                parts.push(format!("[-{short}]"));
            }
        }
    }
    // `--yes` is reserved too; only its short form needs declaring.
    parts.push("[-y]".to_string());
    parts.join(" ")
}

/// agcli's reserved boolean flags that `split`/`merge` also take: already
/// switches on every command, so the usage string does not redeclare them.
const RESERVED_SWITCHES: &[&str] = &["dry-run", "yes"];

/// A path-valued flag's value, refusing one given without a value.
///
/// agcli turns a value flag with nothing after it (`-o` last, or `--dir
/// --yes`) into the value `"true"`. Taken as a path, `merge --yes -o` wrote
/// the merged ledger to `./true` and `split --dir --yes` wrote the period
/// files into `./true/`, past an equivalence check that had no reason to
/// object. A path really named `true` is still taken when it was typed
/// (`--dir true` or `--dir=true`).
fn path_value(
    req: &Req<'_>,
    long: &str,
    short: Option<&str>,
) -> Result<Option<PathBuf>, CommandError> {
    let Some(value) = flag(req, long, short) else {
        return Ok(None);
    };
    // The spelling the value came from (the long one wins, see [`flag`]),
    // and whether `true` was typed as ITS value: `--dir=true`, or `--dir`
    // followed by `true`. Another flag's `--yes=true`, or a positional
    // named `true`, says nothing about this one.
    let spelling = if req.invocation().flag(long).is_some() {
        format!("--{long}")
    } else {
        format!("-{}", short.unwrap_or_default())
    };
    let raw = req.invocation().raw_args();
    let typed = raw.iter().enumerate().any(|(i, arg)| {
        *arg == format!("{spelling}=true")
            || (*arg == spelling && raw.get(i + 1).is_some_and(|next| next == "true"))
    });
    if value.is_empty() || (value == "true" && !typed) {
        return Err(CommandError::new(
            format!("--{long} needs a value"),
            "MISSING_VALUE",
            format!("Pass a path after --{long}."),
        )
        .exit_code(agcli::ExitCode::USAGE));
    }
    Ok(Some(PathBuf::from(value)))
}

/// Refuse two flags `definition` says conflict (`merge --output` with
/// `--ledger`), as `rledger`'s clap parse does.
fn reject_conflicts(
    command: &str,
    definition: &clap::Command,
    req: &Req<'_>,
) -> Result<(), CommandError> {
    let supplied = |arg: &clap::Arg| {
        arg.get_long()
            .is_some_and(|long| req.invocation().flag(long).is_some())
            || arg
                .get_short()
                .is_some_and(|short| req.invocation().flag(&short.to_string()).is_some())
    };
    for arg in definition.get_arguments().filter(|a| supplied(a)) {
        for other in definition.get_arg_conflicts_with(arg) {
            // Checked in both directions: clap records a conflict on the
            // argument that declares it (`--output`), not on both.
            if supplied(other) {
                let name = |a: &clap::Arg| format!("--{}", a.get_long().unwrap_or_default());
                return Err(CommandError::new(
                    format!(
                        "`{command}` does not take {} together with {}",
                        name(arg),
                        name(other)
                    ),
                    "CONFLICTING_FLAGS",
                    format!("Pass one of {} and {}.", name(arg), name(other)),
                )
                .exit_code(agcli::ExitCode::USAGE));
            }
        }
    }
    Ok(())
}

/// Whether the run is confirmed (`--yes`/`-y`) and whether it is a dry run
/// (`--dry-run`/`-n`), each read as agcli reads its reserved booleans, so
/// `--dry-run=false` is not a dry run.
///
/// `--no-input` is NOT a confirmation here, unlike for `add`: it says "never
/// prompt", and these commands rewrite and delete ledger files, which needs
/// an explicit yes.
fn confirmation(req: &Req<'_>) -> (bool, bool) {
    let yes = req.reserved_bool("yes") || req.reserved_bool("y");
    let dry_run = req.dry_run() || req.reserved_bool("n");
    (yes, dry_run)
}

/// The one FILE positional `split` and `merge` take, if any.
fn restructure_file(command: &str, req: &Req<'_>) -> Result<Option<PathBuf>, CommandError> {
    if req.positionals().len() > 1 {
        return Err(CommandError::new(
            format!("{command} takes at most one file"),
            "INVALID_ARGS",
            format!("Pass the one file to {command}, or none to use default.file from the config."),
        )
        .exit_code(agcli::ExitCode::USAGE));
    }
    Ok(req.arg(0).map(PathBuf::from))
}

/// `split`'s arguments, and whether the run is confirmed.
fn build_split_args(req: &Req<'_>) -> Result<(split::Args, bool), CommandError> {
    use clap::ValueEnum as _;
    let definition = split_definition();
    reject_conflicts("split", &definition, req)?;
    let file = restructure_file("split", req)?;
    let periods: Vec<String> = split::Period::value_variants()
        .iter()
        .filter_map(clap::ValueEnum::to_possible_value)
        .map(|p| p.get_name().to_string())
        .collect();
    let by = match flag(req, "by", None) {
        Some(raw) => split::Period::from_str(raw, false).map_err(|_| {
            let allowed: Vec<&str> = periods.iter().map(String::as_str).collect();
            invalid_enum("by", raw, &allowed)
        })?,
        None => {
            return Err(CommandError::new(
                "split requires --by",
                "MISSING_FLAG",
                format!(
                    "Name the period each file covers: --by {}.",
                    periods.join("|")
                ),
            )
            .exit_code(agcli::ExitCode::USAGE));
        }
    };
    let (yes, dry_run) = confirmation(req);
    Ok((
        split::Args {
            file,
            by,
            dir: path_value(req, "dir", None)?,
            ledger: path_value(req, "ledger", None)?,
            dry_run,
        },
        yes,
    ))
}

/// `merge`'s arguments, and whether the run is confirmed.
fn build_merge_args(req: &Req<'_>) -> Result<(merge::Args, bool), CommandError> {
    let definition = merge_definition();
    reject_conflicts("merge", &definition, req)?;
    let file = restructure_file("merge", req)?;
    let (yes, dry_run) = confirmation(req);
    Ok((
        merge::Args {
            file,
            output: path_value(req, "output", Some("o"))?,
            // Read as agcli reads its switches: `--keep-included=false`
            // does not keep them.
            keep_included: req.reserved_bool("keep-included"),
            ledger: path_value(req, "ledger", None)?,
            dry_run,
        },
        yes,
    ))
}

/// Refuse to rewrite ledger files without an explicit `--yes`, as `add`
/// refuses to append without one. `rledger` asks nothing either, but a
/// person typed that command; an agent is told how to proceed instead.
fn require_confirmation(command: &str, yes: bool, dry_run: bool) -> Result<(), CommandError> {
    if yes || dry_run {
        return Ok(());
    }
    Err(CommandError::new(
        format!(
            "ag-rledger {command} needs explicit confirmation: it {}",
            if command == "merge" {
                "rewrites ledger files and removes the ones it inlines"
            } else {
                "rewrites ledger files"
            }
        ),
        "CONFIRMATION_REQUIRED",
        "Run it with --dry-run first to see the plan and the equivalence check without writing \
             anything, then with --yes to write it. The originals are backed up under \
             .rledger-backup/ next to the file.",
    )
    .exit_code(agcli::ExitCode::USAGE))
}

fn split_command() -> Command {
    Command::new(
        "split",
        "Split a file into one file per year or month, plus a root of includes \
         (rewrites files: needs --dry-run or --yes)",
    )
    .usage(with_globals(&clap_usage("split", &split_definition())))
    .allow_unknown_flags()
    .allow_extra_args()
    .handles_dry_run()
    .default_next_action(NextAction::new(
        "ag-rledger split <file> --by year --dry-run",
        "Preview the split and its equivalence check without writing",
    ))
    .handler(|req, _ctx| {
        let parsed = parse_request("split", req, build_split_args);
        Box::pin(async move {
            let ((mut args, yes), globals) = parsed?;
            require_confirmation("split", yes, args.dry_run)?;
            let config = load_config(&globals.budget)?;
            if args.file.is_none() {
                args.file = default_file(&config, globals.profile.as_deref());
            }
            run_restructure("split", |out, err, outcome| {
                split::run_with_outcome(&args, out, err, outcome)
            })
        })
    })
}

fn merge_command() -> Command {
    Command::new(
        "merge",
        "Merge a file and everything it includes back into one file \
         (rewrites and removes files: needs --dry-run or --yes)",
    )
    .usage(with_globals(&clap_usage("merge", &merge_definition())))
    .allow_unknown_flags()
    .allow_extra_args()
    .handles_dry_run()
    .default_next_action(NextAction::new(
        "ag-rledger merge <file> --dry-run",
        "Preview the merge and its equivalence check without writing",
    ))
    .handler(|req, _ctx| {
        let parsed = parse_request("merge", req, build_merge_args);
        Box::pin(async move {
            let ((mut args, yes), globals) = parsed?;
            require_confirmation("merge", yes, args.dry_run)?;
            let config = load_config(&globals.budget)?;
            if args.file.is_none() {
                args.file = default_file(&config, globals.profile.as_deref());
            }
            run_restructure("merge", |out, err, outcome| {
                merge::run_with_outcome(&args, out, err, outcome)
            })
        })
    })
}

/// Run `split` or `merge` and report it: the plan, the equivalence check's
/// verdict and what was written in `result`, every refusal as a coded error
/// carrying as much of that as the run got to, and the warning a merge can
/// leave behind (files it could not remove) in `warnings` (#2633).
fn run_restructure<F>(command: &str, run: F) -> Result<CommandOutput, CommandError>
where
    F: FnOnce(&mut Vec<u8>, &mut Vec<u8>, &mut Outcome) -> anyhow::Result<ProcessExitCode>,
{
    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    let mut outcome = Outcome::default();
    let (result, notices) =
        rustledger_plugin::notice::capture(|| run(&mut stdout, &mut stderr, &mut outcome));
    let diagnostics = library_diagnostics(&notices, CollectedDiagnostics::default());
    let mut body = outcome_json(command, &outcome);
    body.insert(
        "stdout".to_string(),
        json!(String::from_utf8_lossy(&stdout)),
    );
    let stderr = String::from_utf8_lossy(&stderr).into_owned();
    if !stderr.is_empty() {
        body.insert("stderr".to_string(), json!(stderr));
    }
    if let Some(items) = warnings_json(&diagnostics) {
        body.insert("warnings".to_string(), items);
    }

    let refused = match &result {
        Err(e) => Some(match restructure::refusal_code(e) {
            Some(code) => {
                let message =
                    rustledger_plugin::escape_untrusted_text(&format!("{e:#}")).into_owned();
                let (exit, fix) = refusal_fix(code);
                CommandError::new(message, code, fix).exit_code(exit)
            }
            None => command_failed(e),
        }),
        Ok(_) => match &outcome.check {
            Some(check @ Check::Refused { reason, unstable }) => {
                let code = check
                    .refusal_code()
                    .unwrap_or(restructure::code::EQUIVALENCE_FAILED);
                let why = if *unstable {
                    "the ledger as it is cannot be verified"
                } else {
                    "the result would not load as the same ledger"
                };
                let (exit, fix) = refusal_fix(code);
                Some(
                    CommandError::new(
                        rustledger_plugin::escape_untrusted_text(&format!(
                            "refusing to {command}: {why}: {reason}"
                        ))
                        .into_owned(),
                        code,
                        fix,
                    )
                    .exit_code(exit),
                )
            }
            _ => None,
        },
    };
    if let Some(error) = refused {
        // A refusal has its own exit code; the outcome's would read 0 for a
        // run that never reached the check.
        body.remove("exit_status");
        return Err(error.data(Value::Object(body)));
    }
    let next = if outcome.dry_run {
        NextAction::new(
            format!("ag-rledger {command} <same arguments> --yes"),
            "Write the plan: the same command with --yes in place of --dry-run",
        )
    } else {
        NextAction::new(
            "ag-rledger check <file>",
            "Validate the restructured ledger",
        )
    };
    Ok(CommandOutput::new(Value::Object(body))
        .exit_code(0)
        .next_action(next))
}

/// The exit code and the advice for a refusal code (see
/// [`restructure::code`]).
fn refusal_fix(code: &str) -> (i32, &'static str) {
    use restructure::code as c;
    let usage = agcli::ExitCode::USAGE;
    let error = agcli::ExitCode::ERROR;
    let not_found = agcli::ExitCode::NOT_FOUND;
    match code {
        c::MISSING_FILE => (
            usage,
            "Pass a ledger file path or set default.file in rledger config.",
        ),
        c::FILE_NOT_FOUND => (not_found, "Check the path and retry with an existing file."),
        c::INCLUDE_NOT_FOUND => (
            not_found,
            "Fix or remove the include that names no file, then retry.",
        ),
        c::BAD_INCLUDE_PATTERN => (error, "Fix the include pattern, then retry."),
        c::SYMLINK_ELSEWHERE => (
            error,
            "Run it on the file the link points to, if nothing opens the ledger through the link.",
        ),
        c::ENCRYPTED_FILE | c::NOT_UTF8 => (
            error,
            "Restructure a plain-text UTF-8 ledger; this file is left as it is.",
        ),
        c::PARSE_ERRORS => (
            error,
            "Fix the parse errors (`ag-rledger check <file>` lists them), then retry.",
        ),
        c::NOTHING_TO_SPLIT | c::NOTHING_TO_MERGE => {
            (error, "Nothing to do; the file is unchanged.")
        }
        c::NOT_A_DIRECTORY | c::TARGET_IS_SOURCE | c::UNWRITABLE_INCLUDE => {
            (usage, "Choose another --dir.")
        }
        c::TARGET_EXISTS => (
            error,
            "Move the existing file away, or choose another --dir (split) or --output (merge).",
        ),
        c::NOT_IN_LEDGER => (
            usage,
            "Pass, as --ledger, the root file whose includes reach FILE.",
        ),
        c::LOAD_FAILED => (error, "Fix what stops the ledger loading, then retry."),
        c::EQUIVALENCE_FAILED => (
            error,
            "Nothing was written. The reason names the first difference; change the plan \
             (another --dir, --by, or --output) or the ledger, then retry with --dry-run.",
        ),
        c::LEDGER_UNSTABLE => (
            error,
            "Nothing was written. The ledger loads differently from run to run (usually a \
             plugin emitting entries in a varying order); fix that first.",
        ),
        c::CHANGED_ON_DISK => (
            error,
            "Nothing was written. A file changed while the plan was checked; retry.",
        ),
        c::BACKUP_INCLUDED => (
            error,
            "Nothing was changed. With the backup in place the ledger no longer loaded \
             the same: usually an include pattern matches .rledger-backup/ (narrow it); \
             otherwise the ledger loads differently from run to run (see LEDGER_UNSTABLE).",
        ),
        c::WRITE_ROLLED_BACK => (
            error,
            "The originals were restored (with merge --output nothing original was \
             replaced and the output file was removed); a backup, when one was taken, \
             is in backup_dir. The written files passed the check in memory but \
             reloaded differently from disk, usually a ledger that loads differently \
             from run to run (a plugin) or a file edited meanwhile. Retry with \
             --dry-run; if it recurs, treat it as LEDGER_UNSTABLE.",
        ),
        c::RESTORE_FAILED => (
            error,
            "Restoring failed. If backup_dir is set, copy the originals back from it (its \
             manifest.txt lists each file and the files the run created); with merge \
             --output nothing original was replaced, and only the output file may be left.",
        ),
        _ => (
            error,
            "Inspect the message, adjust the invocation, and retry.",
        ),
    }
}

/// `outcome` as the envelope's `result` (or a refusal's `data`). On a
/// rolled-back write, `written`/`removed` are what the run changed before
/// the rollback, and the error's code says whether those files were
/// restored (#2721).
fn outcome_json(command: &str, outcome: &Outcome) -> serde_json::Map<String, Value> {
    let path = |p: &std::path::Path| json!(p.to_string_lossy());
    let mut body = serde_json::Map::new();
    body.insert("command".to_string(), json!(command));
    body.insert(
        "exit_status".to_string(),
        json!(i32::from(outcome.exit_status())),
    );
    body.insert("dry_run".to_string(), json!(outcome.dry_run));
    let plan = outcome.plan.as_ref().map(|plan| {
        let steps: Vec<Value> = plan
            .steps
            .iter()
            .map(|step| match step {
                Step::Create {
                    path: p,
                    dated_directives,
                } => {
                    let mut o = json!({"action": "create", "path": path(p)});
                    if let Some(n) = dated_directives {
                        o["dated_directives"] = json!(n);
                    }
                    o
                }
                Step::Rewrite { path: p, split } => {
                    let mut o = json!({"action": "rewrite", "path": path(p)});
                    if let Some((kept, added)) = split {
                        o["kept_lines"] = json!(kept);
                        o["added_includes"] = json!(added);
                    }
                    o
                }
                Step::Inline {
                    path: p,
                    remove,
                    shared,
                } => json!({
                    "action": "inline",
                    "path": path(p),
                    "remove": remove,
                    "kept_as_shared": shared,
                }),
            })
            .collect();
        let mut o = json!({
            "operation": plan.operation,
            "file": path(&plan.file),
            "steps": steps,
        });
        if let Some(by) = plan.by {
            o["by"] = json!(by);
        }
        o
    });
    body.insert("plan".to_string(), plan.unwrap_or(Value::Null));
    let check = outcome.check.as_ref().map(|check| match check {
        Check::Passed { directives, errors } => json!({
            "passed": true,
            "directives": directives,
            "errors_and_warnings": errors,
        }),
        Check::Refused { reason, .. } => json!({
            "passed": false,
            "code": check.refusal_code(),
            "reason": reason,
        }),
    });
    body.insert("equivalence".to_string(), check.unwrap_or(Value::Null));
    let written = outcome.written.as_ref();
    let paths = |list: Option<&Vec<PathBuf>>| -> Value {
        json!(list.map_or_else(Vec::new, |l| l.iter().map(|p| path(p)).collect::<Vec<_>>()))
    };
    body.insert("written".to_string(), paths(written.map(|w| &w.written)));
    body.insert("removed".to_string(), paths(written.map(|w| &w.removed)));
    body.insert(
        "not_removed".to_string(),
        json!(written.map_or_else(Vec::new, |w| w.not_removed.clone())),
    );
    body.insert(
        "backup_dir".to_string(),
        outcome.backup_dir.as_deref().map_or(Value::Null, path),
    );
    body
}

fn build_check_args(req: &Req<'_>) -> Result<rustledger::cmd::check::Args, CommandError> {
    let format = if bool_flag(req, "json", None) {
        rustledger::cmd::check::OutputFormat::Json
    } else {
        match flag(req, "format", Some("f")).unwrap_or("text") {
            "text" => rustledger::cmd::check::OutputFormat::Text,
            "json" => rustledger::cmd::check::OutputFormat::Json,
            other => return Err(invalid_enum("format", other, &["text", "json"])),
        }
    };

    let lints = match flag(req, "lint", None) {
        Some("transfers") => vec![rustledger::cmd::check::LintName::Transfers],
        Some(other) => return Err(invalid_enum("lint", other, &["transfers"])),
        None => Vec::new(),
    };

    Ok(rustledger::cmd::check::Args {
        file: path_flag(req, "file", None).or_else(|| req.arg(0).map(PathBuf::from)),
        generate_completions: None,
        verbose: bool_flag(req, "verbose", Some("v")),
        quiet: bool_flag(req, "quiet", Some("q")),
        no_cache: bool_flag(req, "no-cache", Some("C")),
        cache_filename: path_flag(req, "cache-filename", None),
        auto: bool_flag(req, "auto", Some("a")),
        plugins: flag_values(req, "plugin", None)
            .into_iter()
            .map(PathBuf::from)
            .collect(),
        native_plugins: flag_values(req, "native-plugin", None),
        format,
        lints,
        lint_min_confidence: parse_flag(req, "lint-min-confidence", None, 0.8)?,
        show_summary: bool_flag(req, "show-summary", None),
        include_rules: flag_values(req, "include-rules", None),
        exclude_rules: flag_values(req, "exclude-rules", None),
    })
}

fn build_query_args(req: &Req<'_>) -> Result<rustledger::cmd::query::Args, CommandError> {
    let explicit_file = path_flag(req, "file", None);
    let mut positionals = req.positionals().to_vec();
    // Only consume the leading positional as the file when no `--file` was
    // given AND it looks like a ledger path (M2). `ag-rledger query "SELECT
    // ..."` is meant to query the config default file, so a bare SQL string
    // must NOT be swallowed as the file path — leave `file = None` so the
    // handler falls back to `default.file`, and treat every positional as
    // query text.
    let file = explicit_file.or_else(|| {
        if positionals
            .first()
            .is_some_and(|first| looks_like_ledger_path(first))
        {
            Some(PathBuf::from(positionals.remove(0)))
        } else {
            None
        }
    });

    let format = match flag(req, "format", Some("f")) {
        Some(raw) => Some(
            rustledger::cmd::query::OutputFormat::from_str_config(raw).ok_or_else(|| {
                invalid_enum("format", raw, &["text", "csv", "json", "beancount"])
            })?,
        ),
        None => None,
    };

    Ok(rustledger::cmd::query::Args {
        file,
        generate_completions: None,
        query: positionals,
        query_file: path_flag(req, "query-file", Some("F")),
        output: path_flag(req, "output", Some("o")),
        format,
        numberify: bool_flag(req, "numberify", Some("m")),
        no_errors: bool_flag(req, "no-errors", Some("q")),
        verbose: bool_flag(req, "verbose", Some("v")),
        no_cache: req.no_cache() || bool_flag(req, "no-cache", None),
    })
}

fn build_format_args(req: &Req<'_>) -> Result<rustledger::cmd::format::Args, CommandError> {
    Ok(rustledger::cmd::format::Args {
        files: req.positionals().iter().map(PathBuf::from).collect(),
        generate_completions: None,
        output: path_flag(req, "output", Some("o")),
        in_place: bool_flag(req, "in-place", Some("i")),
        check: bool_flag(req, "check", None),
        diff: bool_flag(req, "diff", None),
        ledger: path_flag(req, "ledger", None),
        no_ledger: bool_flag(req, "no-ledger", None),
        verbose: bool_flag(req, "verbose", Some("v")),
    })
}

/// `report`'s arguments, before the config fills in what they leave out.
struct ReportArgs {
    /// The ledger, when named (`--file` or a leading positional); `None`
    /// falls back to the config's default file.
    file: Option<PathBuf>,
    report: rustledger::cmd::report_cmd::Report,
    verbose: bool,
    no_cache: bool,
    /// `--format`, when given; `None` falls back to the config.
    format: Option<rustledger::cmd::report_cmd::OutputFormat>,
}

fn report_format(raw: &str) -> Result<rustledger::cmd::report_cmd::OutputFormat, CommandError> {
    use rustledger::cmd::report_cmd::OutputFormat;
    match raw {
        "text" => Ok(OutputFormat::Text),
        "csv" => Ok(OutputFormat::Csv),
        "json" => Ok(OutputFormat::Json),
        other => Err(invalid_enum("format", other, &["text", "csv", "json"])),
    }
}

fn build_report_args(req: &Req<'_>) -> Result<ReportArgs, CommandError> {
    let explicit_file = path_flag(req, "file", None);
    let mut positionals = req.positionals().to_vec();
    let first_is_report = positionals
        .first()
        .is_some_and(|s| parse_report_name(s).is_some());
    let file = explicit_file.or_else(|| {
        if first_is_report || positionals.is_empty() {
            None
        } else {
            Some(PathBuf::from(positionals.remove(0)))
        }
    });

    let report_name = positionals.first().ok_or_else(|| {
        CommandError::new(
            "report subcommand is required",
            "MISSING_REPORT",
            format!("Use one of: {}.", report_names().join(", ")),
        )
        .exit_code(agcli::ExitCode::USAGE)
    })?;
    let report = build_report(report_name, req)?;
    let format = flag(req, "format", Some("f"))
        .map(report_format)
        .transpose()?;
    Ok(ReportArgs {
        file,
        report,
        verbose: bool_flag(req, "verbose", Some("v")),
        no_cache: req.no_cache(),
        format,
    })
}

fn build_report(
    report_name: &str,
    req: &Req<'_>,
) -> Result<rustledger::cmd::report_cmd::Report, CommandError> {
    use rustledger::cmd::report_cmd::Report;
    // Before building: a flag this report cannot read must not be silently
    // dropped, which is what returned an unfiltered figure as a success (#2280).
    reject_inapplicable_flags(report_name, req)?;
    match parse_report_name(report_name).as_deref() {
        Some("balances") => Ok(Report::Balances {
            account: string_flag(req, "account", Some("a")),
            window: date_window(req),
        }),
        Some("balsheet") => Ok(Report::Balsheet {
            window: date_window(req),
        }),
        Some("income") => Ok(Report::Income {
            window: date_window(req),
        }),
        Some("journal") => Ok(Report::Journal {
            account: string_flag(req, "account", Some("a")),
            limit: optional_parse_flag(req, "limit", Some("l"))?,
            running: bool_flag(req, "running", None),
            window: date_window(req),
        }),
        Some("register") => Ok(Report::Register {
            account: string_flag(req, "account", Some("a")),
            limit: optional_parse_flag(req, "limit", Some("l"))?,
            window: date_window(req),
        }),
        Some("holdings") => Ok(Report::Holdings {
            account: string_flag(req, "account", Some("a")),
            window: date_window(req),
        }),
        Some("networth") => Ok(Report::Networth {
            period: string_flag(req, "period", Some("p")).unwrap_or_else(|| "monthly".to_string()),
            currency: string_flag(req, "currency", Some("c")),
            account: string_flag(req, "account", Some("a")),
            no_zero: bool_flag(req, "no-zero", None),
        }),
        Some("accounts") => Ok(Report::Accounts),
        Some("commodities") => Ok(Report::Commodities),
        Some("stats") => Ok(Report::Stats),
        Some("prices") => Ok(Report::Prices {
            commodity: string_flag(req, "commodity", Some("c")),
        }),
        Some("budget") => Ok(Report::Budget {
            account: string_flag(req, "account", Some("a")),
            window: date_window(req),
            children: bool_flag(req, "children", None),
        }),
        Some("returns") => {
            let investments = flag_values(req, "investments", Some("i"));
            // Required by `rledger` too: the investment accounts ARE the
            // portfolio, and there is no default that would mean anything.
            if investments.is_empty() {
                return Err(CommandError::new(
                    "report returns requires --investments",
                    "MISSING_FLAG",
                    "Name the investment account prefix(es): --investments Assets:Investments \
                     (repeatable).",
                )
                .exit_code(agcli::ExitCode::USAGE));
            }
            Ok(Report::Returns {
                investments,
                income: flag_values(req, "income", Some("n")),
                currency: string_flag(req, "currency", Some("c")),
                end: string_flag(req, "end", Some("e")),
                by_group: bool_flag(req, "by-group", None),
            })
        }
        Some("capgains") => Ok(Report::Capgains {
            account: string_flag(req, "account", Some("a")),
            year: optional_parse_flag(req, "year", Some("y"))?,
            end: string_flag(req, "end", Some("e")),
            long_term_days: optional_parse_flag(req, "long-term-days", None)?,
            irr: bool_flag(req, "irr", None),
        }),
        // A report `rledger` has and this match does not: refused by name,
        // never ignored. The drift guard
        // (`ag_rledger_reads_every_rledger_flag_or_refuses_it`) fails until
        // it is wired here.
        Some(other) => Err(CommandError::new(
            format!("report `{other}` is not offered by ag-rledger"),
            "UNSUPPORTED",
            "Run it with `rledger report`.",
        )
        .exit_code(agcli::ExitCode::USAGE)),
        None => Err(invalid_enum("report", report_name, &report_names())),
    }
}

/// The date-window flags `rledger report` shares across its windowed reports
/// (`cmd::report_cmd::DateWindow`). Conflicting combinations are rejected
/// when the window is resolved, by the same code `rledger` runs.
fn date_window(req: &Req<'_>) -> rustledger::cmd::report_cmd::DateWindow {
    rustledger::cmd::report_cmd::DateWindow {
        from: string_flag(req, "from", None),
        to: string_flag(req, "to", None),
        year: string_flag(req, "year", None),
        time: string_flag(req, "time", None),
    }
}

/// Every report's name, from `rledger`'s definition (see [`report_flags`]).
fn report_names() -> Vec<&'static str> {
    report_flags().iter().map(|(r, _)| r.as_str()).collect()
}

/// The report `name` refers to: a report's name or one of `rledger`'s
/// aliases for it (`bal`, `is`), both read from `rledger`'s definition, or
/// one of the longer spellings `ag-rledger` has always accepted.
fn parse_report_name(name: &str) -> Option<String> {
    static ALIASES: OnceLock<Vec<(String, Vec<String>)>> = OnceLock::new();
    let name = match name {
        "balance-sheet" => "balsheet",
        "income-statement" => "income",
        "net-worth" => "networth",
        other => other,
    };
    let aliases = ALIASES.get_or_init(|| {
        use clap::Args as _;
        rustledger::cmd::report_cmd::Args::augment_args(clap::Command::new("report"))
            .get_subcommands()
            .map(|sub| {
                (
                    sub.get_name().to_string(),
                    sub.get_all_aliases().map(str::to_string).collect(),
                )
            })
            .collect()
    });
    aliases
        .iter()
        .find(|(report, spellings)| report == name || spellings.iter().any(|s| s == name))
        .map(|(report, _)| report.clone())
}

fn build_doctor_command(req: &Req<'_>) -> Result<rustledger::cmd::doctor::Command, CommandError> {
    use rustledger::cmd::doctor::{Command as Doctor, Conversion};
    let sub = req.arg(0).ok_or_else(|| {
        CommandError::new(
            "doctor subcommand is required",
            "MISSING_SUBCOMMAND",
            "Use lex, parse, context, linked, missing-open, list-options, print-options, stats, display-context, roundtrip, directories, region, or generate-synthetic.",
        )
        .exit_code(agcli::ExitCode::USAGE)
    })?;
    let arg = |idx| req.arg(idx).map(PathBuf::from);
    match sub {
        "lex" | "dump-lexer" => Ok(Doctor::Lex {
            file: required_path_arg(req, 1, "file")?,
        }),
        "parse" => Ok(Doctor::Parse {
            file: required_path_arg(req, 1, "file")?,
            verbose: bool_flag(req, "verbose", Some("v")),
        }),
        "context" => Ok(Doctor::Context {
            file: required_path_arg(req, 1, "file")?,
            line: parse_positional(req, 2, "line")?,
        }),
        "linked" => Ok(Doctor::Linked {
            file: required_path_arg(req, 1, "file")?,
            location: req.require_arg(2, "location")?.to_string(),
        }),
        "missing-open" => Ok(Doctor::MissingOpen {
            file: required_path_arg(req, 1, "file")?,
        }),
        "list-options" => Ok(Doctor::ListOptions),
        "print-options" => Ok(Doctor::PrintOptions {
            file: required_path_arg(req, 1, "file")?,
        }),
        "stats" => Ok(Doctor::Stats {
            file: required_path_arg(req, 1, "file")?,
        }),
        "display-context" => Ok(Doctor::DisplayContext {
            file: required_path_arg(req, 1, "file")?,
        }),
        "roundtrip" => Ok(Doctor::Roundtrip {
            file: required_path_arg(req, 1, "file")?,
        }),
        "directories" => Ok(Doctor::Directories {
            file: required_path_arg(req, 1, "file")?,
            dirs: req.positionals()[2..].iter().map(PathBuf::from).collect(),
        }),
        "region" => {
            let conversion = match flag(req, "conversion", None) {
                Some("value") => Some(Conversion::Value),
                Some("cost") => Some(Conversion::Cost),
                Some(other) => return Err(invalid_enum("conversion", other, &["value", "cost"])),
                None => None,
            };
            Ok(Doctor::Region {
                file: required_path_arg(req, 1, "file")?,
                start_line: parse_positional(req, 2, "start-line")?,
                end_line: parse_positional(req, 3, "end-line")?,
                conversion,
            })
        }
        "generate-synthetic" => Ok(Doctor::GenerateSynthetic {
            output: path_flag(req, "output", Some("o"))
                .or_else(|| arg(1))
                .unwrap_or_else(|| PathBuf::from("tests/compatibility/synthetic")),
            count: parse_flag(req, "count", Some("c"), 50)?,
            seed: optional_parse_flag(req, "seed", Some("s"))?,
            skip_validation: bool_flag(req, "skip-validation", None),
            manifest: bool_flag(req, "manifest", None),
            edge_cases_only: bool_flag(req, "edge-cases-only", None),
        }),
        other => Err(invalid_enum(
            "doctor subcommand",
            other,
            &[
                "lex",
                "parse",
                "context",
                "linked",
                "missing-open",
                "list-options",
                "print-options",
                "stats",
                "display-context",
                "roundtrip",
                "directories",
                "region",
                "generate-synthetic",
            ],
        )),
    }
}

fn build_extract_args(req: &Req<'_>) -> Result<rustledger::cmd::extract_cmd::Args, CommandError> {
    // Left `None` when unset, like `account` below: an unset flag must not
    // overwrite an `importers.toml` entry's value with a default (#2304).
    let delimiter = flag(req, "delimiter", None).and_then(|d| d.chars().next());
    Ok(rustledger::cmd::extract_cmd::Args {
        generate_completions: None,
        file: path_flag(req, "file", None).or_else(|| req.arg(0).map(PathBuf::from)),
        importer: string_flag(req, "importer", Some("i")),
        config: path_flag(req, "config", None).or_else(|| path_flag(req, "importers-config", None)),
        list_importers: bool_flag(req, "list-importers", None),
        // Left as `None` when unset: extract distinguishes "not named" from
        // "named as the default" to refuse an unconfigured OFX import (#2256).
        account: string_flag(req, "account", Some("a")),
        currency: string_flag(req, "currency", Some("c")),
        date_column: string_flag(req, "date-column", None),
        date_format: string_flag(req, "date-format", None),
        narration_column: string_flag(req, "narration-column", None),
        payee_column: string_flag(req, "payee-column", None),
        amount_column: string_flag(req, "amount-column", None),
        currency_column: string_flag(req, "currency-column", None),
        amount_locale: string_flag(req, "amount-locale", None),
        amount_format: string_flag(req, "amount-format", None),
        debit_column: string_flag(req, "debit-column", None),
        credit_column: string_flag(req, "credit-column", None),
        delimiter,
        skip_rows: optional_parse_flag(req, "skip-rows", None)?,
        invert_sign: bool_flag(req, "invert-sign", None),
        include_zero_amounts: bool_flag(req, "include-zero-amounts", None),
        auto: bool_flag(req, "auto", None),
        no_header: bool_flag(req, "no-header", None),
        use_merchant_dict: bool_flag(req, "use-merchant-dict", None),
        output: path_flag(req, "output", Some("o")),
        force: bool_flag(req, "force", None),
        existing: path_flag(req, "existing", None),
        ledger: path_flag(req, "ledger", None),
        suggest_categories: bool_flag(req, "suggest-categories", None),
        balance: string_flag(req, "balance", None),
        balance_date: string_flag(req, "balance-date", None),
        wasm_importer: flag_values(req, "wasm-importer", None)
            .into_iter()
            .map(PathBuf::from)
            .collect(),
        wasm_importer_dir: flag_values(req, "wasm-importer-dir", None)
            .into_iter()
            .map(PathBuf::from)
            .collect(),
    })
}

fn build_price_args(req: &Req<'_>) -> Result<rustledger::cmd::price_cmd::PriceArgs, CommandError> {
    Ok(rustledger::cmd::price_cmd::PriceArgs {
        file: path_flag(req, "file", Some("f")),
        symbols: req.positionals().to_vec(),
        // `None` when the flag is absent, like `rledger`'s no-default `--currency`:
        // the request falls back to USD but the quote is undeclared (#2731).
        currency: string_flag(req, "currency", Some("c")),
        date: string_flag(req, "date", Some("d")),
        beancount: bool_flag(req, "beancount", Some("b")),
        source_meta: bool_flag(req, "source-meta", None),
        verbose: bool_flag(req, "verbose", Some("v")),
        mapping: flag_values(req, "mapping", Some("m")),
        source: string_flag(req, "source", Some("s")),
        source_cmd: string_flag(req, "source-cmd", None),
        list_sources: bool_flag(req, "list-sources", None),
        no_cache: req.no_cache() || bool_flag(req, "no-cache", None),
        clear_cache: bool_flag(req, "clear-cache", None),
        inactive: bool_flag(req, "inactive", None),
        undeclared: bool_flag(req, "undeclared", None),
        all_commodities: bool_flag(req, "all-commodities", None),
        dry_run: req.dry_run() || bool_flag(req, "dry-run", Some("n")),
        clobber: bool_flag(req, "clobber", Some("C")),
    })
}

fn build_config_args(req: &Req<'_>) -> Result<rustledger::cmd::config_cmd::Args, CommandError> {
    use rustledger::cmd::config_cmd::{Args, ConfigCommand};
    let command = match req.arg(0).unwrap_or("show") {
        "show" => ConfigCommand::Show {
            raw: bool_flag(req, "raw", None),
            format: string_flag(req, "format", Some("f")).unwrap_or_else(|| "toml".to_string()),
        },
        "path" => ConfigCommand::Path,
        "edit" => ConfigCommand::Edit {
            project: bool_flag(req, "project", None),
            system: bool_flag(req, "system", None),
        },
        "init" => ConfigCommand::Init {
            project: bool_flag(req, "project", None),
            force: bool_flag(req, "force", Some("f")),
        },
        "aliases" => ConfigCommand::Aliases,
        other => {
            return Err(invalid_enum(
                "config subcommand",
                other,
                &["show", "path", "edit", "init", "aliases"],
            ));
        }
    };
    Ok(Args { command })
}

fn build_add_args(req: &Req<'_>) -> Result<rustledger::cmd::add_cmd::Args, CommandError> {
    let mut positionals = req.positionals().to_vec();
    // Same M2 heuristic as query: only consume the leading positional as the
    // file when no `--file` was given AND it looks like a ledger path.
    // Otherwise leave `file = None` (the handler falls back to `default.file`)
    // and treat every positional as a `--quick` argument. This keeps
    // `ag-rledger add --quick <payee> <narration> ...` (no explicit file)
    // from swallowing the payee as the ledger path.
    let file = path_flag(req, "file", None).or_else(|| {
        if positionals
            .first()
            .is_some_and(|first| looks_like_ledger_path(first))
        {
            Some(PathBuf::from(positionals.remove(0)))
        } else {
            None
        }
    });
    let mut quick = string_flag(req, "quick", Some("q")).map(|first| {
        let mut items = vec![first];
        items.extend(positionals);
        items
    });
    // `ag-rledger add` is quick-mode only: an agent path has no interactive
    // prompt, so `--quick` is REQUIRED. Without it the downstream
    // `run_quick_mode_with_writer` does `.expect("quick mode args")` and
    // panics on agent-controlled input; return a clean USAGE error instead.
    match quick.as_ref().map(Vec::len) {
        None => {
            return Err(CommandError::new(
                "add requires --quick (agent mode has no interactive prompt)",
                "MISSING_QUICK_ARGS",
                "Use: ag-rledger add <file> --quick <payee> <narration> <account> <amount> <account>",
            )
            .exit_code(agcli::ExitCode::USAGE));
        }
        Some(len) if len < 4 => {
            return Err(CommandError::new(
                "quick mode requires at least payee, narration, account, amount",
                "INVALID_QUICK_ARGS",
                "Use: ag-rledger add <file> --quick <payee> <narration> <account> <amount> <account>",
            )
            .exit_code(agcli::ExitCode::USAGE));
        }
        _ => {}
    }
    Ok(rustledger::cmd::add_cmd::Args {
        file,
        date: string_flag(req, "date", Some("d")),
        dry_run: req.dry_run() || bool_flag(req, "dry-run", Some("n")),
        yes: req.assume_yes() || bool_flag(req, "yes", Some("y")),
        quick: quick.take(),
        no_completion: bool_flag(req, "no-completion", None),
    })
}

/// The lints `ag-rledger lint` runs: every `rledger lint` subcommand.
const LINTS: &[&str] = &["transfers", "closed-nonempty", "control-chars"];

fn build_lint_args(req: &Req<'_>) -> Result<rustledger::cmd::lint::Args, CommandError> {
    use rustledger::cmd::lint::{Args, LintKind, closed_nonempty, control_chars, transfers};
    let subcommand = req.arg(0).ok_or_else(|| {
        CommandError::new(
            "lint name is required",
            "MISSING_LINT",
            format!("Use one of: {}.", LINTS.join(", ")),
        )
        .exit_code(agcli::ExitCode::USAGE)
    })?;
    let format = flag(req, "format", Some("f")).unwrap_or("text");
    let files: Vec<PathBuf> = req.positionals()[1..].iter().map(PathBuf::from).collect();
    let lint = match subcommand {
        "transfers" => LintKind::Transfers(transfers::Args {
            files,
            min_confidence: parse_flag(req, "min-confidence", None, 0.8)?,
            date_window: parse_flag(req, "date-window", None, 3)?,
            amount_tolerance: string_flag(req, "amount-tolerance", None)
                .unwrap_or_else(|| "0.01".to_string()),
            apply: bool_flag(req, "apply", None),
            format: match format {
                "text" => transfers::OutputFormat::Text,
                "json" => transfers::OutputFormat::Json,
                other => return Err(invalid_enum("format", other, &["text", "json"])),
            },
        }),
        "closed-nonempty" => LintKind::ClosedNonempty(closed_nonempty::Args {
            files,
            format: match format {
                "text" => closed_nonempty::OutputFormat::Text,
                "json" => closed_nonempty::OutputFormat::Json,
                other => return Err(invalid_enum("format", other, &["text", "json"])),
            },
        }),
        "control-chars" => LintKind::ControlChars(control_chars::Args {
            files,
            format: match format {
                "text" => closed_nonempty::OutputFormat::Text,
                "json" => closed_nonempty::OutputFormat::Json,
                other => return Err(invalid_enum("format", other, &["text", "json"])),
            },
        }),
        other => return Err(invalid_enum("lint", other, LINTS)),
    };
    let files = match &lint {
        LintKind::Transfers(args) => &args.files,
        LintKind::ClosedNonempty(args) => &args.files,
        LintKind::ControlChars(args) => &args.files,
    };
    if files.is_empty() {
        return Err(missing_file_error(&format!("lint {subcommand}")));
    }
    Ok(Args { lint })
}

/// Run a command whose own output is all on `out` (`doctor`, `config`, `add`,
/// `lint`). What the libraries it calls have to say still reaches the
/// envelope: see [`run_buffered_with_warnings`].
fn run_buffered<F>(command: &str, run: F) -> Result<CommandOutput, CommandError>
where
    F: FnOnce(&mut Vec<u8>) -> anyhow::Result<i32>,
{
    run_buffered_with_warnings(command, |out, _, _| run(out))
}

/// [`run_buffered`], for a command that also writes what `rledger` sends to
/// stderr: progress, `--diff` hunks, fetch errors, warnings. It goes to the
/// envelope's `result.stderr`, not the process's stderr, which the envelope
/// does not carry (#2546).
fn run_buffered_with_stderr<F>(command: &str, run: F) -> Result<CommandOutput, CommandError>
where
    F: FnOnce(&mut Vec<u8>, &mut Vec<u8>) -> anyhow::Result<i32>,
{
    run_buffered_with_warnings(command, |out, _, err| run(out, err))
}

/// [`run_buffered_with_stderr`], for commands that also produce DIAGNOSTICS.
///
/// The envelope carries them in `warnings`, one object per diagnostic.
/// Reports and queries write theirs to a sink rather than the process's
/// stderr precisely so this can happen: an agent asking for a text or CSV
/// budget report used to get a tidy `0.0%`-used row for a budget on a
/// misspelled account, with the warning that says so written to a stream
/// this envelope discards, and `query` reported a failing balance the same
/// way (#2546).
///
/// The libraries a command calls have messages of their own — the Python
/// plugin runtime's download and compile notices, what a Python plugin
/// prints, a WASM importer whose `identify` failed, the `RLEDGER_CONFIG`
/// deprecation warning. They are emitted through
/// [`rustledger_plugin::notice`], captured here rather than written to the
/// process's stderr, and carried in `warnings` with their codes, ahead of the
/// command's own (#2566).
fn run_buffered_with_warnings<F>(command: &str, run: F) -> Result<CommandOutput, CommandError>
where
    F: FnOnce(&mut Vec<u8>, &mut CollectedDiagnostics, &mut Vec<u8>) -> anyhow::Result<i32>,
{
    let mut stdout = Vec::new();
    let mut own = CollectedDiagnostics::default();
    let mut stderr = Vec::new();
    let (outcome, notices) =
        rustledger_plugin::notice::capture(|| run(&mut stdout, &mut own, &mut stderr));
    let diagnostics = library_diagnostics(&notices, own);
    let stderr = String::from_utf8_lossy(&stderr).into_owned();
    let warnings = warnings_json(&diagnostics);
    let exit_code = match outcome {
        Ok(code) => code,
        Err(e) => {
            // What the command wrote before it failed is often the reason
            // (`format` lists each parse error, then fails), so it rides on
            // the error rather than being dropped with the result.
            let mut error = command_failed(&e);
            let mut data = serde_json::Map::new();
            if !stderr.is_empty() {
                data.insert("stderr".to_string(), json!(stderr));
            }
            if let Some(items) = warnings {
                data.insert("warnings".to_string(), items);
            }
            if !data.is_empty() {
                error = error.data(Value::Object(data));
            }
            return Err(error);
        }
    };
    let stdout = String::from_utf8_lossy(&stdout).into_owned();
    let mut result = command_result(command, &stdout, exit_code);
    if let Value::Object(map) = &mut result {
        if !stderr.is_empty() {
            map.insert("stderr".to_string(), json!(stderr));
        }
        if let Some(items) = warnings {
            map.insert("warnings".to_string(), items);
        }
    }
    Ok(CommandOutput::new(result)
        .exit_code(exit_code)
        .next_action(NextAction::new(
            format!("ag-rledger {command} --help"),
            "Inspect command usage",
        )))
}

/// The library notices (those emitted while the config loaded, then those
/// the command's run emitted) followed by the command's own diagnostics.
///
/// A run notice that repeats a config-loading notice verbatim is dropped:
/// `config` loads the config file again, and its deprecation warning is one
/// warning, not two. Other repeats are kept — a plugin that prints the same
/// line on two runs printed it twice.
fn library_diagnostics(
    notices: &[rustledger_plugin::notice::Notice],
    own: CollectedDiagnostics,
) -> CollectedDiagnostics {
    let at_load = config_notices();
    let mut all: Vec<Diagnostic> = at_load
        .iter()
        .chain(notices.iter().filter(|n| !at_load.contains(n)))
        .map(|n| Diagnostic {
            code: Some(n.code.to_string()),
            ..Diagnostic::message(n.message.clone())
        })
        .collect();
    all.extend(own.0);
    CollectedDiagnostics(all)
}

/// The diagnostics as the envelope's `warnings` array, or `None` when there
/// are none.
///
/// One OBJECT per diagnostic, carrying the fields the command already knew.
/// Reports used to hand over formatted lines, so this had to rebuild records
/// by splitting on newlines — which a message carrying its own newline broke
/// in half, and which discarded the date and the account outright.
fn warnings_json(diagnostics: &CollectedDiagnostics) -> Option<Value> {
    if diagnostics.0.is_empty() {
        return None;
    }
    let items: Vec<Value> = diagnostics
        .0
        .iter()
        .map(|d| {
            let mut o = serde_json::Map::new();
            if let Some(code) = &d.code {
                o.insert("code".to_string(), json!(code));
            }
            if let Some(date) = d.date {
                o.insert("date".to_string(), json!(date.to_string()));
            }
            if let Some(account) = &d.account {
                o.insert("account".to_string(), json!(account));
            }
            o.insert("message".to_string(), json!(d.message));
            Value::Object(o)
        })
        .collect();
    Some(json!(items))
}

fn command_result(command: &str, stdout: &str, exit_code: i32) -> Value {
    let trimmed = stdout.trim();
    let parsed = if trimmed.starts_with('{') || trimmed.starts_with('[') {
        serde_json::from_str::<Value>(trimmed).ok()
    } else {
        None
    };
    let mut result = serde_json::Map::new();
    result.insert("command".to_string(), json!(command));
    result.insert("exit_status".to_string(), json!(exit_code));
    result.insert("stdout".to_string(), json!(stdout));
    if let Some(value) = parsed {
        result.insert("data".to_string(), value);
    }
    Value::Object(result)
}

fn command_failed(error: &anyhow::Error) -> CommandError {
    // The chain can quote a WASM module's own text; escaped as in
    // rledger's `render_error`.
    let message = rustledger_plugin::escape_untrusted_text(&format!("{error:#}")).into_owned();
    let (code, exit_code, fix) = if message.contains("FILE is required") {
        (
            "MISSING_FILE",
            agcli::ExitCode::USAGE,
            "Pass a ledger file path or set default.file in rledger config.",
        )
    } else if message.contains("file not found") || message.contains("No such file") {
        (
            "FILE_NOT_FOUND",
            agcli::ExitCode::NOT_FOUND,
            "Check the path and retry with an existing file.",
        )
    } else {
        (
            "COMMAND_FAILED",
            agcli::ExitCode::ERROR,
            "Inspect the message, adjust the invocation, and retry.",
        )
    };
    CommandError::new(message, code, fix).exit_code(exit_code)
}

fn missing_file_error(command: &str) -> CommandError {
    CommandError::new(
        format!("{command} requires a ledger file"),
        "MISSING_FILE",
        "Pass a file path or set default.file in rledger config.",
    )
    .exit_code(agcli::ExitCode::USAGE)
}

fn invalid_enum(name: &str, value: &str, allowed: &[&str]) -> CommandError {
    CommandError::new(
        format!("invalid {name}: {value}"),
        "INVALID_VALUE",
        format!("Use one of: {}.", allowed.join(", ")),
    )
    .exit_code(agcli::ExitCode::USAGE)
}

/// Heuristic: does this leading positional look like a ledger file path
/// rather than query/transaction text? Used by `query` and `add` (M2) so that
/// `ag-rledger query "SELECT ..."` (no `--file`) targets the config default
/// file instead of routing the SQL string into `file`.
///
/// A positional is treated as a ledger path when it either exists on disk or
/// ends in a beancount extension (`.beancount` / `.bean`). Anything else
/// (a BQL string, a payee, a narration) leaves `file = None` so the downstream
/// command uses the configured default.
///
/// Residual limitation: a *non-existent* ledger path with a non-beancount
/// extension (e.g. `ledger.txt` that hasn't been created yet) is not
/// recognized and would be treated as query/transaction text. Callers that
/// need such a path should pass it explicitly via `--file`.
fn looks_like_ledger_path(candidate: &str) -> bool {
    let path = std::path::Path::new(candidate);
    if path.exists() {
        return true;
    }
    path.extension().is_some_and(|ext| {
        ext.eq_ignore_ascii_case("beancount") || ext.eq_ignore_ascii_case("bean")
    })
}

/// A command's arguments, with a record of every flag the command read.
///
/// The commands opt out of agcli's unknown-flag rejection
/// (`allow_unknown_flags`), because they forward flags to the `cmd::*`
/// argument structs rather than re-declaring each in a usage string. That
/// left nothing to notice a flag no handler reads: `--plugin-max-time-secs`
/// and `--plugin-max-memory-mb` ran with the default budget and an `ok`
/// envelope (#2522, #2552), as does every other `rledger` flag the agent
/// surface never wired and every typo.
///
/// So the rejection is done here instead, from what the handler actually
/// read rather than from a list kept beside it: every flag lookup goes
/// through [`Req::flag`], which records the name, and [`Req::reject_unread`]
/// refuses any supplied flag that was never looked up. A flag cannot be
/// accepted without being read, and wiring a new one is the whole job of
/// accepting it.
struct Req<'a> {
    invocation: &'a agcli::Invocation,
    positionals: &'a [String],
    read: RefCell<BTreeSet<String>>,
}

impl<'a> Req<'a> {
    const fn new(invocation: &'a agcli::Invocation, positionals: &'a [String]) -> Self {
        Self {
            invocation,
            positionals,
            read: RefCell::new(BTreeSet::new()),
        }
    }

    const fn invocation(&self) -> &'a agcli::Invocation {
        self.invocation
    }

    const fn positionals(&self) -> &'a [String] {
        self.positionals
    }

    fn arg(&self, index: usize) -> Option<&'a str> {
        self.positionals.get(index).map(String::as_str)
    }

    /// Look up a flag, and record that the command reads it.
    fn flag(&self, key: &str) -> Option<&'a str> {
        self.read.borrow_mut().insert(key.to_string());
        self.invocation.flag(key)
    }

    /// One of agcli's reserved boolean flags, read as agcli reads it.
    fn reserved_bool(&self, key: &str) -> bool {
        self.flag(key).is_some_and(|v| {
            !matches!(
                v.trim().to_ascii_lowercase().as_str(),
                "false" | "0" | "no" | "off"
            )
        })
    }

    fn no_cache(&self) -> bool {
        self.reserved_bool("no-cache")
    }

    fn dry_run(&self) -> bool {
        self.reserved_bool("dry-run")
    }

    fn assume_yes(&self) -> bool {
        self.reserved_bool("yes") || self.reserved_bool("no-input")
    }

    /// Positional `index`, or agcli's `MISSING_ARG` error naming it.
    fn require_arg(&self, index: usize, name: &str) -> Result<&'a str, CommandError> {
        self.arg(index).ok_or_else(|| {
            CommandError::new(
                format!("missing argument <{name}>"),
                "MISSING_ARG",
                format!("Provide <{name}> as positional argument {index}."),
            )
            .exit_code(agcli::ExitCode::USAGE)
        })
    }

    /// The supplied flags this command never read, as typed (`--name`, `-x`).
    fn unread_flags(&self) -> Vec<String> {
        let read = self.read.borrow();
        let mut unread: Vec<String> = self
            .invocation
            .flags()
            .keys()
            .filter(|key| !read.contains(key.as_str()))
            .filter(|key| !FRAMEWORK_FLAGS.contains(&key.as_str()))
            .map(|key| display_flag(key))
            .collect();
        unread.sort();
        unread
    }

    /// Refuse a flag the command did not read. Call after every read.
    fn reject_unread(&self, command: &str) -> Result<(), CommandError> {
        let unread = self.unread_flags();
        if unread.is_empty() {
            return Ok(());
        }
        // agcli's own code for the same refusal, so an agent handles both
        // the same way.
        Err(CommandError::new(
            format!("unknown flag(s) for `{command}`: {}", unread.join(", ")),
            "UNKNOWN_FLAG",
            format!(
                "`ag-rledger {command}` does not read {}. Remove it, or run \
                 `ag-rledger {command} --help` for the flags it takes.",
                unread.join(", ")
            ),
        )
        .exit_code(agcli::ExitCode::USAGE))
    }
}

/// agcli's reserved flags whose meaning holds on every command without the
/// handler reading them, so they are never refused as unread.
///
/// agcli itself acts on `--select`, `--compact`, `--quiet` (drops
/// `next_actions`) and `--version`, and refuses `--dry-run` on a command that
/// does not declare support. `--json` and `--no-color` describe the envelope,
/// which is always uncolored JSON. `--yes` and `--no-input` say "never
/// prompt", which no command here does.
///
/// Deliberately absent: `--no-cache` and `--stdin`. Each changes what a
/// command does, so a command that does not read it would silently drop it,
/// which is the failure this check exists for. `report --no-cache` was one
/// (it is `rledger report --no-cache`, and was ignored).
const FRAMEWORK_FLAGS: &[&str] = &[
    "select", "compact", "quiet", "version", "dry-run", "json", "no-color", "yes", "no-input",
];

fn display_flag(key: &str) -> String {
    if key.chars().count() == 1 {
        format!("-{key}")
    } else {
        format!("--{key}")
    }
}

/// The flags `rledger` takes on every command: `--profile` and the plugin
/// budget.
struct Globals {
    profile: Option<String>,
    budget: PluginBudgetArgs,
}

/// Read the global flags, build a command's arguments, and refuse any flag
/// the command did not read.
///
/// Every handler goes through this, so none can skip the unread-flag check.
fn parse_request<T>(
    command: &str,
    req: &agcli::CommandRequest<'_>,
    build: impl FnOnce(&Req<'_>) -> Result<T, CommandError>,
) -> Result<(T, Globals), CommandError> {
    let req = Req::new(req.invocation(), req.positionals());
    let globals = Globals {
        profile: profile_from_env_or_flag(&req),
        budget: plugin_budget_flags(&req)?,
    };
    let built = build(&req)?;
    req.reject_unread(command)?;
    Ok((built, globals))
}

/// The plugin-budget flags, parsed by the definition `rledger` uses, so the
/// names, ranges and messages are the same in both binaries.
fn plugin_budget_flags(req: &Req<'_>) -> Result<PluginBudgetArgs, CommandError> {
    let names = PluginBudgetArgs::flags();
    let supplied: Vec<(&str, &str)> = names
        .iter()
        .filter_map(|(long, _)| req.flag(long).map(|value| (long.as_str(), value)))
        .collect();
    PluginBudgetArgs::parse_flags(supplied).map_err(|e| {
        // clap's first line is the error; the rest points at `--help` for a
        // binary this is not.
        let rendered = e.to_string();
        let first = rendered.lines().next().unwrap_or_default();
        let message = first.strip_prefix("error: ").unwrap_or(first).to_string();
        CommandError::new(
            message,
            "INVALID_FLAG",
            "--plugin-max-time-secs takes a whole number of seconds, at least 1; \
             --plugin-max-memory-mb takes MiB, from 1 to 4096.",
        )
        .exit_code(agcli::ExitCode::USAGE)
    })
}

/// The config file, loaded once per process, and the notices loading it
/// emitted (the `RLEDGER_CONFIG` deprecation warning).
///
/// Kept as a `Result` so a file that fails to load is reported, not
/// replaced by defaults. `ag-rledger` used `unwrap_or_default()` here, so a
/// typo anywhere in the file silently reset every setting (#2522), where
/// `rledger` stops with the parse error (#1306).
///
/// The notices are captured rather than written to the process's stderr,
/// which the envelope does not carry, and every command's `warnings` begins
/// with them (#2566).
#[allow(clippy::type_complexity)]
fn loaded_config() -> &'static (
    Result<Config, String>,
    Vec<rustledger_plugin::notice::Notice>,
) {
    static CONFIG: OnceLock<(
        Result<Config, String>,
        Vec<rustledger_plugin::notice::Notice>,
    )> = OnceLock::new();
    CONFIG.get_or_init(|| {
        rustledger_plugin::notice::capture(|| {
            Config::load().map(|loaded| loaded.config).map_err(|e| {
                rustledger_plugin::escape_untrusted_text(&format!("{e:#}")).into_owned()
            })
        })
    })
}

/// The config file, loaded once per process. See [`loaded_config`].
fn config_result() -> &'static Result<Config, String> {
    &loaded_config().0
}

/// What loading the config file had to say. See [`loaded_config`].
fn config_notices() -> &'static [rustledger_plugin::notice::Notice] {
    &loaded_config().1
}

/// The config, for a command that uses it, with the plugin budget applied.
///
/// A config that failed to load is an error here, as in `rledger`: every
/// command except `config` (which `rledger` also exempts, since it is how a
/// broken file gets shown and fixed) calls this before it runs.
fn load_config(budget: &PluginBudgetArgs) -> Result<Config, CommandError> {
    let config = config_result()
        .as_ref()
        .map_err(|message| {
            let error = CommandError::new(
                message.clone(),
                "CONFIG_ERROR",
                "Fix the config file named in the message and retry. `ag-rledger config path` \
                 lists the files read; `ag-rledger config show` still runs.",
            )
            .exit_code(agcli::ExitCode::USAGE);
            // What loading the config had to say rides on the error: the
            // `RLEDGER_CONFIG` deprecation is the likeliest explanation of
            // which file failed, and no command runs to carry it (#2566).
            match warnings_json(&library_diagnostics(&[], CollectedDiagnostics::default())) {
                Some(warnings) => error.data(json!({ "warnings": warnings })),
                None => error,
            }
        })?
        .clone();
    // The WASM plugin and importer budget: each flag, else the config file,
    // as `rledger` applies it (first call wins, so every command sees the
    // same value).
    budget.apply(&config.plugins);
    Ok(config)
}

fn default_file(config: &Config, profile: Option<&str>) -> Option<PathBuf> {
    config.effective_file_path(profile)
}

fn profile_from_env_or_flag(req: &Req<'_>) -> Option<String> {
    string_flag(req, "profile", Some("P"))
        .or_else(|| std::env::var("AG_RLEDGER_PROFILE").ok())
        .or_else(|| std::env::var("RLEDGER_PROFILE").ok())
}

/// A flag by its long name, else its short one; the long one wins when both
/// are given.
///
/// Both are looked up, and so both count as read, even when the long one is
/// present: a lazy `or_else` left the short spelling unread whenever the long
/// one was there, so `--quick a -q b` refused `-q` as unknown.
fn flag<'a>(req: &'a Req<'_>, long: &str, short: Option<&str>) -> Option<&'a str> {
    let long = req.flag(long);
    let short = short.and_then(|s| req.flag(s));
    long.or(short)
}

fn string_flag(req: &Req<'_>, long: &str, short: Option<&str>) -> Option<String> {
    flag(req, long, short).map(str::to_string)
}

fn path_flag(req: &Req<'_>, long: &str, short: Option<&str>) -> Option<PathBuf> {
    flag(req, long, short).map(PathBuf::from)
}

fn bool_flag(req: &Req<'_>, long: &str, short: Option<&str>) -> bool {
    flag(req, long, short).is_some()
}

fn parse_flag<T>(
    req: &Req<'_>,
    long: &str,
    short: Option<&str>,
    default: T,
) -> Result<T, CommandError>
where
    T: std::str::FromStr,
{
    optional_parse_flag(req, long, short).map(|value| value.unwrap_or(default))
}

fn optional_parse_flag<T>(
    req: &Req<'_>,
    long: &str,
    short: Option<&str>,
) -> Result<Option<T>, CommandError>
where
    T: std::str::FromStr,
{
    match flag(req, long, short) {
        Some(raw) => raw.parse::<T>().map(Some).map_err(|_| {
            CommandError::new(
                format!("flag --{long} is not valid: {raw:?}"),
                "INVALID_FLAG",
                format!("Pass a valid value for --{long}."),
            )
            .exit_code(agcli::ExitCode::USAGE)
        }),
        None => Ok(None),
    }
}

fn parse_positional<T>(req: &Req<'_>, index: usize, name: &str) -> Result<T, CommandError>
where
    T: std::str::FromStr,
{
    let raw = req.require_arg(index, name)?;
    raw.parse::<T>().map_err(|_| {
        CommandError::new(
            format!("argument <{name}> is not valid: {raw:?}"),
            "INVALID_ARG",
            format!("Pass a valid value for <{name}>."),
        )
        .exit_code(agcli::ExitCode::USAGE)
    })
}

fn required_path_arg(req: &Req<'_>, index: usize, name: &str) -> Result<PathBuf, CommandError> {
    Ok(PathBuf::from(req.require_arg(index, name)?))
}

fn flag_values(req: &Req<'_>, long: &str, short: Option<&str>) -> Vec<String> {
    let long_flag = format!("--{long}");
    let long_prefix = format!("--{long}=");
    let short_flag = short.map(|s| format!("-{s}"));
    let short_prefix = short.map(|s| format!("-{s}="));
    // Looked up first, so the flag counts as read even when its values come
    // from the raw args below.
    let parsed = flag(req, long, short);
    let raw_args = req.invocation().raw_args();
    let mut values = Vec::new();
    let mut i = 0;

    while i < raw_args.len() {
        let arg = &raw_args[i];
        if arg == &long_flag || short_flag.as_ref().is_some_and(|flag| arg == flag) {
            if let Some(value) = raw_args.get(i + 1)
                && !value.starts_with('-')
            {
                values.extend(split_flag_values(value));
                i += 2;
                continue;
            }
        } else if let Some(value) = arg.strip_prefix(&long_prefix) {
            values.extend(split_flag_values(value));
        } else if let Some(prefix) = short_prefix.as_ref()
            && let Some(value) = arg.strip_prefix(prefix)
        {
            values.extend(split_flag_values(value));
        }
        i += 1;
    }

    if values.is_empty()
        && let Some(raw) = parsed
    {
        values.extend(split_flag_values(raw));
    }

    values
}

fn split_flag_values(raw: &str) -> Vec<String> {
    raw.split(',')
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
        .collect()
}

fn exit_code_to_i32(code: ProcessExitCode) -> i32 {
    i32::from(code != ProcessExitCode::SUCCESS)
}

fn expand_config_aliases(args: Vec<String>) -> Vec<String> {
    // A config that failed to load yields no aliases here; the command that
    // runs reports the error (`load_config`), as `rledger` does.
    let default = Config::default();
    let config = config_result().as_ref().unwrap_or(&default);
    let Some(idx) = first_command_index(&args) else {
        return args;
    };
    let Some(expansion) = config.resolve_alias(&args[idx]) else {
        return args;
    };
    let mut expanded = Vec::new();
    expanded.extend(args[..idx].iter().cloned());
    expanded.extend(parse_alias_expansion(expansion));
    expanded.extend(args[idx + 1..].iter().cloned());
    expanded
}

fn first_command_index(args: &[String]) -> Option<usize> {
    // Global flags whose value can follow as its own argument. Their value
    // is not the command: `--plugin-max-time-secs 5 bal` must expand `bal`.
    let mut value_flags = vec!["-P".to_string(), "--profile".to_string()];
    value_flags.extend(
        PluginBudgetArgs::flags()
            .into_iter()
            .map(|(long, _)| format!("--{long}")),
    );
    let mut skip_next = false;
    for (idx, arg) in args.iter().enumerate().skip(1) {
        if skip_next {
            skip_next = false;
            continue;
        }
        if value_flags.iter().any(|f| f == arg) {
            skip_next = true;
            continue;
        }
        if arg.starts_with('-') {
            continue;
        }
        return Some(idx);
    }
    None
}

fn parse_alias_expansion(expansion: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut in_single_quote = false;
    let mut in_double_quote = false;

    for c in expansion.chars() {
        match c {
            '\'' if !in_double_quote => in_single_quote = !in_single_quote,
            '"' if !in_single_quote => in_double_quote = !in_double_quote,
            ' ' | '\t' if !in_single_quote && !in_double_quote => {
                if !current.is_empty() {
                    parts.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every report `rledger` defines is one `parse_report_name` resolves,
    /// by its name and by each of `rledger`'s aliases for it.
    #[test]
    fn every_rledger_report_name_and_alias_resolves() {
        use clap::Args as _;
        let report = rustledger::cmd::report_cmd::Args::augment_args(clap::Command::new("report"));
        for sub in report.get_subcommands() {
            let name = sub.get_name();
            assert_eq!(parse_report_name(name).as_deref(), Some(name));
            for alias in sub.get_all_aliases() {
                assert_eq!(parse_report_name(alias).as_deref(), Some(name), "{alias}");
            }
        }
        // The longer spellings ag-rledger has always taken still work.
        assert_eq!(parse_report_name("net-worth").as_deref(), Some("networth"));
        assert_eq!(
            parse_report_name("balance-sheet").as_deref(),
            Some("balsheet")
        );
        assert_eq!(
            parse_report_name("income-statement").as_deref(),
            Some("income")
        );
        assert_eq!(parse_report_name("nope"), None);
    }

    /// #2280: the usage string advertised the union of every report's flags,
    /// so `report income` promised `--from`/`--to`/`--period`/`--children` and
    /// then discarded them. It is derived from `rledger`'s definition, per
    /// report, so a report that reads nothing cannot appear as accepting
    /// something.
    #[test]
    fn the_usage_string_does_not_promise_flags_a_report_ignores() {
        let usage = report_flag_usage();
        for (report, flags) in report_flags() {
            let segment = usage
                .split("; ")
                .find(|seg| seg.starts_with(&format!("{report}: ")));
            if flags.is_empty() {
                assert!(
                    segment.is_none(),
                    "`{report}` reads no report-specific flags but appears in the usage string"
                );
                continue;
            }
            let segment = segment.unwrap_or_else(|| {
                panic!("`{report}` reads flags but is missing from the usage string")
            });
            let listed: Vec<&str> = segment
                .split_once(": ")
                .expect("segment is `report: flags`")
                .1
                .split("] [")
                .map(|f| f.trim_matches(['[', ']']))
                .map(|f| f.split([' ', '/']).next().unwrap_or_default())
                .collect();
            let expected: Vec<String> = flags.iter().map(|f| format!("--{}", f.long)).collect();
            assert_eq!(listed, expected, "`{report}`'s usage segment disagrees");
        }
    }

    /// A switch is written `[--irr]` and a flag with a value `[--end <END>]`,
    /// which is how agcli tells them apart: before, `--no-zero ledger.beancount`
    /// would have taken the file as the switch's value.
    #[test]
    fn usage_brackets_switches_and_value_flags_as_agcli_reads_them() {
        let usage = report_flag_usage();
        for switch in ["[--irr]", "[--by-group]", "[--no-zero]", "[--children]"] {
            assert!(usage.contains(switch), "{switch} missing from {usage}");
        }
        assert!(usage.contains("[--account/-a <ACCOUNT>]"), "{usage}");
        assert!(
            usage.contains("[--long-term-days <LONG_TERM_DAYS>]"),
            "{usage}"
        );
    }

    /// The reports from #2280 read no report-specific flags at all, except
    /// `income` and `balsheet`, which read the shared date window (#2643)
    /// and nothing else.
    #[test]
    fn the_reports_that_take_no_flags_still_take_none() {
        for report in ["accounts", "commodities", "stats"] {
            let flags = flags_of(report).unwrap_or_else(|| panic!("`{report}` missing"));
            assert!(flags.is_empty(), "`{report}` now lists {flags:?}");
        }
        for report in ["income", "balsheet"] {
            let flags = flags_of(report).unwrap_or_else(|| panic!("`{report}` missing"));
            let longs: Vec<&str> = flags.iter().map(|f| f.long.as_str()).collect();
            assert_eq!(longs, ["from", "to", "year", "time"], "`{report}`");
        }
    }

    /// `--from` and `--to` belong to the reports that take the shared date
    /// window (#2643) and to no other. #2280 was a window flag accepted and
    /// ignored; a report that does not clamp must still refuse it.
    #[test]
    fn date_window_flags_belong_to_the_windowed_reports_only() {
        const WINDOWED: [&str; 7] = [
            "balances", "balsheet", "income", "journal", "register", "holdings", "budget",
        ];
        for (report, flags) in report_flags() {
            let has_dates = flags.iter().any(|f| f.long == "from" || f.long == "to");
            assert_eq!(
                has_dates,
                WINDOWED.contains(&report.as_str()),
                "`{report}`: {flags:?}"
            );
        }
        for report in ["networth", "returns", "capgains", "stats", "prices"] {
            let refusal = report_refusal(&[report, "--from", "2024-01-01"])
                .unwrap_or_else(|| panic!("`{report} --from` accepted"));
            assert!(refusal.contains("INAPPLICABLE_FLAG"), "{report}: {refusal}");
        }
    }

    /// Build `report <name> <args...>`, returning the error code if refused.
    fn report_refusal(args: &[&str]) -> Option<String> {
        let mut argv = vec!["ag-rledger", "report", "f.beancount"];
        argv.extend_from_slice(args);
        let invocation = agcli::parse_invocation(argv).expect("argv parses");
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        build_report_args(&req).err().map(|e| format!("{e:?}"))
    }

    /// Deep-review finding on #2289: the check knew only long spellings, so
    /// `report income -a Foo` was silently accepted. Every short form comes
    /// from `rledger`'s definition now.
    #[test]
    fn a_short_flag_the_report_does_not_read_is_refused() {
        for args in [
            &["income", "-a", "Assets"][..],
            &["balances", "-l", "5"],
            &["stats", "-i", "Assets"],
            &["journal", "-y", "2024"],
            &["balances", "-e", "2024-01-01"],
        ] {
            let refusal = report_refusal(args).unwrap_or_else(|| panic!("{args:?} accepted"));
            assert!(refusal.contains("INAPPLICABLE_FLAG"), "{args:?}: {refusal}");
        }
    }

    /// `-c` is `prices --commodity` and `networth --currency`: on `prices` it
    /// is the commodity, not a currency flag `prices` does not read. The
    /// hand-kept short-form table knew only one meaning per letter, so it
    /// refused `report prices -c AAPL`.
    #[test]
    fn a_short_flag_shared_between_reports_belongs_to_the_one_asked_for() {
        assert_eq!(report_refusal(&["prices", "-c", "AAPL"]), None);
        assert_eq!(report_refusal(&["networth", "-c", "USD"]), None);
        assert_eq!(
            report_refusal(&["returns", "-i", "Assets", "-c", "USD"]),
            None
        );
        // `-e` is `--end` on both returns and capgains.
        assert_eq!(report_refusal(&["capgains", "-e", "2024-12-31"]), None);
    }

    /// #2567: `report returns` and `report capgains` are offered, each flag
    /// read into `rledger`'s own `Report` variant.
    #[test]
    fn returns_and_capgains_read_their_flags() {
        use rustledger::cmd::report_cmd::Report;
        let build = |args: &[&str]| {
            let mut argv = vec!["ag-rledger", "report", "f.beancount"];
            argv.extend_from_slice(args);
            let invocation = agcli::parse_invocation(argv).expect("argv parses");
            let req = Req::new(&invocation, &invocation.positionals()[1..]);
            let built = build_report_args(&req).map(|a| a.report);
            assert!(req.unread_flags().is_empty(), "{:?}", req.unread_flags());
            built
        };
        let Ok(Report::Returns {
            investments,
            income,
            currency,
            end,
            by_group,
        }) = build(&[
            "returns",
            "-i",
            "Assets:Broker",
            "--investments",
            "Assets:Ira",
            "-n",
            "Income:Div",
            "--currency=EUR",
            "--end",
            "2024-12-31",
            "--by-group",
        ])
        else {
            panic!("returns did not build");
        };
        assert_eq!(investments, ["Assets:Broker", "Assets:Ira"]);
        assert_eq!(income, ["Income:Div"]);
        assert_eq!(currency.as_deref(), Some("EUR"));
        assert_eq!(end.as_deref(), Some("2024-12-31"));
        assert!(by_group);

        let refused = build(&["returns"]).err().map(|e| format!("{e:?}"));
        assert!(
            refused.is_some_and(|e| e.contains("MISSING_FLAG")),
            "--investments is required, as in rledger"
        );

        let Ok(Report::Capgains {
            account,
            year,
            end,
            long_term_days,
            irr,
        }) = build(&[
            "capgains",
            "-a",
            "Assets:Broker",
            "-y",
            "2024",
            "-e",
            "2024-06-30",
            "--long-term-days",
            "400",
            "--irr",
        ])
        else {
            panic!("capgains did not build");
        };
        assert_eq!(account.as_deref(), Some("Assets:Broker"));
        assert_eq!(year, Some(2024));
        assert_eq!(end.as_deref(), Some("2024-06-30"));
        assert_eq!(long_term_days, Some(400));
        assert!(irr);
    }

    /// #2567: `lint closed-nonempty` and `explain` are offered.
    #[test]
    fn closed_nonempty_and_explain_build() {
        use rustledger::cmd::lint::{LintKind, closed_nonempty::OutputFormat};
        let invocation = agcli::parse_invocation([
            "ag-rledger",
            "lint",
            "closed-nonempty",
            "a.beancount",
            "b.beancount",
            "--format",
            "json",
        ])
        .unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        let LintKind::ClosedNonempty(args) = build_lint_args(&req).unwrap().lint else {
            panic!("not closed-nonempty");
        };
        assert_eq!(args.files.len(), 2);
        assert!(matches!(args.format, OutputFormat::Json));

        let invocation = agcli::parse_invocation(["ag-rledger", "explain", "E2001"]).unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        assert_eq!(
            build_explain_args(&req).unwrap().code.as_deref(),
            Some("E2001")
        );
        let invocation = agcli::parse_invocation(["ag-rledger", "explain"]).unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        assert_eq!(build_explain_args(&req).unwrap().code, None);
    }

    /// Run `build` on `ag-rledger <args...>` and return the flags it READ.
    fn flags_read<T>(
        args: &[&str],
        build: impl FnOnce(&Req<'_>) -> Result<T, CommandError>,
    ) -> BTreeSet<String> {
        let mut argv = vec!["ag-rledger"];
        argv.extend_from_slice(args);
        let invocation = agcli::parse_invocation(argv).expect("argv parses");
        // positionals()[0] is the command; the handler sees the rest.
        let positionals = &invocation.positionals()[1..];
        let req = Req::new(&invocation, positionals);
        let _ = build(&req);
        req.read.into_inner()
    }

    /// Whether `build` accepts `ag-rledger <args...>`.
    fn builds<T>(args: &[&str], build: impl FnOnce(&Req<'_>) -> Result<T, CommandError>) -> bool {
        let mut argv = vec!["ag-rledger"];
        argv.extend_from_slice(args);
        let invocation = agcli::parse_invocation(argv).expect("argv parses");
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        build(&req).is_ok()
    }

    /// Every flag name, long and short, that a `rledger` clap command
    /// defines directly (not its subcommands').
    fn rledger_flags(cmd: &clap::Command) -> BTreeSet<String> {
        cmd.get_arguments()
            .filter(|arg| !arg.is_positional())
            .flat_map(|arg| {
                let long = arg.get_long().map(str::to_string);
                let short = arg.get_short().map(|c| c.to_string());
                long.into_iter().chain(short)
            })
            .filter(|name| name != "help" && name != "h")
            .collect()
    }

    /// Assert that `ag-rledger` reads every flag `rledger` defines for a
    /// command, except the ones listed as deliberately unsupported (which
    /// it therefore refuses, rather than ignores).
    #[track_caller]
    fn assert_reads_rledger_flags(
        what: &str,
        rledger: &BTreeSet<String>,
        read: &BTreeSet<String>,
        unsupported: &[&str],
    ) {
        let missing: Vec<&String> = rledger
            .iter()
            .filter(|f| !read.contains(*f) && !unsupported.contains(&f.as_str()))
            .collect();
        assert!(
            missing.is_empty(),
            "`ag-rledger {what}` does not read rledger's {missing:?}: wire them, or list \
             them as unsupported (they are then refused, not ignored)"
        );
        // A stale entry would hide the day the flag gets wired, or the day
        // rledger drops it.
        for flag in unsupported {
            assert!(
                rledger.contains(*flag),
                "`{what}`: {flag} is listed as unsupported but rledger has no such flag"
            );
            assert!(
                !read.contains(*flag),
                "`{what}`: {flag} is listed as unsupported but ag-rledger reads it"
            );
        }
    }

    /// The drift guard for #2522/#2552: a flag added to a `rledger` command
    /// fails here until `ag-rledger` reads it or says it does not. Before,
    /// `ag-rledger` ignored whatever it had not wired, so a new `rledger`
    /// flag went silently missing on the agent surface.
    #[test]
    fn ag_rledger_reads_every_rledger_flag_or_refuses_it() {
        use clap::Args as _;
        use rustledger::cmd;

        // `--generate-completions` writes a shell script, not an answer; the
        // agent surface has no use for it.
        const COMPLETIONS: &str = "generate-completions";
        let command = |name: &'static str| clap::Command::new(name);

        let rledger = rledger_flags(&cmd::check::Args::augment_args(command("check")));
        let read = flags_read(&["check", "f.beancount"], build_check_args);
        assert_reads_rledger_flags("check", &rledger, &read, &[COMPLETIONS]);

        let rledger = rledger_flags(&cmd::query::Args::augment_args(command("query")));
        let read = flags_read(&["query", "f.beancount", "SELECT 1"], build_query_args);
        assert_reads_rledger_flags("query", &rledger, &read, &[COMPLETIONS]);

        let rledger = rledger_flags(&cmd::format::Args::augment_args(command("format")));
        let read = flags_read(&["format", "f.beancount"], build_format_args);
        assert_reads_rledger_flags("format", &rledger, &read, &[COMPLETIONS]);

        let report = cmd::report_cmd::Args::augment_args(command("report"));
        let top = rledger_flags(&report);
        for sub in report.get_subcommands() {
            let name = sub.get_name();
            let mut rledger = top.clone();
            rledger.extend(rledger_flags(sub));
            // Every report `rledger` has must build: a report this binary
            // does not offer is a failure here, not a silent skip (#2567).
            // `returns` requires its portfolio, as in `rledger`.
            let mut argv = vec!["report", "f.beancount", name];
            if name == "returns" {
                argv.extend(["--investments", "Assets"]);
            }
            assert!(
                builds(&argv, build_report_args),
                "`rledger report {name}` is not offered by `ag-rledger report`"
            );
            let read = flags_read(&argv, build_report_args);
            // `--no-pager`: the envelope is never paged.
            assert_reads_rledger_flags(
                &format!("report {name}"),
                &rledger,
                &read,
                &[COMPLETIONS, "no-pager"],
            );
        }

        let doctor = cmd::doctor::Args::augment_args(command("doctor"));
        let top = rledger_flags(&doctor);
        for sub in doctor.get_subcommands() {
            let name = sub.get_name();
            let mut rledger = top.clone();
            rledger.extend(rledger_flags(sub));
            let argv = ["doctor", name, "f.beancount", "1", "2"];
            // Every doctor subcommand `rledger` has must build here, not just
            // have its flags read: `flags_read` ignores a refusal (#2567).
            assert!(
                builds(&argv, build_doctor_command),
                "`rledger doctor {name}` is not offered by `ag-rledger doctor`"
            );
            let read = flags_read(&argv, build_doctor_command);
            assert_reads_rledger_flags(&format!("doctor {name}"), &rledger, &read, &[COMPLETIONS]);
        }

        let rledger = rledger_flags(&cmd::extract_cmd::Args::augment_args(command("extract")));
        let read = flags_read(&["extract", "bank.csv"], build_extract_args);
        assert_reads_rledger_flags("extract", &rledger, &read, &[COMPLETIONS]);

        let price = cmd::price_cmd::Args::augment_args(command("price"));
        let read = flags_read(&["price"], build_price_args);
        assert_reads_rledger_flags("price", &rledger_flags(&price), &read, &[COMPLETIONS]);

        let config = cmd::config_cmd::Args::augment_args(command("config"));
        for sub in config.get_subcommands() {
            let name = sub.get_name();
            assert!(
                builds(&["config", name], build_config_args),
                "`rledger config {name}` is not offered by `ag-rledger config`"
            );
            let read = flags_read(&["config", name], build_config_args);
            assert_reads_rledger_flags(&format!("config {name}"), &rledger_flags(sub), &read, &[]);
        }

        let rledger = rledger_flags(&cmd::add_cmd::Args::augment_args(command("add")));
        let read = flags_read(
            &[
                "add",
                "f.beancount",
                "--quick",
                "p",
                "n",
                "Assets:A",
                "1 USD",
            ],
            build_add_args,
        );
        assert_reads_rledger_flags("add", &rledger, &read, &[]);

        let lint = cmd::lint::Args::augment_args(command("lint"));
        for sub in lint.get_subcommands() {
            let name = sub.get_name();
            // Every lint `rledger` has must be one this binary offers (#2567).
            assert!(
                LINTS.contains(&name),
                "`rledger lint {name}` is not offered"
            );
            let read = flags_read(&["lint", name, "f.beancount"], build_lint_args);
            assert_reads_rledger_flags(&format!("lint {name}"), &rledger_flags(sub), &read, &[]);
        }
        assert_eq!(
            LINTS.len(),
            lint.get_subcommands().count(),
            "LINTS names a lint rledger does not have"
        );

        let rledger = rledger_flags(&cmd::explain::Args::augment_args(command("explain")));
        let read = flags_read(&["explain", "E2001"], build_explain_args);
        assert_reads_rledger_flags("explain", &rledger, &read, &[]);

        // `split` and `merge` (#2633): every flag `rledger` defines is read,
        // and each must build, not just have its flags read.
        let argv = ["split", "f.beancount", "--by", "year"];
        assert!(builds(&argv, build_split_args), "`split` does not build");
        let read = flags_read(&argv, build_split_args);
        assert_reads_rledger_flags("split", &rledger_flags(&split_definition()), &read, &[]);

        let argv = ["merge", "f.beancount"];
        assert!(builds(&argv, build_merge_args), "`merge` does not build");
        let read = flags_read(&argv, build_merge_args);
        assert_reads_rledger_flags("merge", &rledger_flags(&merge_definition()), &read, &[]);
    }

    /// A flag the command does not read is refused, a framework flag is not.
    #[test]
    fn unread_flags_are_reported_and_framework_flags_are_not() {
        let argv = [
            "ag-rledger",
            "format",
            "f.beancount",
            "--no-pager",
            "--plugin-max-mem-mb=5",
            "-z",
            "--select=result",
            "--compact",
            "--json",
        ];
        let invocation = agcli::parse_invocation(argv).unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        build_format_args(&req).unwrap();
        assert_eq!(
            req.unread_flags(),
            vec!["--no-pager", "--plugin-max-mem-mb", "-z"]
        );
        let err = req.reject_unread("format").unwrap_err();
        let text = format!("{err:?}");
        assert!(text.contains("UNKNOWN_FLAG"), "{text}");
        assert!(text.contains("--no-pager"), "{text}");
    }

    /// `--no-cache` changes what a command does, so a command that ignores
    /// it must refuse it, unlike `--select`. `report` reads it now.
    #[test]
    fn no_cache_must_be_read() {
        let invocation =
            agcli::parse_invocation(["ag-rledger", "format", "f.beancount", "--no-cache"]).unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        build_format_args(&req).unwrap();
        assert_eq!(req.unread_flags(), vec!["--no-cache"]);

        let invocation = agcli::parse_invocation([
            "ag-rledger",
            "report",
            "f.beancount",
            "balances",
            "--no-cache",
        ])
        .unwrap();
        let req = Req::new(&invocation, &invocation.positionals()[1..]);
        let args = build_report_args(&req).unwrap();
        assert!(args.no_cache, "report must pass --no-cache through");
        assert!(req.unread_flags().is_empty(), "{:?}", req.unread_flags());
    }

    /// The plugin-budget flags go through `rledger`'s own definition, ranges
    /// included.
    #[test]
    fn plugin_budget_flags_parse_through_the_shared_definition() {
        let parse = |args: &[&str]| {
            let mut argv = vec!["ag-rledger", "check", "f.beancount"];
            argv.extend_from_slice(args);
            let invocation = agcli::parse_invocation(argv).unwrap();
            let req = Req::new(&invocation, &invocation.positionals()[1..]);
            plugin_budget_flags(&req)
        };
        assert_eq!(
            parse(&["--plugin-max-time-secs", "7", "--plugin-max-memory-mb=1024"]).unwrap(),
            PluginBudgetArgs {
                plugin_max_time_secs: Some(7),
                plugin_max_memory_mb: Some(1024),
            }
        );
        assert_eq!(parse(&[]).unwrap(), PluginBudgetArgs::default());
        for bad in [
            ["--plugin-max-time-secs", "0"],
            ["--plugin-max-memory-mb", "0"],
            ["--plugin-max-memory-mb", "4097"],
            ["--plugin-max-time-secs", "soon"],
        ] {
            assert!(parse(&bad).is_err(), "{bad:?} must be refused");
        }
    }

    /// A notice the command's run emits twice is reported twice: only a
    /// repeat of a config-loading notice is dropped. (A plugin printing the
    /// same line on two runs printed it twice.)
    #[test]
    fn repeated_run_notices_are_kept() {
        let notice = rustledger_plugin::notice::Notice {
            code: rustledger_plugin::notice::PLUGIN_STDERR,
            message: "done".to_string(),
        };
        let all = library_diagnostics(&[notice.clone(), notice], CollectedDiagnostics::default());
        let ours = all
            .0
            .iter()
            .filter(|d| d.code.as_deref() == Some("PLUGIN_STDERR"))
            .count();
        assert_eq!(ours, 2, "{:?}", all.0);
    }

    /// The value of a global flag before the command is not the command, so
    /// an alias after it still expands (#2522).
    #[test]
    fn alias_lookup_skips_global_flag_values() {
        let args: Vec<String> = [
            "ag-rledger",
            "--plugin-max-time-secs",
            "5",
            "--plugin-max-memory-mb",
            "512",
            "-P",
            "work",
            "bal",
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        assert_eq!(first_command_index(&args), Some(7));
    }
}
