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
//! than re-declaring every flag in the usage string. The naming is
//! `ag-rledger` (mirroring `rledger`), not `agledger`.

use agcli::{
    ActionParam, AgentCli, Command, CommandError, CommandOutput, ExecutionContext, NextAction,
};
use rustledger::config::Config;
use serde_json::{Value, json};
use std::path::PathBuf;
use std::process::ExitCode as ProcessExitCode;

const SCHEMA_VERSION: &str = "ag-rledger.v1";

#[tokio::main]
async fn main() {
    let args = expand_config_aliases(std::env::args().collect());
    let cli = build_cli();
    let mut ctx = ExecutionContext::default();
    let run = cli.run_argv_with_context(args, &mut ctx).await;
    println!("{}", run.to_json());
    std::process::exit(run.exit_code());
}

fn build_cli() -> AgentCli {
    let cli = AgentCli::new("ag-rledger", "Agent-native plain-text accounting CLI")
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
        .command(lint_command());

    debug_assert!(
        cli.audit().is_clean(),
        "ag-rledger command tree should be agent-auditable: {:?}",
        cli.audit()
    );
    cli
}

fn check_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger check [<file>] [--format <format>] [--json] [--verbose] [-v] [--quiet] \
             [-q] [--no-cache] [-C] [--auto] [-a] [--native-plugin <name>] [--lint <name>]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger check <file> --format=json",
            "Validate a ledger and return diagnostics as JSON",
        ))
        .handler(|req, _ctx| {
            let args = build_check_args(req);
            let profile = profile_from_env_or_flag(req);
            Box::pin(async move {
                let mut args = args?;
                let config = load_config();
                if args.file.is_none() {
                    args.file = default_file(&config, profile.as_deref());
                }
                run_buffered("check", |out| {
                    rustledger::cmd::check::run_with_writer(&args, out).map(exit_code_to_i32)
                })
            })
        })
}

fn query_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger query [<file>] <query...> [--file <file>] [--query-file <file>] \
             [--output <file>] [--format <format>] [--numberify] [-m] [--no-errors] [-q] \
             [--verbose] [-v]",
        )
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
            let args = build_query_args(req);
            let profile = profile_from_env_or_flag(req);
            Box::pin(async move {
                let mut args = args?;
                let config = load_config();
                if args.file.is_none() {
                    args.file = default_file(&config, profile.as_deref());
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
                run_buffered("query", |out| {
                    rustledger::cmd::query::run_with_writer(&args, out).map(|()| 0)
                })
            })
        })
}

fn format_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger format [<file>...] [--output <file>] [--in-place] [-i] [--check] [--diff] \
             [--verbose] [-v]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger format <file> --check",
            "Check whether a ledger is in canonical format",
        ))
        .handler(|req, _ctx| {
            let args = build_format_args(req);
            let profile = profile_from_env_or_flag(req);
            Box::pin(async move {
                let mut args = args?;
                let config = load_config();
                if args.files.is_empty()
                    && let Some(file) = default_file(&config, profile.as_deref())
                {
                    args.files.push(file);
                }
                run_buffered("format", |out| {
                    rustledger::cmd::format::run_with_writer(&args, out).map(exit_code_to_i32)
                })
            })
        })
}

fn report_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger report [<file>] <report> [--file <file>] [--format <format>] [--verbose] \
             [-v] [--account <account>] [--limit <n>] [--period <period>] [--currency <currency>] \
             [--no-zero]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger report <file> balances --format=json",
            "Get balances as JSON",
        ))
        .handler(|req, _ctx| {
            let built = build_report_args(req);
            Box::pin(async move {
                let (file, report, verbose, format) = built?;
                run_buffered("report", |out| {
                    rustledger::cmd::report_cmd::run_with_writer(
                        &file, &report, verbose, &format, out,
                    )
                    .map(|()| 0)
                })
            })
        })
}

fn doctor_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger doctor <subcommand> [args...] [--verbose] [-v] [--conversion <value>] \
             [--output <dir>] [--count <n>] [--seed <n>] [--skip-validation] [--manifest] \
             [--edge-cases-only]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger doctor <subcommand> [args...]",
            "Run a doctor subcommand",
        ))
        .handler(|req, _ctx| {
            let command = build_doctor_command(req);
            Box::pin(async move {
                let command = command?;
                run_buffered("doctor", |out| {
                    rustledger::cmd::doctor::run_with_writer(command, out).map(|()| 0)
                })
            })
        })
}

fn extract_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger extract [<file>] [--file <file>] [--list-importers] [--importer <name>] \
             [--config <file>] [--account <account>] [--currency <currency>] [--auto] \
             [--invert-sign] [--include-zero-amounts] [--no-header] \
             [--output <file>] [--existing <file>] [--suggest-categories] [--balance <amount>]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger extract <file> --account=<account>",
            "Convert a bank file to beancount directives",
        ))
        .handler(|req, _ctx| {
            let args = build_extract_args(req);
            Box::pin(async move {
                let args = args?;
                if args.list_importers {
                    return run_buffered("extract list-importers", |out| {
                        rustledger::cmd::extract_cmd::list_importers_with_writer(&args, out)
                            .map(|()| 0)
                    });
                }
                // Do NOT fall back to `default.file`: that is the ledger
                // path, whereas `extract` reads a *bank statement* to import.
                // Defaulting to the ledger would try to parse it as a
                // statement. Require an explicit input (positional or --file).
                let file = args
                    .file
                    .clone()
                    .ok_or_else(|| missing_file_error("extract"))?;
                run_buffered("extract", |out| {
                    rustledger::cmd::extract_cmd::run_with_writer(&args, &file, out).map(|()| 0)
                })
            })
        })
}

fn price_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger price [<symbol>...] [--file <file>] [--currency <currency>] [--date <date>] \
             [--beancount] [-b] [--verbose] [-v] [--mapping <from:to>] [--source <source>] \
             [--source-cmd <cmd>] [--list-sources] [--clear-cache] [--inactive] \
             [--undeclared] [--all-commodities] [-n] [--clobber] [-C]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .handles_dry_run()
        .default_next_action(NextAction::new(
            "ag-rledger price --file <file> --dry-run",
            "Preview price fetches without network calls",
        ))
        .handler(|req, _ctx| {
            let args = build_price_args(req);
            Box::pin(async move {
                let args = args?;
                let config = load_config();
                run_buffered("price", |out| {
                    rustledger::cmd::price_cmd::run_with_writer(&args, &config.price, out)
                        .map(|()| 0)
                })
            })
        })
}

fn config_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger config <show|path|edit|init|aliases> [--raw] [--format <format>] \
             [--project] [--system] [--force] [-f]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger config <subcommand> [--format=<format>]",
            "Run a configuration subcommand",
        ))
        .handler(|req, _ctx| {
            let args = build_config_args(req);
            Box::pin(async move {
                let args = args?;
                run_buffered("config", |out| {
                    rustledger::cmd::config_cmd::run_with_writer(&args, out).map(|()| 0)
                })
            })
        })
}

fn add_command(name: &'static str, description: &'static str) -> Command {
    Command::new(name, description)
        .usage(
            "ag-rledger add [<file>] --quick <payee> <narration> <account> <amount> <account> \
             [--file <file>] [--date <date>] [--no-completion] [-n] [-y]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .handles_dry_run()
        .default_next_action(NextAction::new(
            "ag-rledger add <file> --quick <payee> <narration> <account> <amount> <account> --dry-run",
            "Preview a transaction without editing the ledger",
        ))
        .handler(|req, _ctx| {
            let args = build_add_args(req);
            let profile = profile_from_env_or_flag(req);
            Box::pin(async move {
                let args = args?;
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
                let config = load_config();
                let file = args
                    .file
                    .clone()
                    .or_else(|| default_file(&config, profile.as_deref()))
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
    .usage("ag-rledger compat <install|uninstall> [--prefix <dir>]")
    .allow_unknown_flags()
    .allow_extra_args()
    .default_next_action(NextAction::new(
        "ag-rledger compat <action> [--prefix=<dir>]",
        "Install or uninstall bean-* wrappers",
    ))
    .handler(|req, _ctx| {
        let action = req.arg(0).map(str::to_string);
        let prefix = path_flag(req, "prefix", None);
        Box::pin(async move {
            let action = action.ok_or_else(|| {
                CommandError::new(
                    "compat action is required",
                    "MISSING_ACTION",
                    "Use `install` or `uninstall`.",
                )
                .exit_code(agcli::ExitCode::USAGE)
            })?;
            match action.as_str() {
                "install" => run_buffered("compat install", |out| {
                    rustledger::cmd::compat::install_with_writer(prefix.as_deref(), out).map(|()| 0)
                }),
                "uninstall" => run_buffered("compat uninstall", |out| {
                    rustledger::cmd::compat::uninstall_with_writer(prefix.as_deref(), out)
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

fn lint_command() -> Command {
    Command::new("lint", "Run non-fatal advisory passes")
        .usage(
            "ag-rledger lint transfers <file>... [--min-confidence <n>] [--date-window <days>] \
             [--amount-tolerance <amount>] [--apply] [--format <format>]",
        )
        .allow_unknown_flags()
        .allow_extra_args()
        .default_next_action(NextAction::new(
            "ag-rledger lint <lint> <file> [--format=<format>]",
            "Run an advisory lint",
        ))
        .handler(|req, _ctx| {
            let args = build_lint_args(req);
            Box::pin(async move {
                let args = args?;
                run_buffered("lint", |out| {
                    rustledger::cmd::lint::run_with_writer(&args, out).map(exit_code_to_i32)
                })
            })
        })
}

fn build_check_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::check::Args, CommandError> {
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
        #[cfg(feature = "python-plugin-wasm")]
        plugins: flag_values(req, "plugin", None)
            .into_iter()
            .map(PathBuf::from)
            .collect(),
        native_plugins: flag_values(req, "native-plugin", None),
        format,
        lints,
        lint_min_confidence: parse_flag(req, "lint-min-confidence", None, 0.8)?,
    })
}

fn build_query_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::query::Args, CommandError> {
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

fn build_format_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::format::Args, CommandError> {
    Ok(rustledger::cmd::format::Args {
        files: req.positionals().iter().map(PathBuf::from).collect(),
        generate_completions: None,
        output: path_flag(req, "output", Some("o")),
        in_place: bool_flag(req, "in-place", Some("i")),
        check: bool_flag(req, "check", None),
        diff: bool_flag(req, "diff", None),
        verbose: bool_flag(req, "verbose", Some("v")),
    })
}

fn build_report_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<
    (
        PathBuf,
        rustledger::cmd::report_cmd::Report,
        bool,
        rustledger::cmd::report_cmd::OutputFormat,
    ),
    CommandError,
> {
    let config = load_config();
    let explicit_file = path_flag(req, "file", None);
    let profile = profile_from_env_or_flag(req);
    let mut positionals = req.positionals().to_vec();
    let first_is_report = positionals
        .first()
        .is_some_and(|s| parse_report_name(s).is_some());
    let file = explicit_file
        .or_else(|| {
            if first_is_report || positionals.is_empty() {
                None
            } else {
                Some(PathBuf::from(positionals.remove(0)))
            }
        })
        .or_else(|| default_file(&config, profile.as_deref()))
        .ok_or_else(|| missing_file_error("report"))?;

    let report_name = positionals.first().ok_or_else(|| {
        CommandError::new(
            "report subcommand is required",
            "MISSING_REPORT",
            "Use balances, income, journal, holdings, networth, accounts, commodities, stats, or prices.",
        )
        .exit_code(agcli::ExitCode::USAGE)
    })?;
    let report = build_report(report_name, req)?;
    let format = match flag(req, "format", Some("f"))
        .or(config.commands.report.output.format.as_deref())
        .unwrap_or("text")
    {
        "text" => rustledger::cmd::report_cmd::OutputFormat::Text,
        "csv" => rustledger::cmd::report_cmd::OutputFormat::Csv,
        "json" => rustledger::cmd::report_cmd::OutputFormat::Json,
        other => return Err(invalid_enum("format", other, &["text", "csv", "json"])),
    };
    Ok((file, report, bool_flag(req, "verbose", Some("v")), format))
}

fn build_report(
    report_name: &str,
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::report_cmd::Report, CommandError> {
    use rustledger::cmd::report_cmd::Report;
    match parse_report_name(report_name).as_deref() {
        Some("balances") => Ok(Report::Balances {
            account: string_flag(req, "account", Some("a")),
        }),
        Some("balsheet") => Ok(Report::Balsheet),
        Some("income") => Ok(Report::Income),
        Some("journal") => Ok(Report::Journal {
            account: string_flag(req, "account", Some("a")),
            limit: optional_parse_flag(req, "limit", Some("l"))?,
        }),
        Some("holdings") => Ok(Report::Holdings {
            account: string_flag(req, "account", Some("a")),
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
        _ => Err(invalid_enum(
            "report",
            report_name,
            &[
                "balances",
                "balsheet",
                "income",
                "journal",
                "holdings",
                "networth",
                "accounts",
                "commodities",
                "stats",
                "prices",
            ],
        )),
    }
}

fn parse_report_name(name: &str) -> Option<String> {
    match name {
        "balances" => Some("balances".to_string()),
        "bal" | "balsheet" | "balance-sheet" => Some("balsheet".to_string()),
        "is" | "income" | "income-statement" => Some("income".to_string()),
        "register" | "journal" => Some("journal".to_string()),
        "holdings" => Some("holdings".to_string()),
        "networth" | "net-worth" => Some("networth".to_string()),
        "accounts" => Some("accounts".to_string()),
        "commodities" => Some("commodities".to_string()),
        "stats" => Some("stats".to_string()),
        "prices" => Some("prices".to_string()),
        _ => None,
    }
}

fn build_doctor_command(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::doctor::Command, CommandError> {
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

fn build_extract_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::extract_cmd::Args, CommandError> {
    let delimiter = flag(req, "delimiter", None)
        .unwrap_or(",")
        .chars()
        .next()
        .unwrap_or(',');
    Ok(rustledger::cmd::extract_cmd::Args {
        generate_completions: None,
        file: path_flag(req, "file", None).or_else(|| req.arg(0).map(PathBuf::from)),
        importer: string_flag(req, "importer", Some("i")),
        config: path_flag(req, "config", None).or_else(|| path_flag(req, "importers-config", None)),
        list_importers: bool_flag(req, "list-importers", None),
        account: string_flag(req, "account", Some("a"))
            .unwrap_or_else(|| "Assets:Bank:Checking".to_string()),
        currency: string_flag(req, "currency", Some("c")).unwrap_or_else(|| "USD".to_string()),
        date_column: string_flag(req, "date-column", None).unwrap_or_else(|| "Date".to_string()),
        date_format: string_flag(req, "date-format", None)
            .unwrap_or_else(|| "%Y-%m-%d".to_string()),
        narration_column: string_flag(req, "narration-column", None)
            .unwrap_or_else(|| "Description".to_string()),
        payee_column: string_flag(req, "payee-column", None),
        amount_column: string_flag(req, "amount-column", None)
            .unwrap_or_else(|| "Amount".to_string()),
        currency_column: string_flag(req, "currency-column", None),
        amount_locale: string_flag(req, "amount-locale", None),
        amount_format: string_flag(req, "amount-format", None),
        debit_column: string_flag(req, "debit-column", None),
        credit_column: string_flag(req, "credit-column", None),
        delimiter,
        skip_rows: parse_flag(req, "skip-rows", None, 0)?,
        invert_sign: bool_flag(req, "invert-sign", None),
        include_zero_amounts: bool_flag(req, "include-zero-amounts", None),
        auto: bool_flag(req, "auto", None),
        no_header: bool_flag(req, "no-header", None),
        use_merchant_dict: bool_flag(req, "use-merchant-dict", None),
        output: path_flag(req, "output", Some("o")),
        existing: path_flag(req, "existing", None),
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

fn build_price_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::price_cmd::PriceArgs, CommandError> {
    Ok(rustledger::cmd::price_cmd::PriceArgs {
        file: path_flag(req, "file", Some("f")),
        symbols: req.positionals().to_vec(),
        currency: string_flag(req, "currency", Some("c")).unwrap_or_else(|| "USD".to_string()),
        date: string_flag(req, "date", Some("d")),
        beancount: bool_flag(req, "beancount", Some("b")),
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

fn build_config_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::config_cmd::Args, CommandError> {
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

fn build_add_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::add_cmd::Args, CommandError> {
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

fn build_lint_args(
    req: &agcli::CommandRequest<'_>,
) -> Result<rustledger::cmd::lint::Args, CommandError> {
    use rustledger::cmd::lint::transfers::{Args as TransfersArgs, OutputFormat};
    use rustledger::cmd::lint::{Args, LintKind};
    let subcommand = req.arg(0).ok_or_else(|| {
        CommandError::new("lint name is required", "MISSING_LINT", "Use `transfers`.")
            .exit_code(agcli::ExitCode::USAGE)
    })?;
    if subcommand != "transfers" {
        return Err(invalid_enum("lint", subcommand, &["transfers"]));
    }
    let format = match flag(req, "format", Some("f")).unwrap_or("text") {
        "text" => OutputFormat::Text,
        "json" => OutputFormat::Json,
        other => return Err(invalid_enum("format", other, &["text", "json"])),
    };
    let files: Vec<PathBuf> = req.positionals()[1..].iter().map(PathBuf::from).collect();
    if files.is_empty() {
        return Err(missing_file_error("lint transfers"));
    }
    Ok(Args {
        lint: LintKind::Transfers(TransfersArgs {
            files,
            min_confidence: parse_flag(req, "min-confidence", None, 0.8)?,
            date_window: parse_flag(req, "date-window", None, 3)?,
            amount_tolerance: string_flag(req, "amount-tolerance", None)
                .unwrap_or_else(|| "0.01".to_string()),
            apply: bool_flag(req, "apply", None),
            format,
        }),
    })
}

fn run_buffered<F>(command: &str, run: F) -> Result<CommandOutput, CommandError>
where
    F: FnOnce(&mut Vec<u8>) -> anyhow::Result<i32>,
{
    let mut stdout = Vec::new();
    let exit_code = run(&mut stdout).map_err(|e| command_failed(&e))?;
    let stdout = String::from_utf8_lossy(&stdout).into_owned();
    let result = command_result(command, &stdout, exit_code);
    Ok(CommandOutput::new(result)
        .exit_code(exit_code)
        .next_action(NextAction::new(
            format!("ag-rledger {command} --help"),
            "Inspect command usage",
        )))
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
    let message = format!("{error:#}");
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

fn load_config() -> Config {
    Config::load()
        .map(|loaded| loaded.config)
        .unwrap_or_default()
}

fn default_file(config: &Config, profile: Option<&str>) -> Option<PathBuf> {
    config.effective_file_path(profile)
}

fn profile_from_env_or_flag(req: &agcli::CommandRequest<'_>) -> Option<String> {
    req.flag("profile")
        .or_else(|| req.flag("P"))
        .map(str::to_string)
        .or_else(|| std::env::var("AG_RLEDGER_PROFILE").ok())
        .or_else(|| std::env::var("RLEDGER_PROFILE").ok())
}

fn flag<'a>(
    req: &'a agcli::CommandRequest<'_>,
    long: &str,
    short: Option<&str>,
) -> Option<&'a str> {
    req.flag(long).or_else(|| short.and_then(|s| req.flag(s)))
}

fn string_flag(req: &agcli::CommandRequest<'_>, long: &str, short: Option<&str>) -> Option<String> {
    flag(req, long, short).map(str::to_string)
}

fn path_flag(req: &agcli::CommandRequest<'_>, long: &str, short: Option<&str>) -> Option<PathBuf> {
    flag(req, long, short).map(PathBuf::from)
}

fn bool_flag(req: &agcli::CommandRequest<'_>, long: &str, short: Option<&str>) -> bool {
    flag(req, long, short).is_some()
}

fn parse_flag<T>(
    req: &agcli::CommandRequest<'_>,
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
    req: &agcli::CommandRequest<'_>,
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

fn parse_positional<T>(
    req: &agcli::CommandRequest<'_>,
    index: usize,
    name: &str,
) -> Result<T, CommandError>
where
    T: std::str::FromStr + std::any::Any,
{
    req.arg_parse(index, name)
        .map_err(|err| err.exit_code(agcli::ExitCode::USAGE))
}

fn required_path_arg(
    req: &agcli::CommandRequest<'_>,
    index: usize,
    name: &str,
) -> Result<PathBuf, CommandError> {
    Ok(PathBuf::from(req.require_arg(index, name)?))
}

fn flag_values(req: &agcli::CommandRequest<'_>, long: &str, short: Option<&str>) -> Vec<String> {
    let long_flag = format!("--{long}");
    let long_prefix = format!("--{long}=");
    let short_flag = short.map(|s| format!("-{s}"));
    let short_prefix = short.map(|s| format!("-{s}="));
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
        && let Some(raw) = flag(req, long, short)
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
    let config = load_config();
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
    let mut skip_next = false;
    for (idx, arg) in args.iter().enumerate().skip(1) {
        if skip_next {
            skip_next = false;
            continue;
        }
        if arg == "-P" || arg == "--profile" {
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
