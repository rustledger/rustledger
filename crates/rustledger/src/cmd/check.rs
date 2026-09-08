//! Shared implementation for bean-check and rledger check commands.

use crate::cmd::completions::ShellType;
use crate::report;
use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use rustledger_loader::LoadError;
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::PluginManager;
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::{PluginInput, PluginOptions};
// The canonical advisory-only predicate lives in `rustledger-validate` so that
// `check` (which hides these, mirroring bean-check) and `lint` share one source
// of truth for which codes are advisory.
use rustledger_validate::is_advisory_only_code;
use serde::Serialize;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Output format for diagnostics.
#[derive(Debug, Clone, Copy, Default, ValueEnum)]
pub enum OutputFormat {
    /// Human-readable text output (default)
    #[default]
    Text,
    /// JSON output for IDE/tooling integration
    Json,
}

/// Advisory lints that can be run alongside `check`.
///
/// Modeled as an enum (not a free-form `String`) so unknown names like
/// `--lint tranfsers` fail at argument parsing time instead of silently
/// no-op'ing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum LintName {
    /// Detect likely unlinked inter-account transfer pairs.
    Transfers,
}

/// A diagnostic message in JSON format.
#[derive(Debug, Serialize)]
pub struct JsonDiagnostic {
    /// Source file path
    pub file: String,
    /// Line number (1-based)
    pub line: usize,
    /// Column number (1-based)
    pub column: usize,
    /// End line number (1-based)
    pub end_line: usize,
    /// End column number (1-based)
    pub end_column: usize,
    /// Severity: "error" or "warning"
    pub severity: String,
    /// Processing phase: "parse", "validate", or "plugin"
    pub phase: String,
    /// Error code (e.g., "P0012", "E1001")
    pub code: String,
    /// Error message
    pub message: String,
    /// Optional hint for fixing the error
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint: Option<String>,
    /// Optional context information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<String>,
}

/// JSON output structure for all diagnostics.
#[derive(Debug, Serialize)]
pub struct JsonOutput {
    /// List of diagnostics
    pub diagnostics: Vec<JsonDiagnostic>,
    /// Total error count
    pub error_count: usize,
    /// Total warning count
    pub warning_count: usize,
    /// Number of parse-phase errors
    pub parse_error_count: usize,
    /// Number of validate-phase errors
    pub validate_error_count: usize,
    /// Diagnostics per rule code, present only with `--show-summary`.
    ///
    /// Emitted rather than dropped because a flag that silently does nothing
    /// in one output format is worse than a slightly larger document. Counts
    /// what was found, so it matches the text summary and is unaffected by
    /// `--include-rules` / `--exclude-rules`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_summary: Option<std::collections::BTreeMap<String, usize>>,
}

/// Convert a byte offset to (line, column) in 1-based indexing.
fn byte_offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Validate beancount files and report errors.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file to check (uses config default if not specified)
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// Show verbose output including timing information
    #[arg(short, long)]
    pub verbose: bool,

    /// Suppress all output (just use exit code)
    #[arg(short, long)]
    pub quiet: bool,

    /// Disable the binary cache for parsed directives.
    ///
    /// Also honored: the `BEANCOUNT_DISABLE_LOAD_CACHE` environment variable
    /// (matching Python beancount). Set the `BEANCOUNT_LOAD_CACHE_FILENAME`
    /// env var to redirect the cache to a custom path.
    #[arg(short = 'C', long = "no-cache")]
    pub no_cache: bool,

    /// Override the cache filename (not yet implemented)
    #[arg(long, value_name = "CACHE_FILE", hide = true)]
    pub cache_filename: Option<PathBuf>,

    /// Implicitly enable auto-plugins (`auto_accounts`, etc.)
    #[arg(short = 'a', long)]
    pub auto: bool,

    /// Load a WASM plugin (can be specified multiple times)
    #[cfg(feature = "python-plugin-wasm")]
    #[arg(long = "plugin", value_name = "WASM_FILE")]
    pub plugins: Vec<PathBuf>,

    /// Run built-in native plugins (e.g., `implicit_prices`, `check_commodity`)
    #[arg(long = "native-plugin", value_name = "NAME")]
    pub native_plugins: Vec<String>,

    /// Output format (text or json)
    #[arg(long, short = 'f', value_enum, default_value = "text")]
    pub format: OutputFormat,

    /// Run non-fatal advisory lints alongside validation.
    ///
    /// Repeatable to enable multiple lints. Findings are emitted as
    /// warnings, never errors — exit code is unaffected.
    #[arg(long = "lint", value_enum, value_name = "NAME")]
    pub lints: Vec<LintName>,

    /// Minimum confidence (0.0 - 1.0) for `--lint transfers` matches to be
    /// reported. Default 0.8 silences the noisy 0.7 floor.
    #[arg(long, default_value_t = 0.8)]
    pub lint_min_confidence: f64,

    /// Print a count of diagnostics per rule code, most frequent first.
    ///
    /// Triage aid for a ledger with many findings: it says what to work on
    /// without scrolling through every occurrence (#2282).
    #[arg(long)]
    pub show_summary: bool,

    /// Report only these rule codes (comma-separated, e.g. `E2001,E1001`).
    ///
    /// Named `--include-rules` rather than `--rules` so later filters can be
    /// `--include-<x>` without the first one having claimed the bare name.
    #[arg(long, value_delimiter = ',', value_name = "CODES")]
    pub include_rules: Vec<String>,

    /// Report everything except these rule codes (comma-separated).
    ///
    /// Applied after `--include-rules`, so excluding a code that was also
    /// included drops it: the narrower instruction wins.
    #[arg(long, value_delimiter = ',', value_name = "CODES")]
    pub exclude_rules: Vec<String>,
}

/// Which rule codes to report, and a tally of what was seen.
///
/// Filtering changes only what is *shown*: the exit code still reflects
/// everything found, because `check` succeeding on a ledger with errors the
/// user chose not to look at would be a lie (#2282).
#[derive(Debug, Default)]
struct RuleFilter {
    include: Option<std::collections::HashSet<String>>,
    exclude: std::collections::HashSet<String>,
    /// Every code seen, before filtering. Counted per code for `--show-summary`.
    seen: std::collections::BTreeMap<String, usize>,
}

impl RuleFilter {
    fn new(args: &Args) -> Self {
        let norm = |v: &[String]| -> std::collections::HashSet<String> {
            v.iter()
                .map(|c| c.trim().to_ascii_uppercase())
                .filter(|c| !c.is_empty())
                .collect()
        };
        Self {
            include: if args.include_rules.is_empty() {
                None
            } else {
                Some(norm(&args.include_rules))
            },
            exclude: norm(&args.exclude_rules),
            seen: std::collections::BTreeMap::new(),
        }
    }

    /// Record a diagnostic and say whether it should be reported.
    ///
    /// The tally counts everything, filtered or not, so the summary can say
    /// how much was hidden rather than only what survived.
    fn keep(&mut self, code: &str) -> bool {
        let code = code.to_ascii_uppercase();
        *self.seen.entry(code.clone()).or_insert(0) += 1;
        if self.exclude.contains(&code) {
            return false;
        }
        self.include.as_ref().is_none_or(|inc| inc.contains(&code))
    }

    fn is_filtering(&self) -> bool {
        self.include.is_some() || !self.exclude.is_empty()
    }
}

/// Run the check command, writing all output to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary. The agent-native `ag-rledger` binary calls `run_with_writer`
/// directly with a buffer so the diagnostics can be captured into a JSON
/// envelope.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the check command with the given arguments, writing diagnostics to
/// `stdout`.
///
/// Behavior is identical to the original `run()`; the only change is that
/// human-readable and JSON output go to the injected writer instead of a
/// hard-coded `io::stdout().lock()`. This lets `ag-rledger` buffer the
/// output into an agent envelope without spawning a subprocess.
pub fn run_with_writer<W: Write>(args: &Args, stdout: &mut W) -> Result<ExitCode> {
    let start = std::time::Instant::now();

    // File is required (the --generate-completions flag is only for standalone bean-check)
    let Some(file) = args.file.as_ref() else {
        anyhow::bail!("FILE is required");
    };

    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Collect diagnostics for JSON output
    let json_mode = matches!(args.format, OutputFormat::Json);
    let mut diagnostics: Vec<JsonDiagnostic> = Vec::new();
    let mut rules = RuleFilter::new(args);

    // Determine if colors should be used (TTY detection + NO_COLOR)
    let use_color = !json_mode && report::should_use_color();

    // Load the parsed file via the shared on-disk parse cache
    // (`cmd::loadcache::load_result_cached`): a cache hit skips the
    // expensive parse and reconstructs an equivalent `LoadResult`,
    // otherwise it parses and saves. `--no-cache` /
    // `BEANCOUNT_DISABLE_LOAD_CACHE` disable it. `from_cache` drives the
    // "(from cache)" note below.
    let (load_result, from_cache) = crate::cmd::loadcache::load_result_cached(
        file,
        args.no_cache,
        args.verbose && !args.quiet,
    )?;

    // Count errors split by phase
    let mut error_count = 0;
    let mut parse_error_count = 0;
    let mut validate_error_count = 0;

    // Report load/parse errors
    for load_error in &load_result.errors {
        match load_error {
            LoadError::ParseErrors { path, errors } => {
                let source = std::fs::read_to_string(path).unwrap_or_default();
                let path_str = path.display().to_string();

                // Filter for DISPLAY only, and keep the original count. The
                // text path hands the whole batch to `report_parse_errors`,
                // which cannot skip individual entries, so the filtered set is
                // built here — but counting it would mean `--exclude-rules`
                // exited 0 on a file that does not parse, which is the worst
                // form of a check reporting success it has not earned.
                let found = errors.len();
                let errors: Vec<_> = errors
                    .iter()
                    .filter(|e| rules.keep(&format!("P{:04}", e.kind_code())))
                    .cloned()
                    .collect();
                let errors = &errors[..];

                if json_mode {
                    for error in errors {
                        let (start_line, start_col) =
                            byte_offset_to_line_col(&source, error.span.start);
                        let (end_line, end_col) = byte_offset_to_line_col(&source, error.span.end);
                        diagnostics.push(JsonDiagnostic {
                            file: path_str.clone(),
                            line: start_line,
                            column: start_col,
                            end_line,
                            end_column: end_col,
                            severity: "error".to_string(),
                            phase: "parse".to_string(),
                            code: format!("P{:04}", error.kind_code()),
                            message: error.message(),
                            hint: error.hint.clone(),
                            context: error.context.clone(),
                        });
                    }
                    error_count += found;
                    parse_error_count += found;
                } else if args.quiet {
                    error_count += found;
                } else {
                    // The reporter returns how many it printed, which is the
                    // filtered count; the ledger's error total is `found`.
                    report::report_parse_errors(errors, path, &source, stdout, use_color)?;
                    error_count += found;
                }
            }
            LoadError::Io { path, source } => {
                let path_str = path.display().to_string();
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0001");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: path_str,
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0001".to_string(),
                        message: format!("failed to read file: {source}"),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(stdout, "error: failed to read {path_str}: {source}")?;
                }
                error_count += 1;
            }
            LoadError::IncludeCycle { cycle } => {
                // Delegate to the canonical Display impl on
                // `LoadError::IncludeCycle` so the wording lives in
                // exactly one place (the `#[error(...)]` attribute on
                // the variant). This is load-bearing for pta-standards
                // conformance (#765): the substring `"Duplicate
                // filename"` must appear, and centralizing the format
                // string prevents it from drifting out of sync with the
                // library-level error.
                let message = load_error.to_string();
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0002");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: cycle.first().cloned().unwrap_or_default(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0002".to_string(),
                        message,
                        hint: Some("break the cycle by removing one of the includes".to_string()),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(stdout, "error: {message}")?;
                }
                error_count += 1;
            }
            LoadError::DuplicateInclude { path } => {
                // Same wording as the cycle case and from the same place —
                // the variant's `#[error(...)]` — so the `"Duplicate
                // filename"` substring the pta-standards conformance test
                // asserts on cannot drift between the two.
                let message = load_error.to_string();
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0004");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: path.clone(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0004".to_string(),
                        message,
                        hint: Some(
                            "the file is included from more than one place; its directives \
                             are loaded once"
                                .to_string(),
                        ),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(stdout, "error: {message}")?;
                }
                error_count += 1;
            }
            LoadError::PathTraversal {
                include_path,
                base_dir,
            } => {
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0003");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: base_dir.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0003".to_string(),
                        message: format!(
                            "path traversal not allowed: {} escapes {}",
                            include_path,
                            base_dir.display()
                        ),
                        hint: Some("use paths within the base directory".to_string()),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(
                        stdout,
                        "error: path traversal not allowed: {} escapes {}",
                        include_path,
                        base_dir.display()
                    )?;
                }
                error_count += 1;
            }
            LoadError::Decryption { path, message } => {
                let path_str = path.display().to_string();
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0004");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: path_str,
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0004".to_string(),
                        message: format!("failed to decrypt: {message}"),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(
                        stdout,
                        "error: failed to decrypt {}: {}",
                        path.display(),
                        message
                    )?;
                }
                error_count += 1;
            }
            LoadError::GlobNoMatch { pattern } => {
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0005");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: file.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0005".to_string(),
                        message: format!("include pattern \"{pattern}\" does not match any files"),
                        hint: Some(
                            "check that the glob pattern is correct and files exist".to_string(),
                        ),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(
                        stdout,
                        "error: include pattern \"{pattern}\" does not match any files"
                    )?;
                }
                error_count += 1;
            }
            LoadError::GlobError { pattern, message } => {
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0006");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: file.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0006".to_string(),
                        message: format!(
                            "failed to expand include pattern \"{pattern}\": {message}"
                        ),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(
                        stdout,
                        "error: failed to expand include pattern \"{pattern}\": {message}"
                    )?;
                }
                error_count += 1;
            }
            LoadError::TooManyFiles { .. } => {
                // Message lives once, on the variant's `#[error(...)]`.
                let message = load_error.to_string();
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("E0007");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: file.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0007".to_string(),
                        message,
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet && shown {
                    writeln!(stdout, "error: {message}")?;
                }
                error_count += 1;
            }
        }
    }

    // All option warnings collected by `Options::set` (E7001 unknown option,
    // E7002 invalid value, E7003 duplicate non-repeatable, E7004/E7005/E7006
    // read-only and related) are surfaced here. Everything except E7003 is a
    // hard error; E7003 is a warning (see below).
    //
    // E7001/E7002 match beancount: `bean-check` exits non-zero on an unknown
    // option or an invalid option value.
    //
    // E7003 (duplicate non-repeatable option) is a WARNING, not an error —
    // matching `bean-check` (last value wins, exit 0), the loader, and
    // `validate`. A master ledger that `include`s self-contained sub-ledgers,
    // each declaring its own `option "title"` / `booking_method` / ... for
    // standalone use, is a legitimate beancount layout; erroring on it rejected
    // that pattern and disagreed with our own loader/`validate` (issue #1546).
    // The value is already last-wins (the loader applies the latest). Pinned by
    // `cli_commands_test::test_check_duplicate_option_warns`.
    //
    // E7009 (option in an included file is ignored) is a warning for the same
    // reason, and the reason is the same LEDGER: #1546's repro declares a
    // title in the master and in each sub-ledger. Once #2151 stopped the
    // included values from governing, that layout started reporting E7009 —
    // so leaving this list at E7003 alone made the exact file #1546 was about
    // exit non-zero again. The unit tests all passed; only running its repro
    // end to end caught it.
    let main_file_str = file.display().to_string();
    let mut option_error_count = 0;
    let mut option_warning_count = 0;
    for warning in &load_result.options.warnings {
        let is_error = !matches!(warning.code, "E7003" | "E7009");
        let severity = if is_error { "error" } else { "warning" };
        // Same treatment as the literal-code sites; this one's code is
        // dynamic, so it needs saying explicitly.
        let shown = rules.keep(&warning.code);
        if json_mode && shown {
            diagnostics.push(JsonDiagnostic {
                file: main_file_str.clone(),
                line: 1,
                column: 1,
                end_line: 1,
                end_column: 1,
                severity: severity.to_string(),
                phase: "parse".to_string(),
                code: warning.code.to_string(),
                message: warning.message.clone(),
                hint: None,
                context: None,
            });
            if is_error {
                parse_error_count += 1;
            }
        } else if !args.quiet && shown {
            writeln!(stdout, "{severity}[{}]: {}", warning.code, warning.message)?;
        }
        if is_error {
            option_error_count += 1;
        } else {
            option_warning_count += 1;
        }
    }
    error_count += option_error_count;

    // === Delegate booking, plugins, and validation to process::process() ===
    //
    // process::process() is the single source of truth for the core pipeline:
    // sort → synth-plugins → Early validation → book → regular-plugins (native +
    // WASM + Python) → Late validation → finalize.
    // check.rs handles: caching, load error reporting, JSON formatting,
    // and CLI-specified --plugin WASM files (below).

    // Build LoadOptions for the processing pipeline
    let load_options = rustledger_loader::LoadOptions {
        run_plugins: true,
        auto_accounts: args.auto,
        extra_plugins: args
            .native_plugins
            .iter()
            .map(|name| rustledger_loader::ExtraPlugin {
                name: name.clone(),
                config: None,
            })
            .collect(),
        validate: true,
        ..Default::default()
    };

    // Clear load errors from the result (already reported above with rich formatting)
    let mut process_input = load_result;
    process_input.errors.clear();

    let ledger = rustledger_loader::process(process_input, &load_options)
        .with_context(|| "processing pipeline failed")?;

    // `@@`→`@` price normalization is done in the loader's `finalize` phase (the
    // shared pipeline), so `ledger.directives` is already normalized — every
    // consumer gets it by construction. See `process::finalize`.
    let spanned_directives = ledger.directives;

    let source_map = &ledger.source_map;
    // One renderer per invocation: amortizes GraphicalReportHandler setup
    // and caches NamedSource per file_id across all errors.
    let mut ledger_error_renderer = report::LedgerErrorRenderer::new(use_color);

    // Convert process errors to diagnostics, using the phase field to
    // split into parse/validate/plugin categories.
    for err in &ledger.errors {
        // Advisory-only diagnostics are not surfaced by `check`, which mirrors
        // `bean-check`: Python beancount does not flag closing an account with a
        // residual balance (E1004). They are reported by `rledger lint
        // closed-nonempty` instead.
        if is_advisory_only_code(&err.code) {
            continue;
        }
        // `keep` also tallies, so this must run for every non-advisory
        // diagnostic even when no filter is active. It decides DISPLAY only:
        // `error_count` below still counts a hidden error, because exiting 0
        // on a ledger whose errors the user chose not to look at would report
        // success for a broken file — and `--exclude-rules` in CI would then
        // hide exactly what CI is for.
        let shown = rules.keep(&err.code);
        let severity_str = match err.severity {
            rustledger_loader::ErrorSeverity::Error => "error",
            rustledger_loader::ErrorSeverity::Warning => "warning",
        };

        if json_mode && shown {
            // Compute end line/column from the error's byte span when
            // available, so multi-line directives (e.g. an unbalanced
            // transaction covering 3 lines) report a real end position
            // instead of falling back to start==end (issue #901).
            let loc = err.location.as_ref();
            let fallback_end = (loc.map_or(1, |l| l.line), loc.map_or(1, |l| l.column));
            let (end_line, end_column) = err
                .source_span
                .zip(err.file_id)
                .and_then(|((_, end), fid)| source_map.get(fid as usize).map(|f| f.line_col(end)))
                .unwrap_or(fallback_end);
            diagnostics.push(JsonDiagnostic {
                file: err
                    .location
                    .as_ref()
                    .map_or_else(|| main_file_str.clone(), |l| l.file.display().to_string()),
                line: err.location.as_ref().map_or(1, |l| l.line),
                column: err.location.as_ref().map_or(1, |l| l.column),
                end_line,
                end_column,
                severity: severity_str.to_string(),
                phase: err.phase.clone(),
                code: err.code.clone(),
                message: err.message.clone(),
                hint: None,
                context: None,
            });

            match (err.severity, err.phase.as_str()) {
                (rustledger_loader::ErrorSeverity::Error, "parse") => {
                    parse_error_count += 1;
                }
                (rustledger_loader::ErrorSeverity::Error, "validate") => {
                    validate_error_count += 1;
                }
                _ => {}
            }
        } else if !args.quiet && shown {
            // When the error carries span+file_id and we can resolve the
            // source, render via miette so the user gets a snippet of the
            // offending directive (issue #901). Fall back to a one-line
            // `file:line:col: error[CODE]: message` for errors without
            // span info (e.g. plugin errors, cross-file invariants).
            ledger_error_renderer.render(err, source_map, stdout)?;
        }

        if matches!(err.severity, rustledger_loader::ErrorSeverity::Error) {
            error_count += 1;
        }
    }
    let warning_count = option_warning_count
        + ledger
            .errors
            .iter()
            .filter(|e| {
                matches!(e.severity, rustledger_loader::ErrorSeverity::Warning)
                    && !is_advisory_only_code(&e.code)
            })
            .count();
    #[cfg(feature = "python-plugin-wasm")]
    let mut warning_count = warning_count;

    // === Run CLI-specified WASM plugins as post-processing ===
    // File-declared plugins (native, WASM, Python) are all handled by
    // process::process(). Only CLI --plugin flags need post-process handling.
    #[cfg(feature = "python-plugin-wasm")]
    if !args.plugins.is_empty() {
        let wrappers: Vec<_> = spanned_directives
            .iter()
            .map(|s| rustledger_plugin::directive_to_wrapper(&s.value))
            .collect();

        let current_input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: ledger.options.operating_currency.clone(),
                title: ledger.options.title.clone(),
                // Same as the loader pipeline: CLI-specified WASM plugins must
                // see the ledger's own root names, or they misclassify on a
                // renamed ledger just as the native ones did (#1964).
                account_types: rustledger_plugin::PluginAccountTypes {
                    assets: ledger.options.name_assets.clone(),
                    liabilities: ledger.options.name_liabilities.clone(),
                    equity: ledger.options.name_equity.clone(),
                    income: ledger.options.name_income.clone(),
                    expenses: ledger.options.name_expenses.clone(),
                },
            },
            config: None,
        };

        let mut wasm_mgr = PluginManager::new();
        for plugin_path in &args.plugins {
            if let Err(e) = wasm_mgr.load(plugin_path) {
                let msg = format!("failed to load WASM plugin {}: {e}", plugin_path.display());
                // Tally and filter like every other diagnostic, so
                // --show-summary counts this and --exclude-rules can hide it.
                // The count below is deliberately outside: hiding a
                // diagnostic must not change the exit code.
                let shown = rules.keep("PLUGIN");
                if json_mode && shown {
                    diagnostics.push(JsonDiagnostic {
                        file: main_file_str.clone(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "plugin".to_string(),
                        code: "PLUGIN".to_string(),
                        message: msg,
                        hint: None,
                        context: None,
                    });
                } else if !args.quiet && shown {
                    writeln!(stdout, "error: {msg}")?;
                }
                error_count += 1;
            }
        }
        if !wasm_mgr.is_empty() {
            match wasm_mgr.execute_all(current_input) {
                Ok(output) => {
                    for err in &output.errors {
                        let sev = match err.severity {
                            rustledger_plugin::PluginErrorSeverity::Error => "error",
                            rustledger_plugin::PluginErrorSeverity::Warning => "warning",
                        };
                        // Tally and filter like every other diagnostic, so
                        // --show-summary counts this and --exclude-rules can hide it.
                        // The count below is deliberately outside: hiding a
                        // diagnostic must not change the exit code.
                        let shown = rules.keep("PLUGIN");
                        if json_mode && shown {
                            diagnostics.push(JsonDiagnostic {
                                file: main_file_str.clone(),
                                line: 1,
                                column: 1,
                                end_line: 1,
                                end_column: 1,
                                severity: sev.to_string(),
                                phase: "plugin".to_string(),
                                code: "PLUGIN".to_string(),
                                message: err.message.clone(),
                                hint: None,
                                context: None,
                            });
                        } else if !args.quiet && shown {
                            writeln!(stdout, "{sev}: {}", err.message)?;
                        }
                        match err.severity {
                            rustledger_plugin::PluginErrorSeverity::Error => {
                                error_count += 1;
                            }
                            rustledger_plugin::PluginErrorSeverity::Warning => {
                                warning_count += 1;
                            }
                        }
                    }
                }
                Err(e) => {
                    let msg = format!("WASM plugin execution failed: {e}");
                    // Tally and filter like every other diagnostic, so
                    // --show-summary counts this and --exclude-rules can hide it.
                    // The count below is deliberately outside: hiding a
                    // diagnostic must not change the exit code.
                    let shown = rules.keep("PLUGIN");
                    if json_mode && shown {
                        diagnostics.push(JsonDiagnostic {
                            file: main_file_str.clone(),
                            line: 1,
                            column: 1,
                            end_line: 1,
                            end_column: 1,
                            severity: "error".to_string(),
                            phase: "plugin".to_string(),
                            code: "PLUGIN".to_string(),
                            message: msg,
                            hint: None,
                            context: None,
                        });
                    } else if !args.quiet && shown {
                        writeln!(stdout, "error: {msg}")?;
                    }
                    error_count += 1;
                }
            }
        }
    }

    // === Non-fatal advisory lints (--lint NAME) ===
    // Lint findings are warnings, never errors. They never affect exit code.
    // Under `python-plugin-wasm` the binding above is already `mut`; rebind
    // here only for the other cfg branch.
    #[cfg(not(feature = "python-plugin-wasm"))]
    let mut warning_count = warning_count;
    if args.lints.contains(&LintName::Transfers) {
        // Pair each core directive with its source location (no `DirectiveWrapper`
        // deep clone — the directive is borrowed, only the location is owned).
        let located: Vec<rustledger_ops::transfer::LocatedDirective<'_>> = spanned_directives
            .iter()
            .map(|spanned| {
                let (filename, lineno) =
                    if let Some(file) = source_map.get(spanned.file_id as usize) {
                        let (line, _col) = file.line_col(spanned.span.start);
                        (
                            Some(file.path.to_string_lossy().into_owned()),
                            u32::try_from(line).ok(),
                        )
                    } else {
                        (None, None)
                    };
                rustledger_ops::transfer::LocatedDirective {
                    directive: &spanned.value,
                    filename,
                    lineno,
                }
            })
            .collect();
        let config = rustledger_ops::transfer::TransferConfig::default();
        let matches: Vec<_> = rustledger_ops::transfer::find_transfers_in_ledger(&located, &config)
            .into_iter()
            .filter(|m| m.confidence >= args.lint_min_confidence)
            .collect();
        for m in &matches {
            let msg = format!(
                "likely transfer pair: {} {} {} → {} (confidence {:.2}); link with ^xfer-... to silence",
                m.amount,
                m.currency,
                m.from_account.as_deref().unwrap_or("?"),
                m.to_account.as_deref().unwrap_or("?"),
                m.confidence,
            );
            // Tally and filter like every other diagnostic, so
            // --show-summary counts this and --exclude-rules can hide it.
            // The count below is deliberately outside: hiding a
            // diagnostic must not change the exit code.
            let shown = rules.keep("LINT-XFER");
            if json_mode && shown {
                diagnostics.push(JsonDiagnostic {
                    file: m
                        .from_filename
                        .clone()
                        .unwrap_or_else(|| main_file_str.clone()),
                    line: m.from_lineno.map_or(1, |n| n as usize),
                    column: 1,
                    end_line: m.from_lineno.map_or(1, |n| n as usize),
                    end_column: 1,
                    severity: "warning".to_string(),
                    phase: "lint".to_string(),
                    code: "LINT-XFER".to_string(),
                    message: msg,
                    hint: Some(
                        "run `rledger lint transfers --apply <files>` to add links".to_string(),
                    ),
                    context: None,
                });
            } else if !args.quiet && shown {
                let loc = format!(
                    "{}:{}",
                    m.from_filename.as_deref().unwrap_or("?"),
                    m.from_lineno.map_or_else(|| "?".into(), |n| n.to_string()),
                );
                writeln!(stdout, "{loc}: warning[LINT-XFER]: {msg}")?;
            }
            warning_count += 1;
        }
    }

    // Print summary / output
    let elapsed = start.elapsed();

    if json_mode {
        let output = JsonOutput {
            diagnostics,
            error_count,
            warning_count,
            parse_error_count,
            validate_error_count,
            rule_summary: args.show_summary.then(|| rules.seen.clone()),
        };
        writeln!(stdout, "{}", serde_json::to_string_pretty(&output)?)?;
    } else if !args.quiet {
        if args.verbose {
            let cache_note = if from_cache { " (from cache)" } else { "" };
            writeln!(
                stdout,
                "\nChecked in {:.2}ms{}",
                elapsed.as_secs_f64() * 1000.0,
                cache_note
            )?;
        }
        report::print_summary(error_count, warning_count, stdout, use_color)?;
    }

    // Rule tally, most frequent first. Printed after the diagnostics so it is
    // the last thing on screen, which is where a reader lands after scrolling.
    // Suppressed in JSON mode: a consumer there has the codes already and can
    // count them itself, and a second shape in the same document would be a
    // schema change for no gain.
    // JSON carries the same tally in `rule_summary`, so this is the text form
    // only rather than a second shape in the same document.
    if args.show_summary && !json_mode && !args.quiet {
        let mut rows: Vec<(&String, &usize)> = rules.seen.iter().collect();
        // Count descending, then code ascending, so the order is stable rather
        // than dependent on map iteration for equal counts.
        rows.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));

        if rows.is_empty() {
            writeln!(stdout, "\nNo diagnostics.")?;
        } else {
            let total: usize = rows.iter().map(|(_, n)| **n).sum();
            writeln!(stdout, "\nSummary ({total} total):")?;
            let width = rows
                .iter()
                .map(|(_, n)| n.to_string().len())
                .max()
                .unwrap_or(1);
            for (code, count) in rows {
                writeln!(stdout, "  {count:>width$}  {code}")?;
            }
            // The tally counts what was found, not what was shown, so a filtered
            // run would otherwise look like the filter had changed the ledger.
            if rules.is_filtering() {
                writeln!(
                    stdout,
                    "  (counts are before --include-rules/--exclude-rules)"
                )?;
            }
        }
    }

    if error_count > 0 {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A ledger with one E1001 (unopened account) and two E2001s.
    fn ledger_with_mixed_errors() -> tempfile::NamedTempFile {
        use std::io::Write as _;
        let mut f = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        f.write_all(
            b"2020-01-01 open Assets:Bank USD\n\
              2020-01-01 open Expenses:X USD\n\n\
              2024-01-15 * \"a\"\n  Assets:Bank  -10.00 USD\n  Expenses:X\n\n\
              2024-02-01 balance Assets:Bank  999.00 USD\n\
              2024-03-01 balance Assets:Bank  888.00 USD\n\n\
              2024-04-01 * \"unopened\"\n  Assets:Nope  1.00 USD\n  Expenses:X\n",
        )
        .unwrap();
        f.flush().unwrap();
        f
    }

    fn check_exit(path: &std::path::Path, extra: &[&str]) -> (ExitCode, String) {
        let mut argv = vec!["check", path.to_str().unwrap()];
        argv.extend_from_slice(extra);
        let args = Args::parse_from(argv);
        let mut out = Vec::new();
        let code = run_with_writer(&args, &mut out).expect("check runs");
        (code, String::from_utf8(out).unwrap())
    }

    /// #2282, the property that matters most: hiding a diagnostic must not
    /// make the run succeed. `--exclude-rules` in CI would otherwise mask
    /// exactly what CI is for. My first cut of this got it wrong — the filter
    /// skipped the counting as well as the display, so excluding everything
    /// exited 0 on a broken ledger.
    #[test]
    fn filtering_hides_diagnostics_without_changing_the_exit_code() {
        let f = ledger_with_mixed_errors();
        let failure = format!("{:?}", ExitCode::from(1));

        let (unfiltered, text) = check_exit(f.path(), &[]);
        assert_eq!(format!("{unfiltered:?}"), failure, "the ledger has errors");
        assert!(text.contains("E2001") && text.contains("E1001"));

        let (excluded, text) = check_exit(f.path(), &["--exclude-rules", "E2001"]);
        assert!(!text.contains("E2001"), "excluded code must not be shown");
        assert!(text.contains("E1001"), "other codes must survive");
        assert_eq!(
            format!("{excluded:?}"),
            failure,
            "hiding a diagnostic must not turn a failing check into a pass"
        );

        let (all_hidden, _) = check_exit(f.path(), &["--exclude-rules", "E2001,E1001"]);
        assert_eq!(
            format!("{all_hidden:?}"),
            failure,
            "hiding EVERY diagnostic must still fail"
        );

        let (included, text) = check_exit(f.path(), &["--include-rules", "E2001"]);
        assert!(text.contains("E2001") && !text.contains("E1001"));
        assert_eq!(format!("{included:?}"), failure);
    }

    /// Deep-review finding on #2286: the parse path counted the FILTERED
    /// slice, so `--exclude-rules P0012` exited 0 on a file that does not
    /// parse. Same bug as the validation path, and my earlier test only
    /// covered E-codes so it missed this.
    #[test]
    fn excluding_a_parse_error_does_not_make_the_check_pass() {
        use std::io::Write as _;
        let mut f = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        f.write_all(b"2020-01-01 open Assets:Bank USD\nthis does not parse ~~~\n")
            .unwrap();
        f.flush().unwrap();

        let failure = format!("{:?}", ExitCode::from(1));
        let (unfiltered, text) = check_exit(f.path(), &[]);
        assert_eq!(format!("{unfiltered:?}"), failure);
        assert!(text.contains("P0012"), "precondition: got\n{text}");

        let (excluded, text) = check_exit(f.path(), &["--exclude-rules", "P0012"]);
        assert!(!text.contains("P0012"), "the code must be hidden");
        assert_eq!(
            format!("{excluded:?}"),
            failure,
            "a file that does not parse must never report success"
        );
    }

    /// Second review pass on #2286: only the parse and validation loops were
    /// tallied, so a load-level failure produced the contradiction
    /// "✗ 1 error" followed by "No diagnostics.", and `--exclude-rules` could
    /// not touch it. Partial filtering was the thing I had already refused to
    /// ship for parse errors.
    #[test]
    fn load_level_errors_are_tallied_and_filterable() {
        let dir = tempfile::tempdir().unwrap();
        let a = dir.path().join("a.beancount");
        let b = dir.path().join("b.beancount");
        std::fs::write(&a, "include \"b.beancount\"\n").unwrap();
        std::fs::write(&b, "include \"a.beancount\"\n").unwrap();

        let (_, text) = check_exit(&a, &["--show-summary"]);
        assert!(
            text.contains("E0002"),
            "an include cycle must reach the summary; got:\n{text}"
        );
        assert!(
            !text.contains("No diagnostics"),
            "summary must not contradict the error count; got:\n{text}"
        );

        let failure = format!("{:?}", ExitCode::from(1));
        let (code, text) = check_exit(&a, &["--exclude-rules", "E0002"]);
        assert!(!text.contains("Duplicate filename"), "excluded code shown");
        assert_eq!(
            format!("{code:?}"),
            failure,
            "an unreadable ledger must not report success"
        );
    }

    /// A flag that silently does nothing in one output format is worse than a
    /// slightly larger document, so JSON carries the same tally.
    #[test]
    fn json_carries_the_rule_summary_only_when_asked() {
        let f = ledger_with_mixed_errors();

        let (_, text) = check_exit(f.path(), &["--format", "json", "--show-summary"]);
        let v: serde_json::Value = serde_json::from_str(&text).expect("valid json");
        assert_eq!(v["rule_summary"]["E2001"], 2);
        assert_eq!(v["rule_summary"]["E1001"], 1);

        let (_, text) = check_exit(f.path(), &["--format", "json"]);
        let v: serde_json::Value = serde_json::from_str(&text).expect("valid json");
        assert!(
            v.get("rule_summary").is_none(),
            "the field must be absent unless asked for"
        );
    }

    /// The summary counts what was found, in descending order.
    #[test]
    fn show_summary_reports_counts_per_code() {
        let f = ledger_with_mixed_errors();
        let (_, text) = check_exit(f.path(), &["--show-summary"]);
        let summary = text.split("Summary").nth(1).expect("a summary section");
        let e2001 = summary.find("E2001").expect("E2001 counted");
        let e1001 = summary.find("E1001").expect("E1001 counted");
        assert!(
            e2001 < e1001,
            "two E2001s must sort above one E1001:\n{summary}"
        );
        assert!(summary.contains("3 total"), "got:\n{summary}");
    }

    /// Build `Args` with only the rule flags set, for the filter tests.
    fn rule_args(include: &[&str], exclude: &[&str]) -> Args {
        let mut argv = vec!["check", "f.beancount"];
        let inc = include.join(",");
        let exc = exclude.join(",");
        if !include.is_empty() {
            argv.push("--include-rules");
            argv.push(&inc);
        }
        if !exclude.is_empty() {
            argv.push("--exclude-rules");
            argv.push(&exc);
        }
        Args::parse_from(argv)
    }

    /// #2282: no flags means report everything, and the tally still counts.
    #[test]
    fn no_rule_flags_keeps_everything() {
        let mut f = RuleFilter::new(&rule_args(&[], &[]));
        assert!(f.keep("E2001"));
        assert!(f.keep("P0012"));
        assert!(!f.is_filtering());
        assert_eq!(f.seen.get("E2001"), Some(&1));
    }

    #[test]
    fn include_rules_keeps_only_those_codes() {
        let mut f = RuleFilter::new(&rule_args(&["E2001"], &[]));
        assert!(f.keep("E2001"));
        assert!(!f.keep("E1001"));
        assert!(f.is_filtering());
    }

    #[test]
    fn exclude_rules_drops_those_codes() {
        let mut f = RuleFilter::new(&rule_args(&[], &["E2001"]));
        assert!(!f.keep("E2001"));
        assert!(f.keep("E1001"));
    }

    /// Excluding a code that was also included drops it: the narrower
    /// instruction wins, rather than the order of the flags deciding.
    #[test]
    fn exclude_beats_include_for_the_same_code() {
        let mut f = RuleFilter::new(&rule_args(&["E2001", "E1001"], &["E2001"]));
        assert!(!f.keep("E2001"));
        assert!(f.keep("E1001"));
    }

    /// Codes are written uppercase everywhere, but nobody should have to know
    /// that when typing a flag.
    #[test]
    fn rule_codes_are_case_insensitive() {
        let mut f = RuleFilter::new(&rule_args(&["e2001"], &[]));
        assert!(f.keep("E2001"));
        assert!(f.keep("e2001"));
        assert!(!f.keep("E1001"));
    }

    /// The tally counts what was FOUND, not what was shown, so `--show-summary`
    /// with a filter still says how much exists.
    #[test]
    fn the_tally_counts_filtered_out_diagnostics() {
        let mut f = RuleFilter::new(&rule_args(&[], &["E2001"]));
        assert!(!f.keep("E2001"));
        assert!(!f.keep("E2001"));
        assert!(f.keep("E1001"));
        assert_eq!(
            f.seen.get("E2001"),
            Some(&2),
            "hidden diagnostics still count"
        );
        assert_eq!(f.seen.get("E1001"), Some(&1));
    }

    /// Whitespace and empty entries in a comma list must not become a rule
    /// nobody can match, which would silently drop every diagnostic.
    #[test]
    fn blank_and_padded_entries_are_ignored() {
        let args = Args::parse_from(["check", "f.beancount", "--include-rules", " E2001 ,, "]);
        let mut f = RuleFilter::new(&args);
        assert!(f.keep("E2001"));
        assert!(!f.keep("E1001"));
    }

    #[test]
    fn test_json_diagnostic_phase_field_serializes() {
        let diag = JsonDiagnostic {
            file: "test.beancount".to_string(),
            line: 1,
            column: 1,
            end_line: 1,
            end_column: 1,
            severity: "error".to_string(),
            phase: "parse".to_string(),
            code: "P0001".to_string(),
            message: "test error".to_string(),
            hint: None,
            context: None,
        };
        let json = serde_json::to_value(&diag).unwrap();
        assert_eq!(json["phase"], "parse");

        let diag_validate = JsonDiagnostic {
            phase: "validate".to_string(),
            ..diag
        };
        let json = serde_json::to_value(&diag_validate).unwrap();
        assert_eq!(json["phase"], "validate");
    }

    #[test]
    fn test_json_output_includes_phase_counts() {
        let output = JsonOutput {
            diagnostics: vec![],
            error_count: 3,
            warning_count: 0,
            parse_error_count: 1,
            validate_error_count: 2,
            rule_summary: None,
        };
        let json = serde_json::to_value(&output).unwrap();
        assert_eq!(json["parse_error_count"], 1);
        assert_eq!(json["validate_error_count"], 2);
        assert_eq!(json["error_count"], 3);
    }
}
