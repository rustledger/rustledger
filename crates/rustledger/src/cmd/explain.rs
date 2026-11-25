//! `rledger explain` — describe a diagnostic code, `rustc --explain` style.
//!
//! `rledger explain E2001` prints what the code means, its common cause, and
//! how to fix it; bare `rledger explain` lists every code with its title.
//!
//! It covers every code `rledger check` can print, from two places:
//!
//! - the validator's codes: the text lives on [`ErrorCode`] itself
//!   (`title`/`explanation`), whose exhaustive match keeps it in lockstep
//!   with the enum;
//! - the parser's `P` codes (`P{kind_code:04}`), the loader's `E0xxx` file
//!   and include codes, the option codes `ErrorCode` does not carry, the
//!   plugin codes and `BOOK`/`PLUGIN`/`LOAD`: the text lives in [`OTHER`]
//!   below, because the crates that raise them carry no such text.
//!
//! `tests/explain_drift_test.rs` enumerates every code from its canonical
//! definition (`ErrorCode::ALL`, `ParseError::every_kind_sample`,
//! `OptionWarning::ALL_CODES`, and the literal codes `check` and the loader
//! raise) and asserts this command knows each, so a new code cannot ship
//! without an explanation.

use std::process::ExitCode;

use anyhow::Result;
use clap::Parser;
use rustledger_loader::OptionWarning;
use rustledger_validate::{ErrorCode, Severity};

/// Arguments for `rledger explain`.
#[derive(Debug, Parser)]
pub struct Args {
    /// The diagnostic code to explain (e.g. `E2001`, `e2001`, `2001`,
    /// `P0012`, `BOOK`). Omit to list all codes.
    pub code: Option<String>,
}

/// One code `explain` knows that is not an [`ErrorCode`].
struct OtherCode {
    code: &'static str,
    /// The group it is listed under.
    group: Group,
    /// `true` for an error, `false` for a warning. For an option code this
    /// must agree with [`OptionWarning::is_error_code`] (pinned by a test).
    error: bool,
    title: &'static str,
    explanation: &'static str,
}

/// The groups the listing is printed in, in order.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Group {
    Load,
    Parse,
    Validation,
    Plugin,
}

impl Group {
    const ALL: [Self; 4] = [Self::Load, Self::Parse, Self::Validation, Self::Plugin];

    const fn heading(self) -> &'static str {
        match self {
            Self::Load => "Loading (files and includes)",
            Self::Parse => "Parsing",
            Self::Validation => "Validation, booking and options",
            Self::Plugin => "Plugins",
        }
    }
}

/// The codes with no text of their own in the crate that raises them.
///
/// A code that is also an [`ErrorCode`] (`E8001`, which the plugin loader
/// reuses for "plugin not found") is shown after the validator's text as a
/// second meaning.
const OTHER: &[OtherCode] = &[
    // === Loader: files and includes (E0xxx), raised by `check` ===
    OtherCode {
        code: "E0001",
        group: Group::Load,
        error: true,
        title: "File cannot be read",
        explanation: "The ledger file, or a file an `include` names, does not exist or \
                      cannot be read (permissions, a directory, invalid UTF-8).\n\nWhen \
                      the file is an include target, the error is reported at the \
                      `include` line.\n\nFix: correct the path (a relative include \
                      resolves against the including file's directory), or fix the \
                      file's permissions.",
    },
    OtherCode {
        code: "E0002",
        group: Group::Load,
        error: true,
        title: "Include cycle",
        explanation: "A file includes itself, directly or through other includes. The \
                      error is reported at the `include` that closed the cycle.\n\nFix: \
                      remove the `include` that points back up the chain; a tree of \
                      includes has one root.",
    },
    OtherCode {
        code: "E0003",
        group: Group::Load,
        error: true,
        title: "Include path escapes the ledger directory",
        explanation: "An `include` resolves to a path outside the directory the loader \
                      may read (path traversal protection, e.g. \
                      `include \"../../etc/x\"`).\n\nFix: move the included file under \
                      the ledger's directory, or load the ledger from a directory that \
                      contains both.",
    },
    OtherCode {
        code: "E0004",
        group: Group::Load,
        error: true,
        title: "Duplicate include, or a file that cannot be decrypted",
        explanation: "Either the same file is included from more than one place (its \
                      directives are loaded once, and this is reported as \"Duplicate \
                      filename\", as beancount does), or an encrypted (GPG) file could \
                      not be decrypted.\n\nFix: keep a single `include` of the file; for \
                      an encrypted file, check that `gpg` can decrypt it with your \
                      keys.",
    },
    OtherCode {
        code: "E0005",
        group: Group::Load,
        error: true,
        title: "Include pattern matches no files",
        explanation: "A glob `include` (e.g. `include \"2024/*.beancount\"`) matches no \
                      file.\n\nFix: check the pattern and that the files exist; a \
                      relative pattern resolves against the including file's \
                      directory.",
    },
    OtherCode {
        code: "E0006",
        group: Group::Load,
        error: true,
        title: "Include pattern is invalid",
        explanation: "A glob `include` pattern could not be expanded (malformed glob \
                      syntax, or a directory that cannot be read while expanding \
                      it).\n\nFix: correct the pattern; the message carries the \
                      underlying error.",
    },
    OtherCode {
        code: "E0007",
        group: Group::Load,
        error: true,
        title: "Too many included files",
        explanation: "The include tree loads more files than the loader's limit, a guard \
                      against runaway globs and include bombs.\n\nFix: narrow the glob \
                      patterns, or merge small files.",
    },
    OtherCode {
        code: "LOAD",
        group: Group::Load,
        error: true,
        title: "Ledger could not be loaded",
        explanation: "A loading failure (an unreadable file, an include cycle, ...) as \
                      reported by a surface that receives it as one processing error \
                      rather than under its own `E0xxx` code (the LSP, WASM, the FFI). \
                      `rledger check` reports the same failures under their `E0xxx` \
                      codes.\n\nFix: read the message; `rledger check FILE` shows the \
                      specific code.",
    },
    // === Parser (P codes: `P{ParseError::kind_code:04}`) ===
    OtherCode {
        code: "P0001",
        group: Group::Parse,
        error: true,
        title: "Unexpected character",
        explanation: "The lexer met a character that cannot start any token at that \
                      point (a stray symbol, or a lowercase letter where an account or \
                      currency belongs).\n\nFix: remove or correct the character the \
                      message names.",
    },
    OtherCode {
        code: "P0002",
        group: Group::Parse,
        error: true,
        title: "Unexpected end of file",
        explanation: "The file ends in the middle of a directive (an unterminated \
                      string, a posting cut short).\n\nFix: complete the last directive.",
    },
    OtherCode {
        code: "P0003",
        group: Group::Parse,
        error: true,
        title: "Expected a different token",
        explanation: "The parser expected one kind of token (named in the message) and \
                      found another.\n\nFix: compare the line with the directive's \
                      syntax in the syntax reference.",
    },
    OtherCode {
        code: "P0004",
        group: Group::Parse,
        error: true,
        title: "Invalid date",
        explanation: "A date is not written as `YYYY-MM-DD` (or `YYYY/MM/DD`).\n\nFix: \
                      write the date with a four-digit year and two-digit month and \
                      day.",
    },
    OtherCode {
        code: "P0005",
        group: Group::Parse,
        error: true,
        title: "Invalid number",
        explanation: "A number cannot be read (misplaced commas, several decimal \
                      points, a value out of range).\n\nFix: write plain decimals such \
                      as `-1234.56`.",
    },
    OtherCode {
        code: "P0006",
        group: Group::Parse,
        error: true,
        title: "Invalid account",
        explanation: "An account name is malformed: each colon-separated component must \
                      start with an uppercase letter or a digit \
                      (`Assets:Bank:Checking`).\n\nFix: capitalize the components.",
    },
    OtherCode {
        code: "P0007",
        group: Group::Parse,
        error: true,
        title: "Invalid currency",
        explanation: "A currency (commodity) name is malformed. Currencies are uppercase, \
                      start with a letter, and may contain digits and `'._-` inside \
                      (`USD`, `VTI`, `BRK.B`).\n\nFix: write the currency in uppercase.",
    },
    OtherCode {
        code: "P0008",
        group: Group::Parse,
        error: true,
        title: "Unclosed string",
        explanation: "A string literal has no closing double quote.\n\nFix: add the \
                      closing `\"`. Strings use double quotes only; single quotes are \
                      not string delimiters.",
    },
    OtherCode {
        code: "P0009",
        group: Group::Parse,
        error: true,
        title: "Invalid escape sequence",
        explanation: "A string contains a backslash escape the parser does not \
                      recognize.\n\nFix: write `\\\\` for a literal backslash and `\\\"` \
                      for a double quote.",
    },
    OtherCode {
        code: "P0010",
        group: Group::Parse,
        error: true,
        title: "Missing required field",
        explanation: "A directive lacks a field its syntax requires (named in the \
                      message).\n\nFix: complete the directive per the syntax \
                      reference.",
    },
    OtherCode {
        code: "P0011",
        group: Group::Parse,
        error: true,
        title: "Indentation error",
        explanation: "A line is indented where no directive can continue, or a posting \
                      or metadata line is not indented under its directive.\n\nFix: \
                      indent postings and metadata (two spaces is conventional) and \
                      start every directive in column one.",
    },
    OtherCode {
        code: "P0012",
        group: Group::Parse,
        error: true,
        title: "Syntax error",
        explanation: "The line is not valid Beancount at the point the message names. \
                      Common causes: a transaction without a flag (`2024-01-12 \"Lunch\"` \
                      needs `*`, `!` or `txn`), an unindented posting, single-quoted \
                      strings, a lowercase currency.\n\nFix: correct the line. One bad \
                      line can hide errors after it, so fix parse errors first.",
    },
    OtherCode {
        code: "P0013",
        group: Group::Parse,
        error: true,
        title: "Missing final newline",
        explanation: "The last line of the file is not terminated in a way the parser \
                      accepts.\n\nFix: end the file with a newline.",
    },
    OtherCode {
        code: "P0014",
        group: Group::Parse,
        error: true,
        title: "Expected an account name",
        explanation: "A directive that takes an account (`open`, `close`, `balance`, \
                      `pad`, `note`, `document`, a posting) has none where one \
                      belongs.\n\nFix: write the account.",
    },
    OtherCode {
        code: "P0015",
        group: Group::Parse,
        error: true,
        title: "Invalid date value",
        explanation: "A date has the right shape but is not a calendar date (month 13, \
                      February 30).\n\nFix: correct the date.",
    },
    OtherCode {
        code: "P0016",
        group: Group::Parse,
        error: true,
        title: "Expected an amount",
        explanation: "A directive that takes an amount (`balance`, `price`) has none \
                      where one belongs.\n\nFix: write the number and currency.",
    },
    OtherCode {
        code: "P0017",
        group: Group::Parse,
        error: true,
        title: "Expected a currency after a number",
        explanation: "A number is not followed by its currency where the syntax requires \
                      one.\n\nFix: write the currency after the number (`10.00 USD`).",
    },
    OtherCode {
        code: "P0018",
        group: Group::Parse,
        error: true,
        title: "Invalid account format",
        explanation: "An account name has no `:`: every account is a root plus at least \
                      one component (`Assets:Cash`, not `Cash`).\n\nFix: write the full \
                      account name.",
    },
    OtherCode {
        code: "P0019",
        group: Group::Parse,
        error: true,
        title: "Expected a directive after the date",
        explanation: "A line starts with a date but no directive keyword or transaction \
                      flag follows it.\n\nFix: add the keyword (`open`, `balance`, ...) \
                      or the transaction flag (`*`, `!`, `txn`).",
    },
    OtherCode {
        code: "P0020",
        group: Group::Parse,
        error: true,
        title: "poptag of a tag never pushed",
        explanation: "A `poptag #x` has no matching earlier `pushtag #x`.\n\nFix: remove \
                      the `poptag`, or add the `pushtag`.",
    },
    OtherCode {
        code: "P0021",
        group: Group::Parse,
        error: true,
        title: "pushtag never popped",
        explanation: "A `pushtag #x` has no `poptag #x` before the end of its \
                      file.\n\nFix: add the `poptag` where the tagged block ends.",
    },
    OtherCode {
        code: "P0022",
        group: Group::Parse,
        error: true,
        title: "popmeta of a key never pushed",
        explanation: "A `popmeta key:` has no matching earlier `pushmeta key:`.\n\nFix: \
                      remove the `popmeta`, or add the `pushmeta`.",
    },
    OtherCode {
        code: "P0023",
        group: Group::Parse,
        error: true,
        title: "pushmeta never popped",
        explanation: "A `pushmeta key: value` has no `popmeta key:` before the end of its \
                      file.\n\nFix: add the `popmeta` where the block ends.",
    },
    OtherCode {
        code: "P0024",
        group: Group::Parse,
        error: true,
        title: "Deprecated pipe symbol",
        explanation: "A transaction header separates payee and narration with `|`, which \
                      beancount deprecated.\n\nFix: write the payee and narration as two \
                      strings (`* \"Payee\" \"Narration\"`), or set \
                      `option \"allow_pipe_separator\" \"TRUE\"`.",
    },
    OtherCode {
        code: "P0025",
        group: Group::Parse,
        error: true,
        title: "Invalid booking method",
        explanation: "An `open` directive's booking method is not one of FIFO, STRICT, \
                      STRICT_WITH_SIZE, LIFO, HIFO, NONE, AVERAGE. Methods are \
                      case-sensitive.\n\nFix: write the method in uppercase, e.g. \
                      `2024-01-01 open Assets:Broker \"FIFO\"`.",
    },
    OtherCode {
        code: "P0026",
        group: Group::Parse,
        error: true,
        title: "Byte-order mark inside the file",
        explanation: "A UTF-8 byte-order mark appears in the middle of the file, usually \
                      from concatenating two files that each start with one. Only a \
                      leading BOM is allowed.\n\nFix: delete the stray BOM (invisible in \
                      most editors; `sed -i 's/\\xEF\\xBB\\xBF//g' FILE` strips them \
                      all).",
    },
    // === Options the validator's ErrorCode does not carry ===
    OtherCode {
        code: "E7004",
        group: Group::Validation,
        error: true,
        title: "Deprecated option",
        explanation: "An `option` is deprecated; the message names what replaces \
                      it.\n\nFix: use the replacement the message names, or remove the \
                      option.",
    },
    OtherCode {
        code: "E7005",
        group: Group::Validation,
        error: true,
        title: "Option may not be set",
        explanation: "A read-only option was set: `filename`, or `plugin` \
                      (`option \"plugin\" \"...\"`), as in beancount. The value is not \
                      applied.\n\nFix: load a plugin with the `plugin` directive: \
                      `plugin \"module.name\"`.",
    },
    OtherCode {
        code: "E7006",
        group: Group::Validation,
        error: true,
        title: "Documents directory does not exist",
        explanation: "An `option \"documents\"` names a directory that does not exist. A \
                      relative path resolves against the directory of the top-level \
                      ledger.\n\nFix: create the directory or correct the path.",
    },
    OtherCode {
        code: "E7008",
        group: Group::Validation,
        error: true,
        title: "Invalid account type name",
        explanation: "A `name_*` option (`name_assets`, `name_equity`, ...) is not a valid \
                      account root: empty, lowercase, containing `:`, or containing a \
                      character other than letters, digits and `-`. The value is not \
                      applied; the root keeps its previous value.\n\nFix: write a root \
                      that starts with an uppercase letter, e.g. \
                      `option \"name_equity\" \"Capital\"`.",
    },
    OtherCode {
        code: "E7009",
        group: Group::Validation,
        error: false,
        title: "Option in an included file is ignored",
        explanation: "An option was set in an `include`d file rather than the top-level \
                      ledger. Most options are taken from the top-level file only, so \
                      the included value has no effect (`operating_currency`, \
                      `display_precision` and `insert_pythonpath` still aggregate).\n\n\
                      Fix: move the option to the top-level ledger if it should govern, \
                      or remove it.",
    },
    OtherCode {
        code: "E7010",
        group: Group::Validation,
        error: false,
        title: "Account option written as a full name",
        explanation: "An account-name option (`account_previous_*`, `account_current_*`) \
                      starts with a root name, e.g. `\"Equity:Opening-Balances\"`. These \
                      options are leaf names under the equity root, so this names \
                      `Equity:Equity:Opening-Balances`, in rledger and beancount \
                      alike.\n\nFix: drop the root: \
                      `option \"account_previous_balances\" \"Opening-Balances\"`.",
    },
    OtherCode {
        code: "E7011",
        group: Group::Validation,
        error: false,
        title: "Unrecognized boolean option value",
        explanation: "A boolean option's value is not a word beancount recognizes, so it \
                      reads as false, as in beancount (which reports nothing). \
                      `infer_tolerance_from_cost` takes `1`/`true`/`on`; the other \
                      boolean options take `1`/`true`/`yes`. Case does not matter.\n\n\
                      Fix: write `TRUE` or `FALSE`.",
    },
    OtherCode {
        code: "BOOK",
        group: Group::Validation,
        error: true,
        title: "Booking or interpolation failed",
        explanation: "A transaction could not be booked and no E4xxx code describes the \
                      failure: most often a posting amount that cannot be inferred \
                      (`interpolation failed: cannot infer currency`, a number written \
                      without its currency), or a per-unit cost too small to \
                      represent.\n\nFix: write the currency (`12.50 USD`); a posting \
                      with a cost or price can only take its commodity from the \
                      account.",
    },
    // === Plugins (E8xxx and PLUGIN) ===
    OtherCode {
        code: "E8001",
        group: Group::Plugin,
        error: true,
        title: "Plugin not found",
        explanation: "A `plugin` name matches no built-in, WASM, or resolvable Python \
                      plugin.\n\nFix: check the name against the plugins reference.",
    },
    OtherCode {
        code: "E8002",
        group: Group::Plugin,
        error: true,
        title: "Python plugin failed",
        explanation: "A Python plugin was found but failed to load or run (it raised, or \
                      its runtime could not start). The message carries the underlying \
                      error.\n\nFix: read the embedded error. Python plugins run \
                      sandboxed and must be self-contained: they cannot import from \
                      your virtualenv.",
    },
    OtherCode {
        code: "E8004",
        group: Group::Plugin,
        error: true,
        title: "Python plugin referenced by module name",
        explanation: "A custom Python plugin is referenced by module name \
                      (`plugin \"mypackage.mymodule\"`). rledger does not search the \
                      Python path, so only file-path references load.\n\nFix: reference \
                      the `.py` file: `plugin \"/abs/path/to/mymodule.py\"`.",
    },
    OtherCode {
        code: "E8005",
        group: Group::Plugin,
        error: true,
        title: "Python plugin needs the plugin runtime",
        explanation: "A Python plugin is referenced in a build without the plugin \
                      runtimes (release binaries are built that way).\n\nFix: install \
                      with `cargo install rustledger`, which includes the Python and \
                      WASM runtimes, or use a built-in native plugin.",
    },
    OtherCode {
        code: "PLUGIN",
        group: Group::Plugin,
        error: true,
        title: "Plugin error",
        explanation: "A plugin reported an error, failed, or returned an entry that is \
                      not valid (its changes are then discarded). Also used for a WASM \
                      plugin in a build without the WASM runtime, and for a plugin path \
                      outside the ledger directory. A plugin's own diagnostics may be \
                      warnings.\n\nFix: read the message, which names the plugin; for a \
                      built-in plugin, see the plugins reference for what it checks.",
    },
];

/// One code as `explain` shows it.
struct Entry {
    code: &'static str,
    group: Group,
    error: bool,
    title: &'static str,
    explanation: &'static str,
    /// A second meaning of the same code (`E8001`), from [`OTHER`].
    also: Option<&'static OtherCode>,
}

impl Entry {
    /// The severity `check` reports the code with. An option code goes
    /// through the loader's rule, which is what `check` applies to it: the
    /// validator's `ErrorCode::DuplicateOption` says error, but `check`
    /// reports E7003 as a warning.
    fn severity(&self) -> &'static str {
        let error = if OptionWarning::ALL_CODES.contains(&self.code) {
            OptionWarning::is_error_code(self.code)
        } else {
            self.error
        };
        if error { "error" } else { "warning" }
    }
}

/// Every code `explain` knows, in listing order.
fn entries() -> Vec<Entry> {
    let mut all: Vec<Entry> = ErrorCode::ALL
        .iter()
        .map(|ec| Entry {
            code: ec.code(),
            group: Group::Validation,
            error: matches!(ec.severity(), Severity::Error),
            title: ec.title(),
            explanation: ec.explanation(),
            also: OTHER.iter().find(|o| o.code == ec.code()),
        })
        .collect();
    for other in OTHER {
        if all.iter().any(|e| e.code == other.code) {
            continue;
        }
        all.push(Entry {
            code: other.code,
            group: other.group,
            error: other.error,
            title: other.title,
            explanation: other.explanation,
            also: None,
        });
    }
    // Stable: within a group, the validator's order, then the table's.
    all.sort_by_key(|e| Group::ALL.iter().position(|g| *g == e.group));
    all
}

/// Every code `explain` knows (the drift guard reads this).
#[must_use]
pub fn known_codes() -> Vec<&'static str> {
    entries().into_iter().map(|e| e.code).collect()
}

/// Find a code in any spelling: `E2001`, `e2001`, `2001` (read as an `E`
/// code), `p0012`, `book`.
fn lookup(raw: &str) -> Option<Entry> {
    let raw = raw.trim().to_ascii_uppercase();
    let wanted = if !raw.is_empty() && raw.bytes().all(|b| b.is_ascii_digit()) {
        format!("E{raw}")
    } else {
        raw
    };
    entries().into_iter().find(|e| e.code == wanted)
}

/// Run `rledger explain`.
///
/// # Errors
///
/// Returns an error if writing to stdout fails.
pub fn run(args: &Args) -> Result<ExitCode> {
    let status = run_with_writer(args, &mut std::io::stdout().lock())?;
    Ok(ExitCode::from(status))
}

/// [`run`], writing to `out` and returning the process status as a plain
/// `u8` (0 = success) so tests can assert on it (`std::process::ExitCode`
/// has no `PartialEq`).
///
/// # Errors
///
/// Returns an error if writing to `out` fails.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<u8> {
    match &args.code {
        None => {
            writeln!(out, "Diagnostic codes (rledger explain <CODE>):")?;
            let all = entries();
            for group in Group::ALL {
                writeln!(out, "\n{}:", group.heading())?;
                for e in all.iter().filter(|e| e.group == group) {
                    let title = match e.also {
                        Some(also) => format!("{}; also: {}", e.title, also.title),
                        None => e.title.to_string(),
                    };
                    writeln!(
                        out,
                        "  {:<7} {:<9} {}",
                        e.code,
                        format!("[{}]", e.severity()),
                        title
                    )?;
                }
            }
            Ok(0)
        }
        Some(raw) => {
            if let Some(e) = lookup(raw) {
                writeln!(out, "{}: {}", e.code, e.title)?;
                writeln!(out, "severity: {}\n", e.severity())?;
                writeln!(out, "{}", e.explanation)?;
                if let Some(also) = e.also {
                    writeln!(out, "\nThe same code is also used for: {}\n", also.title)?;
                    writeln!(out, "{}", also.explanation)?;
                }
                Ok(0)
            } else {
                // The argument is echoed on a terminal: escaped, so one
                // carrying an escape sequence cannot act on it (#2714).
                writeln!(
                    out,
                    "unknown code `{}` — run `rledger explain` to list all codes",
                    rustledger_plugin::escape_untrusted_line(raw)
                )?;
                Ok(1)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn output(args: &Args) -> (String, u8) {
        let mut buf = Vec::new();
        let status = run_with_writer(args, &mut buf).expect("write to Vec cannot fail");
        (String::from_utf8(buf).expect("output is UTF-8"), status)
    }

    fn explain(code: &str) -> (String, u8) {
        output(&Args {
            code: Some(code.to_string()),
        })
    }

    #[test]
    fn test_run_with_writer_known_code_in_any_spelling() {
        for spelling in ["E2001", "e2001", "2001", " E2001 "] {
            let (text, status) = explain(spelling);
            assert_eq!(status, 0, "spelling {spelling:?}");
            assert!(text.contains("E2001: Balance assertion failed"));
            assert!(text.contains("Fix:"), "explanation has a fix section");
        }
    }

    #[test]
    fn test_run_with_writer_parse_option_and_load_codes() {
        for (spelling, heading) in [
            ("P0012", "P0012: Syntax error"),
            ("p0012", "P0012: Syntax error"),
            ("E7011", "E7011: Unrecognized boolean option value"),
            ("0001", "E0001: File cannot be read"),
            ("book", "BOOK: Booking or interpolation failed"),
        ] {
            let (text, status) = explain(spelling);
            assert_eq!(status, 0, "{spelling}: {text}");
            assert!(text.contains(heading), "{spelling}: {text}");
            assert!(text.contains("Fix:"), "{spelling}: {text}");
        }
    }

    #[test]
    fn test_run_with_writer_option_severity_follows_the_loader() {
        // E7003 is a warning in `check` (last value wins), whatever the
        // validator's ErrorCode says.
        for (code, severity) in [
            ("E7003", "severity: warning"),
            ("E7011", "severity: warning"),
            ("E7001", "severity: error"),
        ] {
            let (text, _) = explain(code);
            assert!(text.contains(severity), "{code}: {text}");
        }
    }

    #[test]
    fn test_run_with_writer_shared_code_shows_both_meanings() {
        let (text, status) = explain("E8001");
        assert_eq!(status, 0);
        assert!(text.contains("Document file not found"), "{text}");
        assert!(text.contains("Plugin not found"), "{text}");
    }

    #[test]
    fn test_run_with_writer_lists_every_code_without_an_argument() {
        let (text, status) = output(&Args { code: None });
        assert_eq!(status, 0);
        for code in known_codes() {
            assert!(text.contains(code), "listing includes {code}");
        }
    }

    #[test]
    fn test_run_with_writer_unknown_code_exits_nonzero_with_pointer() {
        let (text, status) = explain("E9999");
        assert_eq!(status, 1);
        assert!(text.contains("unknown code"));
        assert!(text.contains("rledger explain"));
    }

    #[test]
    fn test_entries_every_code_is_unique_and_explained() {
        let mut seen = std::collections::HashSet::new();
        for e in entries() {
            assert!(seen.insert(e.code), "{} listed twice", e.code);
            assert!(!e.title.is_empty());
            assert!(
                e.explanation.len() > 40,
                "{} explanation should be substantive",
                e.code
            );
            assert_eq!(lookup(e.code).map(|f| f.code), Some(e.code));
        }
        for other in OTHER {
            assert!(other.explanation.contains("Fix:"), "{}", other.code);
        }
        for ec in ErrorCode::ALL {
            assert_eq!(ErrorCode::from_code(ec.code()), Some(*ec));
        }
    }

    #[test]
    fn test_other_option_codes_match_the_loader_severity() {
        for other in OTHER {
            if OptionWarning::ALL_CODES.contains(&other.code) {
                assert_eq!(
                    other.error,
                    OptionWarning::is_error_code(other.code),
                    "{}: table severity disagrees with the loader",
                    other.code
                );
            }
        }
    }
}
