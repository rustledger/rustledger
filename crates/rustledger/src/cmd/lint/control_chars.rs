//! `rledger lint control-chars` — report control characters in the ledger's
//! strings (#2538).
//!
//! A control character in a narration, a payee, a metadata value or a
//! comment is legal: beancount and `bean-check` accept it, so `check` does
//! not flag it (the same reasoning as #1446). But it is rarely meant. It
//! usually arrives from imported bank data or a file included from
//! elsewhere, where part of the text was someone else's to choose, and
//! rustledger's human-readable output shows it escaped (`\u{1b}`) rather
//! than letting it act on a terminal. This lint finds them so they can be
//! cleaned up at the source.
//!
//! Reported: every character [`rustledger_core::format::is_display_unsafe`]
//! names (a C0 control, DEL, a C1 control, a bidirectional override, a Unicode
//! line or paragraph separator), except a tab, a newline, and the carriage
//! return of a `\r\n`, which are ordinary text.
//!
//! Like the other lints, finding something is not a failure: the exit code
//! is `0` either way. A file that cannot be read is an error.
//!
//! A file with load errors is NOT refused: the input is read by
//! [`super::load::load_source`], the lints' shared loader, at the parsed
//! level, load errors and all. A control character is often what broke the
//! parse (a stray one in a narration can end the string early), and the
//! parser recovers enough to find it, so refusing would hide the very
//! finding that explains the error. But the lint warns that the file had
//! load errors and its findings may be incomplete
//! ([`super::load::warn_load_errors`]), so it never prints a clean "no
//! control characters" over a file it only partly read.

use anyhow::Result;
use clap::Parser;
use rustledger_core::{Directive, MetaValue, Metadata};
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;

use super::load::{load_source, warn_load_errors};
use crate::cmd::messages::Messages;
use crate::cmd::report_cmd::Diagnostics;

use super::OutputFormat;

/// Report control characters in the ledger's strings.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Beancount files to scan. At least one is required.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,

    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

/// One string holding a control character.
#[derive(Serialize)]
struct Finding {
    /// Source file of the directive, if known.
    file: Option<String>,
    /// 1-based line of the directive, if known.
    line: Option<usize>,
    /// Which string: `narration`, `payee`, `metadata "memo"`, ...
    field: String,
    /// The string, as it is. JSON escapes it; text output escapes it with
    /// `\u{..}`.
    text: String,
}

/// The JSON report shape.
#[derive(Serialize)]
struct Report {
    findings: Vec<Finding>,
}

/// Whether `text` holds a character this lint reports.
fn has_control(text: &str) -> bool {
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        let ordinary = match c {
            '\t' | '\n' => true,
            '\r' => chars.peek() == Some(&'\n'),
            _ => false,
        };
        if !ordinary && rustledger_core::format::is_display_unsafe(c) {
            return true;
        }
    }
    false
}

/// Collects the findings of one directive.
struct Strings<'a> {
    found: &'a mut Vec<(String, String)>,
}

impl Strings<'_> {
    fn check(&mut self, field: impl FnOnce() -> String, text: &str) {
        if has_control(text) {
            self.found.push((field(), text.to_string()));
        }
    }

    fn meta(&mut self, meta: &Metadata, prefix: &str) {
        let mut entries: Vec<_> = meta.iter().collect();
        // The report names keys in sorted order, not the map's source order.
        entries.sort_by(|a, b| a.0.cmp(b.0));
        for (key, value) in entries {
            if let MetaValue::String(s) = value {
                self.check(|| format!("{prefix}metadata {:?}", key.as_str()), s);
            }
        }
    }

    fn comments(&mut self, comments: &[String], field: &str) {
        for comment in comments {
            self.check(|| field.to_string(), comment);
        }
    }

    fn directive(&mut self, directive: &Directive) {
        match directive {
            Directive::Transaction(txn) => {
                if let Some(payee) = &txn.payee {
                    self.check(|| "payee".to_string(), payee);
                }
                self.check(|| "narration".to_string(), &txn.narration);
                self.meta(&txn.meta, "");
                self.comments(&txn.trailing_comments, "comment");
                for posting in &txn.postings {
                    let prefix = format!("posting {} ", posting.account);
                    self.meta(&posting.meta, &prefix);
                    self.comments(&posting.comments, &format!("{prefix}comment"));
                    self.comments(&posting.trailing_comments, &format!("{prefix}comment"));
                    if let Some(label) = posting.cost.as_deref().and_then(|c| c.label.as_deref()) {
                        self.check(|| format!("{prefix}cost label"), label);
                    }
                }
            }
            Directive::Note(note) => {
                self.check(|| "comment".to_string(), &note.comment);
                self.meta(&note.meta, "");
            }
            Directive::Event(event) => {
                self.check(|| "event type".to_string(), &event.event_type);
                self.check(|| "value".to_string(), &event.value);
                self.meta(&event.meta, "");
            }
            Directive::Document(document) => {
                self.check(|| "path".to_string(), &document.path);
                self.meta(&document.meta, "");
            }
            Directive::Query(query) => {
                self.check(|| "query name".to_string(), &query.name);
                self.check(|| "query".to_string(), &query.query);
                self.meta(&query.meta, "");
            }
            Directive::Custom(custom) => {
                self.check(|| "custom type".to_string(), &custom.custom_type);
                for (i, value) in custom.values.iter().enumerate() {
                    if let MetaValue::String(s) = value {
                        self.check(|| format!("custom value {}", i + 1), s);
                    }
                }
                self.meta(&custom.meta, "");
            }
            Directive::Balance(d) => self.meta(&d.meta, ""),
            Directive::Open(d) => self.meta(&d.meta, ""),
            Directive::Close(d) => self.meta(&d.meta, ""),
            Directive::Commodity(d) => self.meta(&d.meta, ""),
            Directive::Pad(d) => self.meta(&d.meta, ""),
            Directive::Price(d) => self.meta(&d.meta, ""),
        }
    }
}

/// Run the lint, writing its report to stdout and its warnings to stderr.
///
/// # Errors
/// Fails if an input file cannot be read.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(
        args,
        &mut std::io::stdout().lock(),
        None,
        &mut std::io::stderr().lock(),
    )
}

/// Run the lint, writing the text/JSON report to `out`.
///
/// Scans the directives as written (parsed, before plugins and booking), so
/// a finding points at the line to fix. A file with load errors is scanned
/// as far as it parsed, with a warning that says so (see the module docs);
/// warnings go to `warnings` when given, else to `err` as `warning: ...`
/// lines.
///
/// # Errors
/// Fails if an input file cannot be read.
pub fn run_with_writer<W: std::io::Write>(
    args: &Args,
    out: &mut W,
    warnings: Option<&mut dyn Diagnostics>,
    err: &mut dyn std::io::Write,
) -> Result<ExitCode> {
    let messages = &mut Messages::new(err, warnings);
    let mut findings = Vec::new();
    for path in &args.files {
        let loaded = load_source(path)?;
        warn_load_errors(messages, path, &loaded);
        for spanned in &loaded.directives {
            let mut found = Vec::new();
            Strings { found: &mut found }.directive(&spanned.value);
            if found.is_empty() {
                continue;
            }
            let file = loaded.source_map.get(spanned.file_id as usize);
            let line = file.map(|f| f.line_col(spanned.span.start).0);
            let file = file.map(|f| f.path.display().to_string());
            findings.extend(found.into_iter().map(|(field, text)| Finding {
                file: file.clone(),
                line,
                field,
                text,
            }));
        }
    }

    match args.format {
        OutputFormat::Text => {
            if findings.is_empty() {
                writeln!(out, "No control characters in the ledger's strings.")?;
            } else {
                for f in &findings {
                    let loc = match (&f.file, f.line) {
                        (Some(file), Some(line)) => format!("{file}:{line}"),
                        (Some(file), None) => file.clone(),
                        _ => "<unknown>".to_string(),
                    };
                    writeln!(
                        out,
                        "{}: control character in {}: \"{}\"",
                        rustledger_plugin::escape_untrusted_line(&loc),
                        f.field,
                        rustledger_plugin::escape_untrusted_line(&f.text),
                    )?;
                }
                writeln!(
                    out,
                    "\n{} string(s) with control characters.",
                    findings.len()
                )?;
            }
        }
        OutputFormat::Json => {
            let report = Report { findings };
            writeln!(out, "{}", crate::cmd::to_json_pretty(&report)?)?;
        }
    }
    Ok(ExitCode::SUCCESS)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd::report_cmd::{CollectedDiagnostics, Diagnostic};
    use std::io::Write as _;

    /// The report, and the warnings, for `content`.
    fn lint_with_warnings(content: &str, format: OutputFormat) -> (String, Vec<Diagnostic>) {
        let mut file = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        file.write_all(content.as_bytes()).unwrap();
        let args = Args {
            files: vec![file.path().to_path_buf()],
            format,
        };
        let mut buf: Vec<u8> = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        let mut err: Vec<u8> = Vec::new();
        let code = run_with_writer(&args, &mut buf, Some(&mut sink), &mut err).unwrap();
        assert_eq!(code, ExitCode::SUCCESS);
        assert!(err.is_empty(), "{err:?}");
        (String::from_utf8(buf).unwrap(), sink.0)
    }

    /// The report for `content`, which loads without errors.
    fn lint(content: &str, format: OutputFormat) -> String {
        let (out, warnings) = lint_with_warnings(content, format);
        assert!(warnings.is_empty(), "{warnings:?}");
        out
    }

    /// A control character on a line that also has a parse error is still
    /// found, and the load error is a warning, not a refusal.
    #[test]
    fn test_run_with_writer_answers_over_load_errors_with_a_warning() {
        let (out, warnings) = lint_with_warnings(
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-02 * \"bell\u{7}\" junk\n",
                "  Assets:Cash  -1 USD\n",
                "  Expenses:Food\n",
            ),
            OutputFormat::Text,
        );
        // The invalid token after the lone string keeps that string in the
        // payee's place (#2932), so the character is reported in the payee.
        assert!(
            out.contains(":2: control character in payee: \"bell\\u{7}\""),
            "the control character is still found:\n{out}"
        );
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        assert_eq!(
            warnings[0].code.as_deref(),
            Some(super::super::load::LOAD_ERRORS)
        );
        assert!(
            warnings[0]
                .message
                .contains("has load errors, so findings may be incomplete"),
            "{warnings:?}"
        );
    }

    /// With no finding at all, the load errors still say the clean report
    /// is not the whole story.
    #[test]
    fn test_run_with_writer_never_reports_clean_silently_over_load_errors() {
        let (out, warnings) =
            lint_with_warnings("include \"missing-xyz.beancount\"\n", OutputFormat::Json);
        let report: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(report["findings"], serde_json::json!([]));
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        assert_eq!(
            warnings[0].code.as_deref(),
            Some(super::super::load::LOAD_ERRORS)
        );
    }

    /// Without a sink, the warning is a `warning:` line on stderr.
    #[test]
    fn test_run_with_writer_writes_the_load_warning_to_err_without_a_sink() {
        let mut file = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        file.write_all(b"include \"missing-xyz.beancount\"\n")
            .unwrap();
        let args = Args {
            files: vec![file.path().to_path_buf()],
            format: OutputFormat::Text,
        };
        let (mut out, mut err) = (Vec::new(), Vec::new());
        run_with_writer(&args, &mut out, None, &mut err).unwrap();
        let err = String::from_utf8(err).unwrap();
        assert!(
            err.starts_with(&format!(
                "warning: {}: has load errors, so findings may be incomplete: ",
                file.path().display()
            )),
            "{err}"
        );
        assert_eq!(
            String::from_utf8(out).unwrap(),
            "No control characters in the ledger's strings.\n"
        );
    }

    #[test]
    fn reports_control_characters_with_their_field_and_line() {
        let out = lint(
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-02 * \"SHOP\u{1b}]52;c;aGk=\u{7}\" \"lunch\\b\"\n",
                "  memo: \"bidi \u{202e} here\"\n",
                "  Assets:Cash  -1 USD\n",
                "    note: \"del \u{7f}\"\n",
                "  Expenses:Food\n",
                "2024-01-03 note Assets:Cash \"multi\nline\ttab ok\"\n",
            ),
            OutputFormat::Text,
        );
        // Escaped, never raw.
        assert!(
            !out.chars()
                .any(|c| c != '\n' && rustledger_core::format::is_display_unsafe(c)),
            "{out:?}"
        );
        for want in [
            ":2: control character in payee: \"SHOP\\u{1b}]52;c;aGk=\\u{7}\"",
            // `\b` in the source decodes to U+0008 (#2672).
            ":2: control character in narration: \"lunch\\u{8}\"",
            ":2: control character in metadata \"memo\": \"bidi \\u{202e} here\"",
            ":2: control character in posting Assets:Cash metadata \"note\": \"del \\u{7f}\"",
            "4 string(s) with control characters.",
        ] {
            assert!(out.contains(want), "missing {want:?} in:\n{out}");
        }
        // A newline and a tab are ordinary text.
        assert!(!out.contains("comment"), "{out}");
    }

    #[test]
    fn json_keeps_the_text_as_data_and_is_terminal_safe() {
        let out = lint(
            "2024-01-01 open Assets:Cash\n\
             2024-01-02 note Assets:Cash \"a\u{9b}31m b\"\n",
            OutputFormat::Json,
        );
        assert!(!out.contains('\u{9b}'), "{out:?}");
        let report: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(report["findings"][0]["field"], "comment");
        assert_eq!(report["findings"][0]["text"], "a\u{9b}31m b");
        assert_eq!(report["findings"][0]["line"], 2);
    }

    #[test]
    fn a_clean_ledger_reports_nothing() {
        let out = lint(
            "2024-01-01 open Assets:Cash\r\n\
             2024-01-02 note Assets:Cash \"plain ünïcode\"\r\n",
            OutputFormat::Text,
        );
        assert_eq!(out, "No control characters in the ledger's strings.\n");
    }
}
