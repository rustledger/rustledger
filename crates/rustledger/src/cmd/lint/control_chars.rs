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

use anyhow::{Context, Result};
use clap::Parser;
use rustledger_core::{Directive, MetaValue, Metadata};
use rustledger_loader::Loader;
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;

pub use super::closed_nonempty::OutputFormat;

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
        let mut keys: Vec<&String> = meta.keys().collect();
        // A hash map's order; the report's is stable.
        keys.sort();
        for key in keys {
            if let Some(MetaValue::String(s)) = meta.get(key) {
                self.check(|| format!("{prefix}metadata {key:?}"), s);
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

/// Run the lint, writing its report to stdout.
///
/// # Errors
/// Fails if an input file cannot be read.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = std::io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the lint, writing the text/JSON report to `out`.
///
/// Scans the directives as written (parsed, before plugins and booking), so
/// a finding points at the line to fix.
///
/// # Errors
/// Fails if an input file cannot be read.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    let mut findings = Vec::new();
    for path in &args.files {
        let loaded = Loader::new()
            .load(path)
            .with_context(|| format!("failed to load {}", path.display()))?;
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
    use std::io::Write as _;

    fn lint(content: &str, format: OutputFormat) -> String {
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
        run_with_writer(&args, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
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
