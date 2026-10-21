//! A command's stderr, with its warnings kept as records when the caller
//! wants them.
//!
//! `extract` and `price` write two kinds of thing to stderr: progress
//! ("Using importer 'bank' from ...", "Extracted 12 transactions from ...")
//! and warnings (a skipped duplicate, a currency the account's `open` does
//! not allow, a price that failed to fetch). On a terminal both are lines.
//! An agent needs the warnings as data: `ag-rledger` used to hand them over
//! as prose in `result.stderr`, to be parsed back apart (#2566).
//!
//! [`Messages`] is the stderr writer plus an optional
//! [`Diagnostics`] sink. Progress is written with `write!`, as before.
//! Warnings go through [`Messages::warn`] or [`Messages::emit_as`]: with no
//! sink they are written as exactly the line `rledger` has always printed, so
//! its output is unchanged byte for byte; with one they become a
//! [`Diagnostic`] with a stable code, in the shape `query` and `report` use.

use crate::cmd::report_cmd::{Diagnostic, Diagnostics};
use std::fmt::Display;
use std::io;

/// A command's stderr, and where its warnings go. See the module docs.
pub struct Messages<'a> {
    err: &'a mut dyn io::Write,
    warnings: Option<&'a mut dyn Diagnostics>,
}

impl<'a> Messages<'a> {
    /// Progress to `err`; warnings to `warnings` when given, else to `err`
    /// as the lines `rledger` prints.
    pub fn new<'e: 'a, 'w: 'a>(
        err: &'a mut (dyn io::Write + 'e),
        warnings: Option<&'a mut (dyn Diagnostics + 'w)>,
    ) -> Self {
        Self {
            err,
            warnings: warnings.map(|w| w as &'a mut dyn Diagnostics),
        }
    }

    /// A warning whose terminal form is `warning: <message>`.
    pub fn warn(&mut self, code: &str, message: impl Into<String>) {
        let message = message.into();
        let line = format!("warning: {message}");
        self.emit_as(
            Diagnostic {
                code: Some(code.to_string()),
                ..Diagnostic::message(message)
            },
            line,
        );
    }

    /// A warning recorded as `diagnostic`, whose terminal form is `line`
    /// (for the messages `rledger` prints without a `warning:` prefix).
    pub fn emit_as(&mut self, diagnostic: Diagnostic, line: impl Display) {
        if let Some(sink) = self.warnings.as_deref_mut() {
            sink.emit(diagnostic);
        } else {
            // A failed write of a warning must never cost the reader the
            // command's output.
            //
            // The line can quote text from the ledger or from a network
            // price source (a fetch error's body), and a terminal reads it,
            // so it is escaped (#2538). A recorded diagnostic keeps it as it
            // is.
            let line = line.to_string();
            let _ = writeln!(
                self.err,
                "{}",
                rustledger_plugin::escape_untrusted_text(&line)
            );
        }
    }
}

/// Progress: what is written with `write!` goes to stderr as before.
impl io::Write for Messages<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.err.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.err.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd::report_cmd::CollectedDiagnostics;
    use std::io::Write as _;

    #[test]
    fn without_a_sink_warnings_are_the_terminal_lines() {
        let mut err = Vec::new();
        let mut m = Messages::new(&mut err, None);
        let _ = writeln!(m, "progress");
        m.warn("CODE", "something is off");
        m.emit_as(Diagnostic::message("x"), "  skipped y");
        assert_eq!(
            String::from_utf8(err).unwrap(),
            "progress\nwarning: something is off\n  skipped y\n"
        );
    }

    #[test]
    fn with_a_sink_warnings_are_records_and_progress_stays_on_stderr() {
        let mut err = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        let mut m = Messages::new(&mut err, Some(&mut sink));
        let _ = writeln!(m, "progress");
        m.warn("CODE", "something is off");
        assert_eq!(String::from_utf8(err).unwrap(), "progress\n");
        assert_eq!(
            sink.0,
            vec![Diagnostic {
                code: Some("CODE".to_string()),
                ..Diagnostic::message("something is off")
            }]
        );
    }
}
