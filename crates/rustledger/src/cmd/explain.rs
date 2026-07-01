//! `rledger explain` — describe a validation error code, `rustc --explain`
//! style.
//!
//! `rledger explain E2001` prints what the code means, its common cause, and
//! how to fix it; bare `rledger explain` lists every code with its title. The
//! text lives on [`ErrorCode`] itself (`title`/`explanation`), so the binary
//! is self-contained and the exhaustive match keeps it in lockstep with the
//! enum.

use std::process::ExitCode;

use anyhow::Result;
use clap::Parser;
use rustledger_validate::ErrorCode;

/// Arguments for `rledger explain`.
#[derive(Debug, Parser)]
pub struct Args {
    /// The error code to explain (e.g. `E2001`, `e2001`, or `2001`).
    /// Omit to list all codes.
    pub code: Option<String>,
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
            writeln!(out, "Validation error codes (rledger explain <CODE>):\n")?;
            for code in ErrorCode::ALL {
                writeln!(
                    out,
                    "  {:<7} {:<9} {}",
                    code.code(),
                    format!("[{:?}]", code.severity()).to_lowercase(),
                    code.title()
                )?;
            }
            Ok(0)
        }
        Some(raw) => {
            if let Some(code) = ErrorCode::from_code(raw) {
                writeln!(out, "{}: {}", code.code(), code.title())?;
                writeln!(out, "severity: {:?}\n", code.severity())?;
                writeln!(out, "{}", code.explanation())?;
                Ok(0)
            } else {
                writeln!(
                    out,
                    "unknown error code `{raw}` — run `rledger explain` to list all codes"
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

    #[test]
    fn explains_a_known_code_in_any_spelling() {
        for spelling in ["E2001", "e2001", "2001", " E2001 "] {
            let (text, status) = output(&Args {
                code: Some(spelling.to_string()),
            });
            assert_eq!(status, 0, "spelling {spelling:?}");
            assert!(text.contains("E2001: Balance assertion failed"));
            assert!(text.contains("Fix:"), "explanation has a fix section");
        }
    }

    #[test]
    fn lists_every_code_without_an_argument() {
        let (text, status) = output(&Args { code: None });
        assert_eq!(status, 0);
        for ec in ErrorCode::ALL {
            assert!(text.contains(ec.code()), "listing includes {}", ec.code());
        }
    }

    #[test]
    fn unknown_code_exits_nonzero_with_pointer() {
        let (text, status) = output(&Args {
            code: Some("E9999".to_string()),
        });
        assert_eq!(status, 1);
        assert!(text.contains("unknown error code"));
        assert!(text.contains("rledger explain"));
    }

    #[test]
    fn every_code_roundtrips_and_has_title_and_explanation() {
        for ec in ErrorCode::ALL {
            assert_eq!(
                ErrorCode::from_code(ec.code()),
                Some(*ec),
                "{} must parse back to its variant",
                ec.code()
            );
            assert!(!ec.title().is_empty());
            assert!(
                ec.explanation().len() > 40,
                "{} explanation should be substantive",
                ec.code()
            );
        }
    }
}
