//! Pager support for long output.
//!
//! Pipes output through a pager program (like `less`) when stdout is a TTY.
//! Respects `$PAGER` environment variable and config `output.pager` setting.

use std::io::{self, IsTerminal, Write};
use std::process::{Child, Command, Stdio};

/// A writer that pipes to a pager process, or falls back to stdout.
pub enum PagerWriter {
    /// Output piped to a pager process.
    Pager {
        /// The pager child process.
        child: Child,
        /// Stdin pipe to the pager (`None` after `finish()` is called).
        stdin: Option<std::process::ChildStdin>,
    },
    /// Direct stdout (no pager).
    Stdout(
        /// Locked stdout handle.
        io::StdoutLock<'static>,
    ),
}

impl Write for PagerWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Pager { stdin: Some(s), .. } => match s.write(buf) {
                Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Ok(0),
                other => other,
            },
            Self::Pager { stdin: None, .. } => Ok(0), // Already finished
            Self::Stdout(out) => out.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Pager { stdin: Some(s), .. } => s.flush(),
            Self::Pager { stdin: None, .. } => Ok(()),
            Self::Stdout(out) => out.flush(),
        }
    }
}

impl Drop for PagerWriter {
    fn drop(&mut self) {
        self.finish();
    }
}

impl PagerWriter {
    /// Close the pipe and wait for the pager process to exit.
    pub fn finish(&mut self) {
        if let Self::Pager { stdin, child } = self {
            // Drop stdin to send EOF to the pager
            *stdin = None;
            // Wait for pager to exit
            let _ = child.wait();
        }
    }
}

/// Check if an error is a broken pipe (user quit the pager early).
///
/// This should be silently ignored, matching git behavior.
pub fn is_broken_pipe(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        cause
            .downcast_ref::<io::Error>()
            .is_some_and(|e| e.kind() == io::ErrorKind::BrokenPipe)
    })
}

/// Create a pager writer.
///
/// Returns a pager process if:
/// - stdout is a TTY
/// - `NO_PAGER` env var is not set
/// - A pager command is available (config → `$PAGER` → `less`)
/// - The pager process starts successfully
///
/// Falls back to stdout otherwise.
pub fn create_pager(config_pager: Option<&str>) -> PagerWriter {
    create_pager_in(&PagerEnv::from_process(), config_pager)
}

/// The process-environment inputs to the paging decision, separated from
/// [`create_pager`] so the decision is TESTABLE: the old tests asserted the
/// non-TTY branch by ASSUMING test stdout is never a terminal, which is
/// false under `cargo test` in a real terminal (libtest captures the
/// thread-local print handles, not fd 1) — the tests then failed AND
/// actually spawned `less` on the developer's machine (#1729). Tests now
/// construct this struct directly and never consult (or mutate — parallel
/// tests race on `set_var`) the real environment.
struct PagerEnv {
    /// Whether fd 1 is a terminal (`io::stdout().is_terminal()`).
    is_tty: bool,
    /// Whether `NO_PAGER` is set.
    no_pager: bool,
    /// `$PAGER`, if set.
    pager: Option<String>,
}

impl PagerEnv {
    fn from_process() -> Self {
        Self {
            is_tty: io::stdout().is_terminal(),
            no_pager: std::env::var_os("NO_PAGER").is_some(),
            pager: std::env::var("PAGER").ok(),
        }
    }
}

fn create_pager_in(env: &PagerEnv, config_pager: Option<&str>) -> PagerWriter {
    // Don't page if stdout is not a TTY (piped, redirected, etc.)
    if !env.is_tty {
        return PagerWriter::Stdout(io::stdout().lock());
    }

    // Check NO_PAGER env var
    if env.no_pager {
        return PagerWriter::Stdout(io::stdout().lock());
    }

    // Resolve pager command: config → $PAGER → "less"
    let pager_cmd = config_pager
        .map(String::from)
        .or_else(|| env.pager.clone())
        .unwrap_or_else(|| "less".to_string());

    if pager_cmd.is_empty() {
        return PagerWriter::Stdout(io::stdout().lock());
    }

    // Parse command and args (handles quoted arguments like "less --prompt 'foo bar'")
    let parts = match shell_words::split(&pager_cmd) {
        Ok(parts) if !parts.is_empty() => parts,
        _ => return PagerWriter::Stdout(io::stdout().lock()),
    };
    let (program, args) = (parts[0].as_str(), &parts[1..]);

    // Start the pager process
    // Set LESS=FRX if not already set (matching git behavior):
    //   F = exit if output fits one screen
    //   R = allow ANSI color codes
    //   X = don't clear screen on exit
    let mut cmd = Command::new(program);
    cmd.args(args).stdin(Stdio::piped());
    if std::env::var_os("LESS").is_none() {
        cmd.env("LESS", "FRX");
    }
    match cmd.spawn() {
        Ok(mut child) => {
            let stdin = child.stdin.take();
            PagerWriter::Pager { child, stdin }
        }
        Err(_) => {
            // Pager not found or failed to start — fall back to stdout
            PagerWriter::Stdout(io::stdout().lock())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_broken_pipe() {
        let err = anyhow::anyhow!(io::Error::new(io::ErrorKind::BrokenPipe, "pipe broke"));
        assert!(is_broken_pipe(&err));
    }

    #[test]
    fn test_is_broken_pipe_nested() {
        let inner = io::Error::new(io::ErrorKind::BrokenPipe, "pipe broke");
        let err = anyhow::anyhow!(inner).context("writing output");
        assert!(is_broken_pipe(&err));
    }

    #[test]
    fn test_is_not_broken_pipe() {
        let err = anyhow::anyhow!("some other error");
        assert!(!is_broken_pipe(&err));

        let err = anyhow::anyhow!(io::Error::new(io::ErrorKind::NotFound, "not found"));
        assert!(!is_broken_pipe(&err));
    }

    /// Hermetic environment for pager-decision tests: every field is
    /// explicit, so outcomes cannot depend on the terminal, `NO_PAGER`,
    /// or `$PAGER` of whoever runs the tests (#1729).
    fn env(is_tty: bool, no_pager: bool, pager: Option<&str>) -> PagerEnv {
        PagerEnv {
            is_tty,
            no_pager,
            pager: pager.map(String::from),
        }
    }

    #[test]
    fn test_create_pager_non_tty() {
        // Non-TTY stdout never pages, with or without config.
        let writer = create_pager_in(&env(false, false, None), None);
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_with_config_non_tty() {
        let writer = create_pager_in(&env(false, false, Some("less")), Some("less -R"));
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_tty_no_pager_wins() {
        // NO_PAGER suppresses paging even on a TTY with a configured pager.
        let writer = create_pager_in(&env(true, true, Some("less")), Some("less -R"));
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_tty_empty_command_falls_back() {
        // An explicitly empty pager command means "don't page".
        let writer = create_pager_in(&env(true, false, None), Some(""));
        assert!(matches!(writer, PagerWriter::Stdout(_)));
        // Same via $PAGER.
        let writer = create_pager_in(&env(true, false, Some("")), None);
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_tty_unparsable_command_falls_back() {
        // shell_words can't split an unterminated quote — fall back, don't panic.
        let writer = create_pager_in(&env(true, false, None), Some("less '"));
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_tty_spawn_failure_falls_back() {
        // A pager binary that doesn't exist must fall back to stdout rather
        // than erroring. (Spawn-SUCCESS on a TTY is deliberately untested:
        // it would launch a real process from the test suite.)
        let writer = create_pager_in(
            &env(true, false, None),
            Some("/nonexistent/rledger-test-pager-binary"),
        );
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_pager_writer_stdout_write() {
        // Stdout variant should write successfully
        let mut writer = PagerWriter::Stdout(io::stdout().lock());
        // Writing to stdout in tests works (captured by test harness)
        let result = writer.write(b"test");
        assert!(result.is_ok());
    }
}
