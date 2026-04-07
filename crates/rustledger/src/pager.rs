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
    // Don't page if stdout is not a TTY (piped, redirected, etc.)
    if !io::stdout().is_terminal() {
        return PagerWriter::Stdout(io::stdout().lock());
    }

    // Check NO_PAGER env var
    if std::env::var_os("NO_PAGER").is_some() {
        return PagerWriter::Stdout(io::stdout().lock());
    }

    // Resolve pager command: config → $PAGER → "less"
    let pager_cmd = config_pager
        .map(String::from)
        .or_else(|| std::env::var("PAGER").ok())
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

    #[test]
    fn test_create_pager_non_tty() {
        // In CI/tests, stdout is not a TTY — should always return Stdout variant
        let writer = create_pager(None);
        assert!(matches!(writer, PagerWriter::Stdout(_)));
    }

    #[test]
    fn test_create_pager_with_config_non_tty() {
        // Even with config, non-TTY should return Stdout
        let writer = create_pager(Some("less -R"));
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
