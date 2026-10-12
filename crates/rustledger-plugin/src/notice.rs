//! Messages the plugin and importer runtimes have for the person running
//! them, and where they go.
//!
//! Some things the runtimes have to say are not errors and have no return
//! value to ride on: the one-time `CPython` download and compile, what a
//! Python plugin printed, a WASM plugin that failed to hot-reload, a WASM
//! importer whose `identify` trapped. They used to be written straight to
//! the process's stderr, which is right for a terminal and wrong for a
//! caller that reports in some other way: `ag-rledger` emits one JSON
//! envelope and discards stderr, so an agent never saw them (#2566).
//!
//! Each such message goes through [`emit`]. By default it is written to
//! stderr exactly as before. Inside [`capture`] it is collected instead, as
//! a [`Notice`] with a stable code, for the caller to report.
//!
//! Capture is per THREAD. Every notice is emitted on the thread that called
//! into the runtime (a Python plugin runs on a thread of its own, but its
//! stderr is forwarded after that thread is joined), so wrapping the call
//! is enough, and two captures on two threads — parallel tests — never see
//! each other's notices.

use std::cell::RefCell;
use std::io::Write;

/// The `CPython` runtime's performance notice, shown when it is loaded.
pub const PYTHON_RUNTIME_LOADING: &str = "PYTHON_RUNTIME_LOADING";
/// The one-time `CPython` download and its progress.
pub const PYTHON_RUNTIME_DOWNLOAD: &str = "PYTHON_RUNTIME_DOWNLOAD";
/// Compiling the `CPython` module, or a compiled-module cache that could not
/// be read or written.
pub const PYTHON_RUNTIME_COMPILE: &str = "PYTHON_RUNTIME_COMPILE";
/// What a Python plugin wrote to its stderr (escaped, see
/// [`crate::untrusted`]).
pub const PLUGIN_STDERR: &str = "PLUGIN_STDERR";
/// A watched WASM plugin changed on disk and failed to load; the old one is
/// kept.
pub const PLUGIN_RELOAD_FAILED: &str = "PLUGIN_RELOAD_FAILED";
/// A WASM importer's `identify` failed, so it was treated as not matching.
pub const IMPORTER_IDENTIFY_FAILED: &str = "IMPORTER_IDENTIFY_FAILED";

/// One message from a runtime, as [`capture`] collects it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Notice {
    /// What kind of message this is: one of this module's constants, or a
    /// caller's own code for a message it routes the same way.
    pub code: &'static str,
    /// The message: the text that would have gone to stderr, without its
    /// trailing newlines. Text from a plugin or importer is already escaped.
    pub message: String,
}

thread_local! {
    static CAPTURED: RefCell<Option<Vec<Notice>>> = const { RefCell::new(None) };
}

/// Report `text` under `code`.
///
/// `text` is exactly what goes to stderr when nothing is capturing, trailing
/// newline included, so moving a message here leaves the terminal output
/// byte for byte as it was. Inside [`capture`], it is collected instead, with
/// its trailing newlines removed. A message that is only blank lines is
/// dropped there: it was spacing on the terminal, not something to report.
pub fn emit(code: &'static str, text: &str) {
    let captured = CAPTURED.with(|cell| {
        let mut slot = cell.borrow_mut();
        let Some(notices) = slot.as_mut() else {
            return false;
        };
        let message = text.trim_end_matches(['\n', '\r']);
        if !message.trim().is_empty() {
            notices.push(Notice {
                code,
                message: message.to_string(),
            });
        }
        true
    });
    if !captured {
        // A failed write of a notice must never fail the work it is about.
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(text.as_bytes());
        let _ = err.flush();
    }
}

/// Report a warning under `code`.
///
/// It is `warning: <message>` on stderr, as the terminal has always shown it,
/// or `message` alone inside [`capture`]: the `warning:` is the terminal's
/// severity marker, not part of the message.
pub fn emit_warning(code: &'static str, message: &str) {
    let captured = CAPTURED.with(|cell| {
        let mut slot = cell.borrow_mut();
        let Some(notices) = slot.as_mut() else {
            return false;
        };
        notices.push(Notice {
            code,
            message: message.to_string(),
        });
        true
    });
    if !captured {
        emit(code, &format!("warning: {message}\n"));
    }
}

/// Run `f`, collecting every notice it emits on this thread instead of
/// writing it to stderr.
///
/// Nests: an inner capture collects what is emitted inside it, and the outer
/// one resumes afterwards. The previous state is restored even if `f`
/// panics.
pub fn capture<R>(f: impl FnOnce() -> R) -> (R, Vec<Notice>) {
    /// Puts the enclosing capture's state (or none) back when dropped,
    /// including on a panic out of `f`.
    struct Restore {
        previous: Option<Vec<Notice>>,
    }
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.previous.take();
            CAPTURED.with(|cell| *cell.borrow_mut() = previous);
        }
    }

    let restore = Restore {
        previous: CAPTURED.with(|cell| cell.borrow_mut().replace(Vec::new())),
    };
    let result = f();
    let notices = CAPTURED
        .with(|cell| cell.borrow_mut().take())
        .unwrap_or_default();
    drop(restore);
    (result, notices)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capture_collects_with_trailing_newlines_removed() {
        let ((), notices) = capture(|| {
            emit(PLUGIN_STDERR, "hello\nworld\n");
            emit(PYTHON_RUNTIME_LOADING, "loading\n\n");
        });
        assert_eq!(
            notices,
            vec![
                Notice {
                    code: PLUGIN_STDERR,
                    message: "hello\nworld".to_string(),
                },
                Notice {
                    code: PYTHON_RUNTIME_LOADING,
                    message: "loading".to_string(),
                },
            ]
        );
    }

    #[test]
    fn a_captured_warning_drops_the_terminal_prefix() {
        let ((), notices) = capture(|| emit_warning(PLUGIN_RELOAD_FAILED, "it broke"));
        assert_eq!(
            notices,
            vec![Notice {
                code: PLUGIN_RELOAD_FAILED,
                message: "it broke".to_string(),
            }]
        );
    }

    #[test]
    fn blank_spacing_is_not_a_notice() {
        let ((), notices) = capture(|| emit(PYTHON_RUNTIME_DOWNLOAD, "\n"));
        assert!(notices.is_empty(), "{notices:?}");
    }

    #[test]
    fn captures_nest_and_restore() {
        let ((inner, ()), outer) = capture(|| {
            emit(PLUGIN_STDERR, "outer before\n");
            let ((), inner) = capture(|| emit(PLUGIN_STDERR, "inner\n"));
            emit(PLUGIN_STDERR, "outer after\n");
            (inner, ())
        });
        let messages = |n: &[Notice]| n.iter().map(|n| n.message.clone()).collect::<Vec<_>>();
        assert_eq!(messages(&inner), ["inner"]);
        assert_eq!(messages(&outer), ["outer before", "outer after"]);
        // Nothing is capturing any more.
        assert!(CAPTURED.with(|cell| cell.borrow().is_none()));
    }

    #[test]
    fn a_panic_inside_capture_restores_the_previous_state() {
        let caught = std::panic::catch_unwind(|| {
            capture::<()>(|| panic!("boom"));
        });
        assert!(caught.is_err());
        assert!(CAPTURED.with(|cell| cell.borrow().is_none()));
    }

    #[test]
    fn capture_is_per_thread() {
        let ((), notices) = capture(|| {
            std::thread::spawn(|| {
                // Not captured here: written to this thread's stderr.
                let ((), theirs) = capture(|| emit(PLUGIN_STDERR, "theirs\n"));
                assert_eq!(theirs.len(), 1);
            })
            .join()
            .unwrap();
            emit(PLUGIN_STDERR, "ours\n");
        });
        assert_eq!(notices.len(), 1);
        assert_eq!(notices[0].message, "ours");
    }
}
