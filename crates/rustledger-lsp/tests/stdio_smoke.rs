//! Stdio integration test for the `rledger-lsp` binary.
//!
//! The in-process `lsp_protocol` harness uses `Connection::memory()`,
//! which bypasses the production stdio framing. This binary-level
//! test pipes Content-Length-framed JSON-RPC over stdin/stdout of a
//! spawned `rledger-lsp` process, exercising the path real editors
//! drive:
//!
//! - the `start_stdio` initialize handshake
//! - `Content-Length` header parsing and writing
//! - shutdown + exit notification + process exit code
//!
//! If this test fails, the in-process harness can still be passing —
//! framing or stdio plumbing bugs would otherwise only surface in
//! production. This test is small and slow (it spawns a binary) so
//! it lives separately from the `lsp_protocol` harness.

use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Frame an LSP JSON-RPC body with the spec-required
/// `Content-Length` header.
fn frame(body: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{}", body.len(), body)
}

/// Read framed messages from `r` until `deadline`, returning the
/// concatenated body bytes (un-framed, separated by `\n` for
/// readability).
///
/// Real LSP clients would parse this into typed messages; the test
/// just substring-matches on the wire bytes, which keeps it
/// dependency-light and resilient to lsp-types version changes.
fn read_until<R: Read>(mut r: R, deadline: Instant) -> String {
    let mut buf = Vec::new();
    let mut tmp = [0u8; 4096];
    while Instant::now() < deadline {
        match r.read(&mut tmp) {
            Ok(0) => break, // EOF
            Ok(n) => buf.extend_from_slice(&tmp[..n]),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(_) => break,
        }
        // Heuristic: if we've seen a shutdown response, we have
        // enough to assert on; bail early so the test is fast.
        if String::from_utf8_lossy(&buf).contains("\"id\":2") {
            break;
        }
    }
    String::from_utf8_lossy(&buf).to_string()
}

/// Drive the binary through initialize -> shutdown -> exit and
/// verify the framed responses arrive over stdout.
#[test]
fn rledger_lsp_binary_handles_initialize_shutdown_exit() {
    // `CARGO_BIN_EXE_<name>` is set by cargo for integration tests
    // when the package has a `[[bin]]` target. This avoids hard-coding
    // a path under `target/`.
    let bin = env!("CARGO_BIN_EXE_rledger-lsp");

    let mut child = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn rledger-lsp");

    let mut stdin = child.stdin.take().expect("child stdin");
    let stdout = child.stdout.take().expect("child stdout");

    // initialize (id=1) + initialized + shutdown (id=2) + exit
    let messages = [
        frame(
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":null,"rootUri":null,"capabilities":{}}}"#,
        ),
        frame(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
        frame(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#),
        frame(r#"{"jsonrpc":"2.0","method":"exit","params":null}"#),
    ];
    for msg in &messages {
        stdin.write_all(msg.as_bytes()).expect("write to child");
    }
    stdin.flush().expect("flush child stdin");
    // Deliberately keep `stdin` open until the end of the test:
    // dropping it here races the server's reader thread on CI. If
    // the reader sees EOF before it pulls the buffered `shutdown` +
    // `exit` messages out of the pipe, the server's main loop
    // breaks via channel-close before processing them, and stdout
    // ends after the initialize response only. The explicit `exit`
    // notification we just wrote is the LSP-spec-correct way to
    // terminate the server, and the in-process `process::exit` in
    // `main_loop` ends the child before `wait_or_kill` returns.

    let output = read_until(stdout, Instant::now() + Duration::from_secs(10));
    // Release stdin AFTER reading; the child has already process::exit'd
    // by the time we get here, so close-on-drop just frees the
    // descriptor.
    drop(stdin);
    assert!(
        output.contains("Content-Length:"),
        "expected at least one Content-Length-framed response on stdout; \
         got: {output:?}"
    );
    assert!(
        output.contains("\"id\":1"),
        "expected initialize response with id=1; got: {output:?}"
    );
    assert!(
        output.contains("\"id\":2"),
        "expected shutdown response with id=2; got: {output:?}"
    );

    // The process should exit on its own after `exit`. Give it a
    // generous window; fall back to kill if it hangs (would indicate
    // a stdio-path bug we'd want to surface as a failed test).
    let status = wait_or_kill(&mut child, Duration::from_secs(5));
    assert!(
        status.success(),
        "rledger-lsp exited non-zero after a clean shutdown+exit sequence: {status:?}"
    );
}

/// Wait for the child to exit, killing it if the deadline passes.
/// Returns the final `ExitStatus`.
fn wait_or_kill(child: &mut std::process::Child, max: Duration) -> std::process::ExitStatus {
    let deadline = Instant::now() + max;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return status,
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    return child.wait().expect("wait after kill");
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => panic!("try_wait failed: {e}"),
        }
    }
}
