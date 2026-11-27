//! rledger's side of the parse-error parity harness
//! (`scripts/compat-parse-error-parity.py`, #2872).
//!
//! Reads framed inputs on stdin and prints, for each, the parse errors
//! `rustledger_parser::parse` reports, one JSON object per line:
//!
//! ```text
//! {"id":"<id>","errors":[[<line>,"P0003","<message>"],...]}
//! ```
//!
//! The line is the one `rledger check` prints for the error: the 1-based line
//! of the span's start, computed by [`LineIndex`], the same lookup
//! `check --format json` uses. Nothing is normalized here; the harness does all
//! of that in one place, for both sides.
//!
//! Input frames: an id line, a decimal byte-length line, then that many bytes
//! of UTF-8 source. Framing (not one file per input) lets the harness feed
//! generated cases without writing them to disk.
//!
//! With `--jsonl` it speaks the JSON-lines protocol of pta-standards'
//! differential tooling (`tooling/differential`, `ptadiff.protocol`)
//! instead, which the parity harness uses: one `{"id": ..., "text": ...}`
//! object per input line, and per input one output line
//!
//! ```text
//! {"id":"<id>","errors":[{"line":<line>,"code":"P0003","msg":"<message>"},...]}
//! ```
//!
//! with the same lines, codes and messages as the framed form.
//!
//! Run with `cargo run -p rustledger-loader --no-default-features --example
//! parse_error_lines [-- --jsonl]`; it needs no plugin runtime.

use std::io::{self, BufWriter, Read, Write};

use rustledger_loader::LineIndex;

fn invalid(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// The next `\n`-terminated header line of `rest`, and what follows it.
fn header(rest: &[u8]) -> io::Result<(&str, &[u8])> {
    let end = rest
        .iter()
        .position(|&b| b == b'\n')
        .ok_or_else(|| invalid("truncated frame header".to_string()))?;
    let line = std::str::from_utf8(&rest[..end])
        .map_err(|e| invalid(format!("frame header is not UTF-8: {e}")))?;
    Ok((line, &rest[end + 1..]))
}

/// The parse errors of `source`, as `(line, code, message)`.
fn parse_errors(source: &str) -> Vec<(usize, String, String)> {
    let result = rustledger_parser::parse(source);
    let index = LineIndex::new(source);
    result
        .errors
        .iter()
        .map(|e| {
            (
                index.line_col(e.span.start).0,
                format!("P{:04}", e.kind_code()),
                e.message(),
            )
        })
        .collect()
}

/// The framed protocol: id line, byte-length line, source bytes.
fn run_framed(input: &[u8], out: &mut impl Write) -> io::Result<()> {
    let mut rest = input;
    while !rest.is_empty() {
        let (id, after_id) = header(rest)?;
        let (len, body) = header(after_id)?;
        let n: usize = len
            .parse()
            .map_err(|e| invalid(format!("frame length {len:?}: {e}")))?;
        if body.len() < n {
            return Err(invalid(format!("input {id:?} is truncated")));
        }
        let source = std::str::from_utf8(&body[..n])
            .map_err(|e| invalid(format!("input {id:?} is not UTF-8: {e}")))?;
        rest = &body[n..];
        let errors: Vec<serde_json::Value> = parse_errors(source)
            .into_iter()
            .map(|(line, code, msg)| serde_json::json!([line, code, msg]))
            .collect();
        writeln!(out, "{}", serde_json::json!({ "id": id, "errors": errors }))?;
    }
    Ok(())
}

/// The JSON-lines protocol: one `{"id", "text"}` object per line.
fn run_jsonl(input: &[u8], out: &mut impl Write) -> io::Result<()> {
    let text =
        std::str::from_utf8(input).map_err(|e| invalid(format!("input is not UTF-8: {e}")))?;
    for (n, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let obj: serde_json::Value = serde_json::from_str(line)
            .map_err(|e| invalid(format!("input line {}: {e}", n + 1)))?;
        let (Some(id), Some(source)) = (obj["id"].as_str(), obj["text"].as_str()) else {
            return Err(invalid(format!(
                "input line {}: expected string `id` and `text`",
                n + 1
            )));
        };
        let errors: Vec<serde_json::Value> = parse_errors(source)
            .into_iter()
            .map(|(line, code, msg)| serde_json::json!({ "line": line, "code": code, "msg": msg }))
            .collect();
        writeln!(out, "{}", serde_json::json!({ "id": id, "errors": errors }))?;
    }
    Ok(())
}

fn main() -> io::Result<()> {
    let jsonl = match std::env::args().nth(1).as_deref() {
        None => false,
        Some("--jsonl") => true,
        Some(other) => return Err(invalid(format!("unknown argument {other:?}"))),
    };
    let mut input = Vec::new();
    io::stdin().read_to_end(&mut input)?;
    let mut out = BufWriter::new(io::stdout());
    if jsonl {
        run_jsonl(&input, &mut out)?;
    } else {
        run_framed(&input, &mut out)?;
    }
    out.flush()
}
