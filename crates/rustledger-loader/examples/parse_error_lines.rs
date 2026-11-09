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
//! Run with `cargo run -p rustledger-loader --no-default-features --example
//! parse_error_lines`; it needs no plugin runtime.

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

fn main() -> io::Result<()> {
    let mut input = Vec::new();
    io::stdin().read_to_end(&mut input)?;
    let mut out = BufWriter::new(io::stdout());
    let mut rest = &input[..];
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
        let result = rustledger_parser::parse(source);
        let index = LineIndex::new(source);
        let errors: Vec<serde_json::Value> = result
            .errors
            .iter()
            .map(|e| {
                serde_json::json!([
                    index.line_col(e.span.start).0,
                    format!("P{:04}", e.kind_code()),
                    e.message(),
                ])
            })
            .collect();
        let line = serde_json::json!({ "id": id, "errors": errors });
        writeln!(out, "{line}")?;
    }
    out.flush()
}
