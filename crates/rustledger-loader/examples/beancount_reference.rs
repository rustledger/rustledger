//! The beancount reference oracle's side of its drift checks: for each input,
//! the tokens and the errors that rledger's model of beancount 3.2.3's parser
//! (`rustledger_parser::cst::__beancount_reference_*`, built from
//! pta-standards' clean-room grammar) predicts, before rledger's deliberate
//! differences are applied. A checker compares them with beancount's own
//! `lex_iter_string` and `parse_string`.
//!
//! Input framing is `parse_error_lines`'s: an id line, a decimal byte-length
//! line, then that many bytes of UTF-8 source. Output, one JSON object per
//! input:
//!
//! ```text
//! {"id":"<id>","tokens":[["<NAME>",<line>,<start>,<end>],...],"errors":[[<line>,"<message>"],...],
//!  "gate_skips_grammar":true,"gated_slots":[[<line>,"lexical"],...]}
//! ```
//!
//! `gate_skips_grammar` says whether rledger's parse skips the oracle on the
//! input (its own parse reports no error); `gated_slots` are then the slots
//! the oracle, with rledger's deliberate differences applied, would have
//! held it to, which the checker requires to hold no syntax error.
//!
//! Run with `cargo run -p rustledger-loader --no-default-features --example
//! beancount_reference`.

use std::io::{self, BufWriter, Read, Write};

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
        let tokens: Vec<serde_json::Value> =
            rustledger_parser::cst::__beancount_reference_tokens(source)
                .into_iter()
                .map(|(name, line, start, end)| serde_json::json!([name, line, start, end]))
                .collect();
        let errors: Vec<serde_json::Value> =
            rustledger_parser::cst::__beancount_reference_errors(source)
                .into_iter()
                .map(|(line, message)| serde_json::json!([line, message]))
                .collect();
        let gated = rustledger_parser::cst::__beancount_gate_skips_grammar(source);
        let overlaid: Vec<serde_json::Value> = if gated {
            rustledger_parser::cst::__beancount_overlaid_slots(source)
                .into_iter()
                .map(|(line, kind)| serde_json::json!([line, kind]))
                .collect()
        } else {
            Vec::new()
        };
        let line = serde_json::json!({
            "id": id,
            "tokens": tokens,
            "errors": errors,
            "gate_skips_grammar": gated,
            "gated_slots": overlaid,
        });
        writeln!(out, "{line}")?;
    }
    out.flush()
}
