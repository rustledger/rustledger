//! Drift guard for [`BcLexer`], the recovery model's port of beancount
//! 3.2.3's lexer: on every pinned input, its tokens must be beancount's own,
//! as `beancount.parser.lexer.lex_iter_string` reports them (called as a
//! black box, through pta-standards' `ptadiff` package, whose forked workers
//! survive beancount's segfaults).
//!
//! Compared per token: beancount's token name and the token's byte span. The
//! recovery model ([`super::recovery`]) predicts which lines beancount
//! reports from these tokens, so a token it reads differently is a wrong
//! prediction waiting for an input to hit it; the parse-error parity harness
//! only sees such a drift once it changes a reported line.
//!
//! `BcLexer` lumps punctuation and the `TRUE` / `FALSE` / `NULL` literals
//! into [`Bc::Other`]; the recovery never needs them apart. Each `Other`
//! token's text names exactly one beancount token (`beancount_name`), so the
//! comparison is as strict as a split class would make it.
//!
//! Inputs: every git-tracked `.beancount` / `.bean` file and the two parser
//! fuzz targets' crash regressions; with `RLEDGER_BC_LEXER_DRIFT_FUZZ_DIR`,
//! the fuzz corpus extracted there (the `fuzz-corpus` commit the parity
//! manifest pins); and, generated on the Python side, the stray-character
//! matrix (`scripts/stray-char-matrix.py`) and ptadiff's generator sample
//! (`GENERATOR_SAMPLE` of `scripts/compat-parse-error-parity.py`).
//!
//! Runs only where Python beancount 3.2.3 and ptadiff are importable
//! (`RLEDGER_BEANCOUNT_PYTHON` names the interpreter, default `python3`;
//! `RLEDGER_PTADIFF` a ptadiff checkout, default the installed package), and
//! skips with a marker otherwise. `RLEDGER_BC_LEXER_DRIFT_REQUIRE=1` (CI's
//! `python-gated-cargo-tests` job) turns every skip into a failure and
//! requires the fuzz corpus.

use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use super::recovery::{Bc, BcLexer, Kw};

/// beancount's name for a token `BcLexer` reads as `t` over `text`.
fn beancount_name(t: Bc, text: &str) -> &'static str {
    match t {
        Bc::Eol => "EOL",
        Bc::Eof => "EOF",
        Bc::Indent => "INDENT",
        Bc::Date => "DATE",
        Bc::Txn => "TXN",
        Bc::Flag => "FLAG",
        Bc::Asterisk => "ASTERISK",
        Bc::Hash => "HASH",
        Bc::Capital => "CAPITAL",
        Bc::Str => "STRING",
        Bc::Account => "ACCOUNT",
        Bc::Currency => "CURRENCY",
        Bc::Number => "NUMBER",
        Bc::Tag => "TAG",
        Bc::Link => "LINK",
        Bc::Key => "KEY",
        Bc::Colon => "COLON",
        Bc::Pipe => "PIPE",
        Bc::Error => "error",
        Bc::Kw(k) => match k {
            Kw::Balance => "BALANCE",
            Kw::Open => "OPEN",
            Kw::Close => "CLOSE",
            Kw::Commodity => "COMMODITY",
            Kw::Pad => "PAD",
            Kw::Event => "EVENT",
            Kw::Price => "PRICE",
            Kw::Note => "NOTE",
            Kw::Document => "DOCUMENT",
            Kw::Query => "QUERY",
            Kw::Custom => "CUSTOM",
            Kw::Pushtag => "PUSHTAG",
            Kw::Poptag => "POPTAG",
            Kw::Pushmeta => "PUSHMETA",
            Kw::Popmeta => "POPMETA",
            Kw::Option => "OPTION",
            Kw::Plugin => "PLUGIN",
            Kw::Include => "INCLUDE",
        },
        Bc::Other => match text {
            "," => "COMMA",
            "~" => "TILDE",
            "+" => "PLUS",
            "-" => "MINUS",
            "/" => "SLASH",
            "(" => "LPAREN",
            ")" => "RPAREN",
            "@@" => "ATAT",
            "@" => "AT",
            "{{" => "LCURLCURL",
            "}}" => "RCURLCURL",
            "{" => "LCURL",
            "}" => "RCURL",
            "TRUE" | "FALSE" => "BOOL",
            "NULL" => "NONE",
            // Unreachable while `Other` covers only the texts above; a new
            // one shows up as a mismatch naming it.
            _ => "OTHER?",
        },
    }
}

/// `(name, start, end)` for each of `BcLexer`'s tokens over `src`, without
/// its end-of-input token (beancount's iterator has none).
fn bc_lexer_tokens(src: &str) -> Vec<(String, usize, usize)> {
    BcLexer::at_line_start(src, 0)
        .filter(|(t, _)| *t != Bc::Eof)
        .map(|(t, r)| {
            (
                beancount_name(t, &src[r.clone()]).to_string(),
                r.start,
                r.end,
            )
        })
        .collect()
}

/// The Python side: reads `{"inputs": [[id, text], ...], "matrix": path,
/// "generators": [...]}` on stdin, adds the matrix and generator inputs, and
/// prints one JSON line per input: `{"id", "text", "tokens": [[name, start,
/// end], ...]}` (byte spans), or `{"id", "text", "crash": why}`.
const PYTHON: &str = r#"
import importlib.util, json, os, sys
# Read the request first, even to skip: the test is still writing it.
req = json.load(sys.stdin)
try:
    import beancount, beancount.parser.lexer
except ImportError as e:
    print("SKIP beancount", e); sys.exit(0)
if beancount.__version__ != "3.2.3":
    print("SKIP beancount version", beancount.__version__); sys.exit(0)
if os.environ.get("RLEDGER_PTADIFF"):
    sys.path.insert(0, os.environ["RLEDGER_PTADIFF"])
try:
    import ptadiff, ptadiff.formats.beancount
except ImportError as e:
    print("SKIP ptadiff", e); sys.exit(0)
items = [tuple(x) for x in req["inputs"]]
spec = importlib.util.spec_from_file_location("matrix", req["matrix"])
matrix = importlib.util.module_from_spec(spec); spec.loader.exec_module(matrix)
for name, base in matrix.BASES:
    for i, src in enumerate(matrix.cases(base)):
        items.append((f"matrix:{name}#{i}", src))
gens = ptadiff.get_format("beancount").generators
for g in req["generators"]:
    name, seed, n = g.split(":")
    for i, src in enumerate(gens[name](int(seed), int(n))):
        items.append((f"gen:{g}#{i}", src))
out = ptadiff.get_format("beancount").oracle(version="3.2.3").lex(items, jobs=os.cpu_count() or 1)
print("OK", len(items))
for item_id, text in items:
    toks = out[item_id]
    if isinstance(toks, ptadiff.Crash):
        print(json.dumps({"id": item_id, "text": text, "crash": toks.why})); continue
    data = text.encode("utf-8")
    starts = [0] + [i + 1 for i, b in enumerate(data) if b == 10]
    pos, spans = 0, []
    for t in toks:
        raw = t.text.encode("utf-8", "surrogateescape")
        # From the start of the token's first line (a comment skipped before
        # it can hold the same text); a token spanning lines (a string)
        # carries its LAST line. An end of line is the next newline.
        first = t.line - raw.count(b"\n")
        line_start = starts[first - 1] if 0 < first <= len(starts) else 0
        at = data.find(raw, pos if t.kind == "EOL" else max(pos, line_start))
        if at < 0:
            spans.append([t.kind, -1, -1]); continue
        spans.append([t.kind, at, at + len(raw)])
        pos = at + len(raw)
    print(json.dumps({"id": item_id, "text": text, "tokens": spans}))
"#;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn required() -> bool {
    std::env::var("RLEDGER_BC_LEXER_DRIFT_REQUIRE").as_deref() == Ok("1")
}

/// Skips with `marker` printed, or fails when skipping is forbidden.
fn skip(marker: &str) {
    assert!(
        !required(),
        "{marker} (RLEDGER_BC_LEXER_DRIFT_REQUIRE=1 forbids skipping)"
    );
    eprintln!("{marker}");
}

/// The UTF-8 files the test reads itself, as `(id, text)`.
fn file_inputs() -> Vec<(String, String)> {
    let root = repo_root();
    let mut out = Vec::new();
    let mut add = |id: String, path: &Path| {
        if let Ok(text) = std::fs::read_to_string(path) {
            out.push((id, text));
        }
    };
    let listed = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["ls-files", "-z", "*.beancount", "*.bean"])
        .output()
        .expect("git ls-files runs");
    assert!(listed.status.success(), "git ls-files failed");
    for rel in String::from_utf8_lossy(&listed.stdout).split('\0') {
        if !rel.is_empty() {
            add(rel.to_string(), &root.join(rel));
        }
    }
    let mut dirs: Vec<(String, PathBuf)> = ["fuzz_parse", "fuzz_green_eq_red"]
        .iter()
        .map(|t| {
            (
                format!("regressions/{t}"),
                root.join("crates/rustledger-parser/fuzz/regressions")
                    .join(t),
            )
        })
        .collect();
    match std::env::var("RLEDGER_BC_LEXER_DRIFT_FUZZ_DIR") {
        Ok(dir) => {
            for t in ["fuzz_parse", "fuzz_green_eq_red"] {
                let d = Path::new(&dir).join(t);
                assert!(d.is_dir(), "{} is missing", d.display());
                dirs.push((format!("fuzz/{t}"), d));
            }
        }
        Err(_) => assert!(
            !required(),
            "RLEDGER_BC_LEXER_DRIFT_REQUIRE=1 needs RLEDGER_BC_LEXER_DRIFT_FUZZ_DIR"
        ),
    }
    for (label, dir) in dirs {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut paths: Vec<PathBuf> = entries.filter_map(|e| Some(e.ok()?.path())).collect();
        paths.sort();
        for p in paths {
            if p.is_file() && p.file_name().is_some_and(|n| n != "README.md") {
                let name = p.file_name().unwrap_or_default().to_string_lossy();
                add(format!("{label}/{name}"), &p);
            }
        }
    }
    out
}

/// `GENERATOR_SAMPLE` from the parity harness, so both run the same sample.
fn generator_sample() -> Vec<String> {
    let script = std::fs::read_to_string(repo_root().join("scripts/compat-parse-error-parity.py"))
        .expect("the parity harness is readable");
    let start = script
        .find("GENERATOR_SAMPLE = (")
        .expect("GENERATOR_SAMPLE is defined");
    let body = &script[start..];
    let body = &body[..body.find(')').expect("GENERATOR_SAMPLE is closed")];
    body.split('"')
        .skip(1)
        .step_by(2)
        .map(str::to_string)
        .collect()
}

#[test]
fn test_bc_lexer_matches_beancount_lex_iter_string() {
    let python = std::env::var("RLEDGER_BEANCOUNT_PYTHON").unwrap_or_else(|_| "python3".into());
    let inputs = file_inputs();
    let request = serde_json::json!({
        "inputs": inputs,
        "matrix": repo_root().join("scripts/stray-char-matrix.py"),
        "generators": generator_sample(),
    });
    let child = Command::new(&python)
        .args(["-I", "-c", PYTHON])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn();
    let Ok(mut child) = child else {
        skip("Skipping: Python beancount not available (no python3)");
        return;
    };
    // A failed write (python exited early) shows in its output below.
    let _ = child
        .stdin
        .take()
        .expect("stdin is piped")
        .write_all(request.to_string().as_bytes());
    let output = child.wait_with_output().expect("python runs");
    assert!(output.status.success(), "the python side failed");
    let stdout = String::from_utf8(output.stdout).expect("python prints UTF-8");
    let mut lines = stdout.split('\n');
    let head = lines.next().unwrap_or_default();
    if let Some(why) = head.strip_prefix("SKIP ") {
        let marker = if why.starts_with("ptadiff") {
            format!("Skipping: ptadiff not available ({why})")
        } else {
            format!("Skipping: Python beancount not available ({why})")
        };
        skip(&marker);
        return;
    }
    let total: usize = head
        .strip_prefix("OK ")
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("unexpected first line from python: {head:?}"));

    let (mut compared, mut crashed, mut differ) = (0usize, 0usize, Vec::new());
    for line in lines.filter(|l| !l.is_empty()) {
        let obj: serde_json::Value = serde_json::from_str(line).expect("python prints JSON");
        let id = obj["id"].as_str().unwrap_or_default();
        let text = obj["text"].as_str().unwrap_or_default();
        if obj.get("crash").is_some() {
            crashed += 1;
            continue;
        }
        compared += 1;
        let theirs: Vec<(String, usize, usize)> = obj["tokens"]
            .as_array()
            .expect("tokens")
            .iter()
            .map(|t| {
                let span =
                    |i: usize| usize::try_from(t[i].as_i64().unwrap_or(-1)).unwrap_or(usize::MAX);
                (
                    t[0].as_str().unwrap_or_default().to_string(),
                    span(1),
                    span(2),
                )
            })
            .collect();
        let mine = bc_lexer_tokens(text);
        if mine != theirs {
            differ.push((id.to_string(), text.to_string(), mine, theirs));
        }
    }
    assert_eq!(compared + crashed, total, "python answered every input");
    // beancount's lexer crashing is not expected on any pinned input; a few
    // would be tolerable, all of them would mean the comparison never ran.
    assert!(
        compared > total * 99 / 100,
        "only {compared} of {total} inputs were lexed"
    );
    let mut report = String::new();
    for (id, text, mine, theirs) in differ.iter().take(20) {
        let at = mine
            .iter()
            .zip(theirs)
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| mine.len().min(theirs.len()));
        let lo = at.saturating_sub(2);
        let _ = writeln!(
            report,
            "{id}: {text:?}\n   BcLexer   {:?}\n   beancount {:?}",
            &mine[lo..mine.len().min(at + 3)],
            &theirs[lo..theirs.len().min(at + 3)],
        );
    }
    assert!(
        differ.is_empty(),
        "BcLexer reads {} of {compared} inputs differently from beancount's lexer \
         ({crashed} crashed beancount's lexer); first ones:\n{report}",
        differ.len()
    );
    eprintln!("bc lexer drift: {compared} inputs agree ({crashed} crashed beancount's lexer)");
}
