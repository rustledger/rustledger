//! A proptest generator of realistic, parse-clean ledgers for the formatter
//! round-trip properties.
//!
//! Shared through `#[path]` by `rustledger-parser`'s
//! `format_roundtrip_properties` test and `rustledger-lsp`'s
//! `format_surface_parity` test, so both draw from the same shapes.
//!
//! Every directive kind, with the parts a formatter rebuilds and can get wrong:
//! multi-line and unicode strings with escapes, comments in every slot
//! (header-trailing, own-line inside a body, posting-trailing, metadata-
//! trailing, between directives, org-mode headings), metadata of every value
//! type, tags and links, cost specs (per-unit, total, compound, dated,
//! labelled, merge), prices, arithmetic, 28-digit numbers, thousands
//! separators, deliberately sloppy spacing (tabs, runs of spaces), and a
//! whole-file BOM, CRLF line endings and a missing final newline.

use proptest::prelude::*;

fn account() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("Assets:Bank:Checking".to_string()),
        Just("Assets:Broker".to_string()),
        Just("Expenses:Food".to_string()),
        Just("Expenses:Café:Ünïcode".to_string()),
        Just("Income:Salary".to_string()),
        Just("Liabilities:Card".to_string()),
        Just("Equity:Opening-Balances".to_string()),
        Just("Expenses:生活".to_string()),
        "Assets:[A-Z][a-z]{0,8}".prop_map(|s| s),
    ]
}

fn currency() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("USD"),
        Just("EUR"),
        Just("HOOL"),
        Just("VACHR"),
        Just("BTC.X"),
        Just("A_B-C"),
    ]
}

/// A number literal, as written: scale kept, thousands separators sometimes,
/// up to 28 significant digits.
fn number() -> impl Strategy<Value = String> {
    prop_oneof![
        4 => (-100_000i64..100_000, 0u32..4).prop_map(|(n, s)| {
            rust_decimal::Decimal::new(n, s).to_string()
        }),
        1 => Just("1,234.56".to_string()),
        1 => Just("-12,345,678.00".to_string()),
        1 => "[1-9][0-9]{20,26}".prop_map(|s| s),
        1 => "0\\.[0-9]{20,27}".prop_map(|s| s),
        1 => Just("1.50".to_string()),
        1 => Just("0.000".to_string()),
    ]
}

/// A positive number (prices and cost numbers).
fn positive() -> impl Strategy<Value = String> {
    number().prop_map(|n| n.trim_start_matches('-').to_string())
}

/// A number or an arithmetic expression of numbers.
fn expr() -> impl Strategy<Value = String> {
    // Operands are small, so no expression overflows or divides inexactly
    // below the 1e-28 floor (both parse errors).
    let small = || {
        (1u32..10_000, 0u32..3)
            .prop_map(|(n, s)| rust_decimal::Decimal::new(n.into(), s).to_string())
    };
    prop_oneof![
        5 => number(),
        1 => (small(), small()).prop_map(|(a, b)| format!("{a} + {b}")),
        1 => (small(), small()).prop_map(|(a, b)| format!("({a} * {b})")),
        1 => (small(), prop_oneof![Just(2), Just(4), Just(5), Just(8)]).prop_map(|(a, b)| format!("{a}/{b}")),
        1 => small().prop_map(|a| format!("-({a})")),
    ]
}

/// String contents: unicode, escaped quotes and backslashes, and newlines
/// (a multi-line string), `;` and `#` that must stay text.
fn string_body() -> impl Strategy<Value = String> {
    prop_oneof![
        3 => "[A-Za-z0-9 ]{0,16}".prop_map(|s| s),
        1 => Just("Café ünïcode 生活 🍕".to_string()),
        1 => Just("multi\nline".to_string()),
        1 => Just("a\n\n  ; not a comment\nb".to_string()),
        1 => Just("tab\there".to_string()),
        1 => Just("quote \\\" inside".to_string()),
        1 => Just("back\\\\slash".to_string()),
        1 => Just("x ; y # z ^w".to_string()),
        1 => Just("trailing spaces   \n  leading".to_string()),
    ]
}

fn string() -> impl Strategy<Value = String> {
    string_body().prop_map(|s| format!("\"{s}\""))
}

fn date() -> impl Strategy<Value = String> {
    (2000i32..2030, 1u32..13, 1u32..29).prop_map(|(y, m, d)| format!("{y:04}-{m:02}-{d:02}"))
}

/// The gap between two tokens on a line: canonical, sloppy, or a tab.
fn gap() -> impl Strategy<Value = &'static str> {
    prop_oneof![4 => Just(" "), 1 => Just("   "), 1 => Just("\t"), 1 => Just(" \t ")]
}

/// A body-line indent: two spaces, four, a tab, or a sloppy mix.
fn indent() -> impl Strategy<Value = &'static str> {
    prop_oneof![4 => Just("  "), 1 => Just("    "), 1 => Just("\t"), 1 => Just(" \t")]
}

/// An optional same-line trailing comment.
fn trailing() -> impl Strategy<Value = String> {
    prop_oneof![
        4 => Just(String::new()),
        1 => Just(" ; note".to_string()),
        1 => Just("  ;; \"quoted\" ; nested".to_string()),
        1 => Just("\t;".to_string()),
        1 => Just(" ;ünïcode 生活".to_string()),
    ]
}

fn tags_links() -> impl Strategy<Value = String> {
    prop::collection::vec(
        prop_oneof![
            "#[a-z][a-z0-9-]{0,6}".prop_map(|s| s),
            "\\^[a-z][a-z0-9_.]{0,6}".prop_map(|s| s),
        ],
        0..3,
    )
    .prop_map(|v| v.iter().fold(String::new(), |acc, t| acc + " " + t))
}

fn meta_value() -> impl Strategy<Value = String> {
    prop_oneof![
        string(),
        number(),
        date(),
        account(),
        currency().prop_map(str::to_string),
        Just("TRUE".to_string()),
        Just("FALSE".to_string()),
        (number(), currency()).prop_map(|(n, c)| format!("{n} {c}")),
        "#[a-z]{1,5}".prop_map(|s| s),
    ]
}

/// Metadata lines at `indent`, each with an optional trailing comment.
fn meta_lines(indent: &'static str) -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec(
        ("[a-z][a-zA-Z0-9_-]{1,8}", gap(), meta_value(), trailing())
            .prop_map(move |(k, g, v, c)| format!("{indent}{k}:{g}{v}{c}")),
        0..3,
    )
    .prop_map(|mut v| {
        // A repeated key is an error; keep the first.
        let mut seen = std::collections::HashSet::new();
        v.retain(|l| seen.insert(l.trim().split(':').next().unwrap_or("").to_string()));
        v
    })
}

fn cost() -> impl Strategy<Value = String> {
    prop_oneof![
        (positive(), Just("CCY")).prop_map(|(n, c)| format!(" {{{n} {c}}}")),
        (positive(), Just("CCY")).prop_map(|(n, c)| format!(" {{{{{n} {c}}}}}")),
        (positive(), positive(), Just("CCY")).prop_map(|(a, b, c)| format!(" {{{a} # {b} {c}}}")),
        (positive(), Just("CCY"), date()).prop_map(|(n, c, d)| format!(" {{{n} {c}, {d}}}")),
        (positive(), Just("CCY"), date(), string_body())
            .prop_map(|(n, c, d, l)| format!(" {{ {n} {c} ,{d}, \"{}\" }}", l.replace('\n', " "))),
        Just(" {}".to_string()),
        Just(" {*}".to_string()),
    ]
}

fn price() -> impl Strategy<Value = String> {
    prop_oneof![
        (positive(), Just("CCY")).prop_map(|(n, c)| format!(" @ {n} {c}")),
        (positive(), Just("CCY")).prop_map(|(n, c)| format!(" @@  {n} {c}")),
    ]
}

/// A posting line (with its metadata lines) at `ind`.
fn posting() -> impl Strategy<Value = String> {
    (
        indent(),
        prop_oneof![4 => Just(""), 1 => Just("! "), 1 => Just("* ")],
        account(),
        prop_oneof![
            1 => Just(None),
            4 => (gap(), expr(), currency()).prop_map(|(g, e, c)| Some(format!("{g} {e} {c}"))),
        ],
        prop_oneof![3 => Just(String::new()), 1 => cost()],
        prop_oneof![3 => Just(String::new()), 1 => price()],
        currency(),
        trailing(),
        meta_lines("      "),
    )
        .prop_map(
            |(ind, flag, acct, amount, cost, price, cost_ccy, c, meta)| {
                let mut line = format!("{ind}{flag}{acct}");
                if let Some(a) = amount {
                    line.push_str(&a);
                    line.push_str(&cost.replace("CCY", cost_ccy));
                    line.push_str(&price.replace("CCY", cost_ccy));
                }
                line.push_str(&c);
                for m in meta {
                    line.push('\n');
                    line.push_str(&m);
                }
                line
            },
        )
}

/// An own-line comment inside a body, at any indent (not column 0: there
/// it ends a transaction, as in beancount), or none.
fn body_comment() -> impl Strategy<Value = Option<String>> {
    prop_oneof![
        4 => Just(None),
        1 => (
            prop_oneof![Just(" "), Just("  "), Just("    "), Just("\t"), Just("        ")],
            prop_oneof![Just(";"), Just("; body"), Just(";; \"q\" ; x"), Just("; 生活")],
        )
            .prop_map(|(i, c)| Some(format!("{i}{c}"))),
    ]
}

fn transaction() -> impl Strategy<Value = String> {
    (
        date(),
        prop_oneof![Just("*"), Just("!"), Just("txn"), Just("P"), Just("#")],
        prop_oneof![
            string().prop_map(|n| format!(" {n}")),
            (string(), string()).prop_map(|(p, n)| format!(" {p} {n}")),
            Just(String::new()),
        ],
        tags_links(),
        trailing(),
        meta_lines("  "),
        prop::collection::vec((body_comment(), posting()), 0..4),
        body_comment(),
    )
        .prop_map(|(d, flag, strings, tl, c, meta, postings, last_comment)| {
            // A one-letter flag needs a space, a tab or a `\n` after it (a
            // CRLF's `\r` is none), as beancount lexes it.
            let flag = if flag == "P" && strings.is_empty() && tl.is_empty() {
                "*"
            } else {
                flag
            };
            let mut out = format!("{d} {flag}{strings}{tl}{c}");
            for m in meta {
                out.push('\n');
                out.push_str(&m);
            }
            for (comment, p) in &postings {
                if let Some(bc) = comment {
                    out.push('\n');
                    out.push_str(bc);
                }
                out.push('\n');
                out.push_str(p);
            }
            if let Some(bc) = last_comment {
                out.push('\n');
                out.push_str(&bc);
            }
            out
        })
}

fn simple_directive() -> impl Strategy<Value = String> {
    prop_oneof![
        (
            date(),
            account(),
            prop::collection::vec(currency(), 0..3),
            trailing()
        )
            .prop_map(|(d, a, cs, c)| format!("{d} open {a} {}{c}", cs.join(","))),
        (date(), account(), currency(), string()).prop_map(|(d, a, cur, b)| format!(
            "{d} open {a} {cur} {}",
            if b.len() % 2 == 0 {
                "\"FIFO\""
            } else {
                "\"STRICT\""
            }
        )),
        (date(), account()).prop_map(|(d, a)| format!("{d} close {a}")),
        (date(), currency(), meta_lines("  ")).prop_map(|(d, c, m)| {
            let mut s = format!("{d} commodity {c}");
            for l in m {
                s.push('\n');
                s.push_str(&l);
            }
            s
        }),
        (date(), currency(), gap(), positive(), currency())
            .prop_map(|(d, c, g, n, q)| format!("{d} price {c}{g}{n} {q}")),
        (date(), account(), expr(), currency(), trailing())
            .prop_map(|(d, a, n, c, t)| format!("{d} balance {a}  {n} {c}{t}")),
        (date(), account(), number(), positive(), currency())
            .prop_map(|(d, a, n, t, c)| format!("{d} balance {a} {n} ~ {t} {c}")),
        (date(), account(), account()).prop_map(|(d, a, b)| format!("{d} pad {a} {b}")),
        (date(), account(), string()).prop_map(|(d, a, s)| format!("{d} note {a} {s}")),
        (date(), account(), string(), tags_links())
            .prop_map(|(d, a, s, t)| format!("{d} document {a} {s}{t}")),
        (date(), string(), string()).prop_map(|(d, a, b)| format!("{d} event {a} {b}")),
        (date(), string(), string()).prop_map(|(d, a, b)| format!("{d} query {a} {b}")),
        (
            date(),
            string(),
            prop::collection::vec(
                prop_oneof![
                    string(),
                    number(),
                    date(),
                    account(),
                    Just("TRUE".to_string()),
                    (number(), currency()).prop_map(|(n, c)| format!("{n} {c}")),
                ],
                0..4
            )
        )
            .prop_map(|(d, n, v)| format!("{d} custom {n} {}", v.join(" "))),
    ]
}

fn undated() -> impl Strategy<Value = String> {
    prop_oneof![
        string().prop_map(|v| format!("option \"title\" {v}")),
        Just("option \"operating_currency\" \"USD\"".to_string()),
        string().prop_map(|v| format!("plugin \"beancount.plugins.auto\" {v}")),
        Just("plugin \"beancount.plugins.implicit_prices\"".to_string()),
        Just("include \"other.beancount\"".to_string()),
    ]
}

/// A comment or heading line between directives.
fn interstitial() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("; a comment".to_string()),
        Just(";".to_string()),
        Just("* Org heading \"with a quote".to_string()),
        Just("** Sub heading".to_string()),
        Just("# hash comment".to_string()),
        Just("#+STARTUP: showall".to_string()),
        Just("% percent comment".to_string()),
        Just(String::new()),
    ]
}

/// One top-level item: a directive, possibly preceded by comment lines.
fn item() -> impl Strategy<Value = String> {
    (
        prop::collection::vec(interstitial(), 0..2),
        prop_oneof![
            4 => transaction(),
            4 => simple_directive(),
            1 => undated(),
            1 => ("[a-z]{1,4}", simple_directive())
                .prop_map(|(t, d)| format!("pushtag #{t}\n{d}\npoptag #{t}")),
        ],
    )
        .prop_map(|(pre, d)| {
            let mut s = String::new();
            for p in pre {
                s.push_str(&p);
                s.push('\n');
            }
            s.push_str(&d);
            s
        })
}

/// A whole ledger: items joined by newlines, then a whole-file encoding
/// variant (BOM, CRLF, no final newline).
pub fn ledger() -> impl Strategy<Value = String> {
    (
        prop::collection::vec(item(), 1..8),
        any::<bool>(),
        prop_oneof![4 => Just("\n"), 1 => Just("\r\n")],
        prop_oneof![4 => Just(true), 1 => Just(false)],
    )
        .prop_map(|(items, bom, eol, final_nl)| {
            let mut body = items.join("\n");
            if final_nl {
                body.push('\n');
            }
            if eol == "\r\n" {
                body = crlf_outside_strings(&body);
            }
            if bom {
                body.insert(0, '\u{FEFF}');
            }
            body
        })
}

/// `\n` to `\r\n` outside string literals, so a CRLF ledger's multi-line
/// strings keep their LF values (a CRLF inside a string is string content).
/// A quote in a comment or a column-0 heading line opens no string.
fn crlf_outside_strings(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    let mut in_string = false;
    let mut escaped = false;
    let mut in_comment = false;
    let mut line_start = true;
    for ch in s.chars() {
        if line_start && !in_string && matches!(ch, '*' | '#' | '%') {
            in_comment = true;
        }
        line_start = false;
        match ch {
            '\n' if !in_string => {
                out.push_str("\r\n");
                in_comment = false;
                line_start = true;
                continue;
            }
            '\n' => line_start = true,
            ';' if !in_string => in_comment = true,
            '"' if !escaped && !in_comment => in_string = !in_string,
            _ => {}
        }
        escaped = ch == '\\' && !escaped;
        out.push(ch);
    }
    out
}

/// Run `cases` cases of the property `test` over `strategy()` on a thread
/// with a large stack, and panic with proptest's minimal failing input.
///
/// The ledger strategy is deeply nested (`prop_oneof!` over tuples of
/// tuples), and in a debug build building and drawing from it overflows the
/// default test-thread stack on macOS and Windows (Linux's is larger), so it
/// is built and run on a thread of its own.
pub fn run_property<S, F>(cases: u32, strategy: fn() -> S, test: F)
where
    S: Strategy + 'static,
    S::Value: std::fmt::Debug,
    F: Fn(S::Value) -> Result<(), proptest::test_runner::TestCaseError> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("ledger-property".into())
        .stack_size(256 << 20)
        .spawn(move || {
            let mut runner =
                proptest::test_runner::TestRunner::new(ProptestConfig::with_cases(cases));
            if let Err(e) = runner.run(&strategy(), test) {
                panic!("{e}");
            }
        })
        .expect("spawn the property thread");
    if let Err(panic) = handle.join() {
        std::panic::resume_unwind(panic);
    }
}
