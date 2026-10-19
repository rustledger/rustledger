//! BQL's regular expressions are Python's, as in bean-query (#2656).
//!
//! bean-query matches with Python's `re`: `x ~ p` is
//! `re.search(p, x, re.IGNORECASE)`, `grep`/`grepn` are `re.search`,
//! `subst` is `re.sub`, `findfirst` is `re.match` over `sorted(values)`, and
//! `has_account(p)` and `JOURNAL 'p'` are `~` in disguise. rledger handed the
//! pattern to the `regex` crate unchanged, whose syntax is not Python's. Each
//! pattern is now read with Python's grammar (`rustledger_core::py_regex`),
//! and a construct rledger cannot express is an error naming it.
//!
//! Every expected value is beanquery 0.2.0's (beancount 3.2.3, `CPython` 3.13)
//! on [`LEDGER`], except the refusals, whose text is rledger's.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::executor::SummaryAccounts;
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2023-01-01 open Assets:Bank USD
2023-01-01 open Assets:Bank-Card USD
2023-01-01 open Expenses:Food USD
2023-01-01 open Expenses:Coffee:Shop USD

2023-01-05 * "Café Ünïcode" "Lunch at [the] place" #zeta #Alpha #beta
  Expenses:Food      20.00 USD
  Assets:Bank       -20.00 USD

2023-01-06 * "Shop" "coffee beans 2x" #coffee
  Expenses:Coffee:Shop   5.00 USD
  Assets:Bank-Card      -5.00 USD
"#;

fn cell(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(inv) => inv.to_string(),
        Value::Boolean(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        Value::Null => String::new(),
        other => format!("{other:?}"),
    }
}

fn run(source: &str, query: &str) -> Result<Vec<Vec<String>>, String> {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", source);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    let result = executor
        .execute(&parse(query).expect("parses"))
        .map_err(|e| e.to_string())?;
    Ok(result
        .rows
        .iter()
        .map(|row| row.iter().map(cell).collect())
        .collect())
}

fn rows(source: &str, query: &str) -> Vec<Vec<String>> {
    run(source, query).unwrap_or_else(|e| panic!("{query}: {e}"))
}

fn table(expected: &[&[&str]]) -> Vec<Vec<String>> {
    expected
        .iter()
        .map(|row| row.iter().map(ToString::to_string).collect())
        .collect()
}

fn column(query: &str) -> Vec<String> {
    rows(LEDGER, query)
        .into_iter()
        .map(|mut r| r.remove(0))
        .collect()
}

fn error(query: &str) -> String {
    run(LEDGER, query).expect_err(query)
}

/// `~` searches anywhere, ignoring case; `!~` is its negation.
#[test]
fn tilde_is_a_case_insensitive_search() {
    assert_eq!(
        column("SELECT DISTINCT account WHERE account ~ 'bank' ORDER BY account"),
        ["Assets:Bank", "Assets:Bank-Card"]
    );
    assert!(column("SELECT DISTINCT account WHERE account ~ '^bank'").is_empty());
    assert_eq!(
        column("SELECT DISTINCT account WHERE account !~ 'bank' ORDER BY account"),
        ["Expenses:Coffee:Shop", "Expenses:Food"]
    );
    // Python's `\Z` is the end of the string; `regex` has no `\Z`.
    assert_eq!(
        column(r"SELECT DISTINCT account WHERE account ~ 'card\Z'"),
        ["Assets:Bank-Card"]
    );
    // An inline flag group turns the case back on, as in Python.
    assert!(column("SELECT DISTINCT narration WHERE narration ~ '(?-i:LUNCH)'").is_empty());
    assert_eq!(
        column("SELECT DISTINCT narration WHERE narration ~ '(?-i:Lunch)'"),
        ["Lunch at [the] place"]
    );
}

/// Patterns whose text means something else to the `regex` crate.
#[test]
fn tilde_reads_python_syntax() {
    // A set of `[`, `:`, `a`, `l`, `p`, `h`, followed by `]`, to Python; a
    // POSIX class to `regex`, which matched every account.
    assert!(column("SELECT DISTINCT account WHERE account ~ '[[:alpha:]]'").is_empty());
    // `(?P<name>...)` and Python's escapes.
    assert_eq!(
        column("SELECT DISTINCT account WHERE account ~ ':(?P<x>[a-z])' ORDER BY account").len(),
        4
    );
    assert_eq!(
        column(r"SELECT DISTINCT narration WHERE narration ~ '\d'"),
        ["coffee beans 2x"]
    );
    assert_eq!(
        column(r"SELECT DISTINCT payee WHERE payee ~ '\u00fcn\u00efcode'"),
        ["Café Ünïcode"]
    );
}

/// A construct Python has and rledger cannot express is refused by name,
/// never matched differently.
#[test]
fn constructs_rledger_cannot_express_are_refused() {
    for (query, construct) in [
        ("SELECT account WHERE account ~ 'Bank(?!-)'", "lookahead"),
        ("SELECT account WHERE account ~ '(?<=:)Bank'", "lookbehind"),
        (r"SELECT account WHERE account ~ '(a)\1'", "backreference"),
        ("SELECT account FROM has_account('Bank(?=-)')", "lookahead"),
        ("JOURNAL 'Bank(?!-)'", "lookahead"),
        ("SELECT grep('a(?=t)', narration)", "lookahead"),
        ("SELECT findfirst('(?<=a)l', tags)", "lookbehind"),
        ("SELECT subst('(?=a)a', 'b', narration)", "lookahead"),
    ] {
        let err = error(query);
        assert!(
            err.contains(construct) && err.contains("rledger does not"),
            "{query}: {err}"
        );
    }
    // A pattern Python rejects too.
    let err = error("SELECT account WHERE account ~ 'Bank('");
    assert!(err.contains("not a valid regular expression"), "{err}");
}

/// `grep` and `grepn` are case-sensitive `re.search`; `grepn` refuses a
/// group the pattern does not have, as `match.group(n)` does.
#[test]
fn grep_and_grepn_are_case_sensitive_searches() {
    assert_eq!(
        rows(
            LEDGER,
            r"SELECT grep('[a-z]+', narration), grep('LUNCH', narration), grepn('(\w+) (\w+)', narration, 2) WHERE account ~ 'Bank$|Card'"
        ),
        table(&[&["unch", "", "at"], &["coffee", "", "beans"]])
    );
    for n in ["5", "-1"] {
        let err = error(&format!(r"SELECT grepn('(\w+)', narration, {n})"));
        assert!(err.contains("no such group"), "{n}: {err}");
    }
}

/// `subst` is `re.sub`: `\2 \1` are groups, `$1` is literal text.
#[test]
fn subst_is_python_re_sub() {
    assert_eq!(
        rows(
            LEDGER,
            r"SELECT subst('(\w+) (\w+)', '\2 \1', narration), subst('o', '$1', narration) WHERE account ~ 'Bank$|Card'"
        ),
        table(&[
            &["at Lunch [the] place", "Lunch at [the] place"],
            &["beans coffee 2x", "c$1ffee beans 2x"],
        ])
    );
    // NULL in, NULL out: a transaction with no payee. This was a type error.
    let no_payee = r#"
2023-01-01 open Assets:Bank USD
2023-01-01 open Expenses:Food USD
2023-01-05 * "Lunch"
  Expenses:Food      20.00 USD
  Assets:Bank       -20.00 USD
"#;
    assert_eq!(
        rows(no_payee, "SELECT subst('a', 'b', payee), 'k'"),
        table(&[&["", "k"], &["", "k"]])
    );
}

/// `findfirst` is `re.match` (anchored, case-sensitive) over the sorted set.
#[test]
fn findfirst_matches_the_sorted_set_from_the_start() {
    assert_eq!(
        rows(
            LEDGER,
            "SELECT findfirst('[a-z]', tags), findfirst('eta', tags), findfirst('alpha', tags) WHERE account ~ 'Bank$|Card'"
        ),
        table(&[&["beta", "", ""], &["coffee", "", ""]])
    );
}

/// `has_account` and `JOURNAL`'s pattern are case-insensitive searches.
#[test]
fn has_account_and_journal_ignore_case() {
    assert_eq!(
        column("SELECT account FROM has_account('BANK-card')"),
        ["Expenses:Coffee:Shop", "Assets:Bank-Card"]
    );
    // Python syntax, not `regex`'s: no account has a `]` after a letter.
    assert!(column("SELECT account FROM has_account('[[:alpha:]]')").is_empty());
    assert!(rows(LEDGER, "JOURNAL '[[:alpha:]]'").is_empty());
    assert_eq!(
        rows(LEDGER, "JOURNAL 'bank-CARD'")
            .into_iter()
            .map(|r| r[4].clone())
            .collect::<Vec<_>>(),
        ["Assets:Bank-Card"]
    );
}

/// Narrations with each kind of character the two engines' word definitions
/// disagree on (a decomposed accent, a Devanagari vowel sign, an emoji
/// zero-width joiner, a superscript) on the `!` transactions; the `*` ones
/// hold none.
const WORDS: &str = "2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Coffee USD
2024-01-02 * \"black coffee\" #t0
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-03 * \"th\u{e9} coffee\" #t1
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-04 ! \"cafe\u{301} coffee\" #t2
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-05 ! \"\u{91a}\u{93e}\u{92f} coffee\" #t3
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-06 ! \"\u{1f468}\u{200d}\u{1f469} coffee\" #t4
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-07 ! \"x\u{b2} coffee\" #t5
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
2024-01-08 * \"coffeehouse\" #t6
  Expenses:Coffee  1.00 USD
  Assets:Cash  -1.00 USD
";

/// An account with a decomposed accent, which beancount accepts.
const ACCENTED_ACCOUNT: &str = "2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Cafe\u{301} USD
2024-01-02 * \"x\"
  Expenses:Cafe\u{301}  1.00 USD
  Assets:Cash  -1.00 USD
";

/// `\b` and `\B` answer as bean-query does where the text lets them answer
/// exactly, and are refused, naming the character, where it does not
/// (#2656). Expected rows are bean-query's.
#[test]
fn word_boundaries_answer_exactly_or_refuse() {
    // `*` rows: ASCII and a precomposed `é`, a word character to both.
    assert_eq!(
        rows(
            WORDS,
            r"SELECT date, narration ~ '\bcoffee\b' WHERE flag = '*'"
        ),
        table(&[
            &["2024-01-02", "TRUE"],
            &["2024-01-02", "TRUE"],
            &["2024-01-03", "TRUE"],
            &["2024-01-03", "TRUE"],
            &["2024-01-08", "FALSE"],
            &["2024-01-08", "FALSE"],
        ])
    );
    assert_eq!(
        rows(
            WORDS,
            r"SELECT date, narration !~ '\bcoffee\b' WHERE flag = '*'"
        )
        .iter()
        .map(|r| r[1].clone())
        .collect::<Vec<_>>(),
        ["FALSE", "FALSE", "FALSE", "FALSE", "TRUE", "TRUE"]
    );
    assert_eq!(
        rows(
            WORDS,
            r"SELECT date, narration ~ '\Bfee\b' WHERE flag = '*'"
        )
        .iter()
        .map(|r| r[1].clone())
        .collect::<Vec<_>>(),
        ["TRUE", "TRUE", "TRUE", "TRUE", "FALSE", "FALSE"]
    );
    assert_eq!(
        rows(
            WORDS,
            r"SELECT grep('\bcof\w+', narration), grepn('(\w+) (coffee)\b', narration, 1), subst('\bcoffee\b', 'tea', narration) WHERE flag = '*'"
        ),
        table(&[
            &["coffee", "black", "black tea"],
            &["coffee", "black", "black tea"],
            &["coffee", "th\u{e9}", "th\u{e9} tea"],
            &["coffee", "th\u{e9}", "th\u{e9} tea"],
            &["coffeehouse", "", "coffeehouse"],
            &["coffeehouse", "", "coffeehouse"],
        ])
    );
    // `AND` stops at a false left operand, as bean-query's does, so the `!`
    // rows' narrations are never matched.
    assert_eq!(
        rows(
            WORDS,
            r"SELECT date WHERE flag = '*' AND narration ~ '\bcoffee\b'"
        )
        .len(),
        4
    );
    // `(?a)`: ASCII word boundaries, exact on any text.
    assert_eq!(
        rows(WORDS, r"SELECT narration ~ '(?a)\bcoffee\b'")
            .iter()
            .filter(|r| r[0] == "TRUE")
            .count(),
        12
    );
    // Each site refuses a text holding a character it cannot classify the
    // way Python does, naming it.
    for (query, character) in [
        (r"SELECT date WHERE narration ~ '\bcoffee\b'", "U+0301"),
        (
            r"SELECT date WHERE narration !~ '\bcoffee\b' AND flag = '!'",
            "U+0301",
        ),
        (
            r"SELECT grep('\bcof', narration) WHERE date = 2024-01-05",
            "U+093E",
        ),
        (
            r"SELECT grepn('(\bcof)', narration, 1) WHERE date = 2024-01-06",
            "U+200D",
        ),
        (
            r"SELECT subst('\bcoffee', 'tea', narration) WHERE date = 2024-01-07",
            "U+00B2",
        ),
        (
            r"SELECT findfirst('\bx', narration) WHERE date = 2024-01-07",
            "U+00B2",
        ),
    ] {
        let err = run(WORDS, query).expect_err(query);
        assert!(
            err.contains(character) && err.contains(r"(?a)\b"),
            "{query}: {err}"
        );
    }
    // has_account answers when an account it can match exactly matches,
    // as Python's `any` does whatever order it tries them in.
    assert_eq!(
        rows(
            ACCENTED_ACCOUNT,
            r"SELECT account FROM has_account('\bCash\b')"
        )
        .len(),
        2
    );
    for query in [
        r"SELECT account FROM has_account('\bCafe\b')",
        r"JOURNAL '\bCash\b'",
    ] {
        let err = run(ACCENTED_ACCOUNT, query).expect_err(query);
        assert!(err.contains("U+0301"), "{query}: {err}");
    }
}
