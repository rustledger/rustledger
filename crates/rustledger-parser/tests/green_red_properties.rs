//! Green/red parser parity over GENERATED beancount source (#1902 Phase 3).
//!
//! The green transaction converter returns `Some` only when it exactly
//! replicates the red path and bails to red otherwise, so any divergence is a
//! green bug. Two things already pin that: `fuzz_green_eq_red`, and the
//! `parse_green_eq_red_corpus` list inside `cst/green.rs`.
//!
//! Neither reaches the green path with any regularity, which is the gap this
//! closes.
//!
//! `fuzz_green_eq_red` mutates raw BYTES. Measured before writing this: of
//! 20 000 random byte inputs, **zero** produced even one directive — let alone
//! the well-formed simple transaction the green converter is the only consumer
//! of. The fuzzer is a fine guard on lexing and error recovery, and it is
//! structurally incapable of exercising the thing it is named after. So the
//! green converter's correctness rested entirely on ~25 hand-picked corpus
//! entries, i.e. on what someone thought to write down.
//!
//! A structured generator inverts that. Every case here parses, so the green
//! path engages on most of them, and the shapes are combined rather than
//! enumerated: costs crossed with prices crossed with flags crossed with tags,
//! which is where the corpus stops (it has one entry per feature, not products
//! of features). #1713 — the compound-cost latch — was exactly a product bug.
//!
//! The generator deliberately emits the red-FALLBACK triggers too (posting
//! metadata, body comments, arithmetic, the deprecated pipe). Those exercise
//! the other side of the branch: green must decline, and declining must land
//! on the same answer.

use proptest::prelude::*;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

const ACCOUNTS: &[&str] = &[
    "Assets:Bank",
    "Assets:Broker",
    "Expenses:Food",
    "Income:Salary",
    "Liabilities:Card",
    "Equity:Opening",
];
const CURRENCIES: &[&str] = &["USD", "EUR", "AAPL", "GBP"];
const FLAGS: &[&str] = &["*", "!", "txn"];

/// A number, spanning the shapes the lexer treats differently.
fn number() -> impl Strategy<Value = String> {
    prop_oneof![
        (1i64..10_000).prop_map(|n| n.to_string()),
        (1i64..10_000).prop_map(|n| format!("-{n}")),
        (1i64..1000, 0u32..3).prop_map(|(n, s)| format!(
            "{n}.{:0width$}",
            0,
            width = s as usize + 1
        )),
        Just("0".to_owned()),
        // Thousands separators and a leading `+` are lexed, not arithmetic.
        (1i64..999).prop_map(|n| format!("{n},000.00")),
        (1i64..999).prop_map(|n| format!("+{n}.50")),
    ]
}

/// A cost spec, including the shapes that historically diverged.
///
/// `{}` (empty), `{{...}}` (total), the compound `{N # M CCY}` from #1713, and
/// costs carrying a date or a label — each is a separate branch in the green
/// converter's `cost_spec_from_tokens` mirror.
fn cost() -> impl Strategy<Value = String> {
    prop_oneof![
        Just(String::new()),
        Just(" {}".to_owned()),
        (number(), 0usize..CURRENCIES.len())
            .prop_map(|(n, c)| format!(" {{{n} {}}}", CURRENCIES[c])),
        (number(), 0usize..CURRENCIES.len())
            .prop_map(|(n, c)| format!(" {{{{{n} {}}}}}", CURRENCIES[c])),
        (number(), number(), 0usize..CURRENCIES.len())
            .prop_map(|(a, b, c)| format!(" {{{a} # {b} {}}}", CURRENCIES[c])),
        (number(), 0usize..CURRENCIES.len(), 1u32..28)
            .prop_map(|(n, c, d)| format!(" {{{n} {}, 2024-01-{d:02}}}", CURRENCIES[c])),
        (number(), 0usize..CURRENCIES.len())
            .prop_map(|(n, c)| format!(" {{{n} {}, \"lot-a\"}}", CURRENCIES[c])),
        // `*` merge, and a bare date-only spec.
        Just(" {*}".to_owned()),
        Just(" {2024-03-01}".to_owned()),
    ]
}

/// A price annotation: absent, per-unit `@`, or total `@@`.
fn price() -> impl Strategy<Value = String> {
    prop_oneof![
        Just(String::new()),
        (number(), 0usize..CURRENCIES.len()).prop_map(|(n, c)| format!(" @ {n} {}", CURRENCIES[c])),
        (number(), 0usize..CURRENCIES.len())
            .prop_map(|(n, c)| format!(" @@ {n} {}", CURRENCIES[c])),
        Just(" @".to_owned()),
        // ARITHMETIC price amounts. Green must bail on these and let the
        // later increment evaluate them — a branch nothing reached before:
        // deleting the bail outright (`amount_present && amount.is_none()`)
        // failed no test in the crate, and neither did making the amount
        // latch the LAST token instead of the first, which is the #1713 shape
        // one level down. Both are caught now.
        (number(), number(), 0usize..CURRENCIES.len())
            .prop_map(|(a, b, c)| format!(" @ {a} + {b} {}", CURRENCIES[c])),
        (number(), number(), 0usize..CURRENCIES.len())
            .prop_map(|(a, b, c)| format!(" @@ {a} * {b} {}", CURRENCIES[c])),
        (number(), number(), 0usize..CURRENCIES.len())
            .prop_map(|(a, b, c)| format!(" @ ({a} - {b}) {}", CURRENCIES[c])),
    ]
}

/// One posting line, with its optional flag, units, cost and price.
///
/// An elided-units posting (`Assets:Bank` alone) is included because it is the
/// balancing leg every real transaction has, and because the green converter
/// has to reproduce red's `None` units rather than a zero.
fn posting() -> impl Strategy<Value = String> {
    (
        prop_oneof![Just(""), Just("! "), Just("* "), Just("# ")],
        0usize..ACCOUNTS.len(),
        prop::option::of((number(), 0usize..CURRENCIES.len())),
        cost(),
        price(),
    )
        .prop_map(|(flag, acct, units, cost, price)| match units {
            Some((n, c)) => format!(
                "  {flag}{} {n} {}{cost}{price}",
                ACCOUNTS[acct], CURRENCIES[c]
            ),
            None => format!("  {flag}{}", ACCOUNTS[acct]),
        })
}

/// Trailing tags and links on the transaction line.
fn tags_and_links() -> impl Strategy<Value = String> {
    prop::collection::vec(
        prop_oneof![
            Just(" #trip".to_owned()),
            Just(" #food".to_owned()),
            Just(" ^invoice-1".to_owned()),
            Just(" ^receipt".to_owned()),
        ],
        0..3,
    )
    .prop_map(|v| v.concat())
}

/// Lines appended INSIDE a transaction that force the green path to bail.
///
/// Green must decline on each of these and hand over to red. That is half the
/// contract and the corpus covers it one entry at a time; here they land in
/// combination with arbitrary postings, costs and prices.
fn fallback_line() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("    note: \"m\"\n".to_owned()),
        Just("    ; a body comment\n".to_owned()),
        Just("    key: 42\n".to_owned()),
        Just("    when: 2024-05-05\n".to_owned()),
        Just("  Assets:Bank 5 USD + 3 USD\n".to_owned()),
        Just("  Assets:Bank 5 USD 3 USD\n".to_owned()),
    ]
}

fn transaction() -> impl Strategy<Value = String> {
    (
        1u32..28,
        0usize..FLAGS.len(),
        prop::option::of(Just("\"Payee\"".to_owned())),
        tags_and_links(),
        prop::collection::vec(posting(), 1..4),
        prop::collection::vec(fallback_line(), 0..2),
        any::<bool>(),
    )
        .prop_map(|(day, flag, payee, tl, postings, extras, pipe)| {
            let head = match (&payee, pipe) {
                (Some(p), true) => format!("{p} | \"narration\""),
                (Some(p), false) => format!("{p} \"narration\""),
                (None, _) => "\"narration\"".to_owned(),
            };
            let mut s = format!("2024-01-{day:02} {} {head}{tl}\n", FLAGS[flag]);
            for e in &extras {
                s.push_str(e);
            }
            for p in &postings {
                s.push_str(p);
                s.push('\n');
            }
            s
        })
}

/// The non-transaction directives, plus options and plugins.
///
/// The green converter does not handle these, so they hold trivially — which
/// is the point of including them. If it ever grows to, a divergence shows up
/// here rather than shipping unpinned, the same reasoning the fuzz target
/// applies to `includes`/`plugins`.
fn other_directive() -> impl Strategy<Value = String> {
    (
        1u32..28,
        0usize..ACCOUNTS.len(),
        0usize..CURRENCIES.len(),
        number(),
    )
        .prop_flat_map(|(d, a, c, n)| {
            let (acct, cur) = (ACCOUNTS[a], CURRENCIES[c]);
            prop_oneof![
                Just(format!("2024-02-{d:02} open {acct}\n")),
                Just(format!("2024-02-{d:02} open {acct} {cur}\n")),
                Just(format!("2024-02-{d:02} open {acct} {cur} \"FIFO\"\n")),
                Just(format!("2024-02-{d:02} close {acct}\n")),
                Just(format!("2024-02-{d:02} balance {acct} {n} {cur}\n")),
                Just(format!("2024-02-{d:02} balance {acct} {n} ~ 0.01 {cur}\n")),
                Just(format!("2024-02-{d:02} price {cur} {n} USD\n")),
                Just(format!("2024-02-{d:02} note {acct} \"a note\"\n")),
                Just(format!("2024-02-{d:02} event \"loc\" \"here\"\n")),
                Just(format!("2024-02-{d:02} document {acct} \"/x.pdf\"\n")),
                Just(format!("2024-02-{d:02} commodity {cur}\n")),
                Just(format!("2024-02-{d:02} pad {acct} Equity:Opening\n")),
                Just(format!("2024-02-{d:02} custom \"budget\" \"x\" {n}\n")),
                Just(format!("2024-02-{d:02} query \"q\" \"SELECT 1\"\n")),
                Just("option \"title\" \"t\"\n".to_owned()),
                Just("plugin \"beancount.plugins.auto\"\n".to_owned()),
                Just("; a top-level comment\n".to_owned()),
                Just("\n".to_owned()),
                // Error recovery — a green bail must still agree with red on
                // WHERE recovery resumes.
                Just("garbage line\n".to_owned()),
                Just("2024-13-99 * \"bad date\"\n  Assets:Bank 1 USD\n".to_owned()),
            ]
        })
}

fn ledger_source() -> impl Strategy<Value = String> {
    prop::collection::vec(
        prop_oneof![3 => transaction(), 2 => other_directive()],
        1..7,
    )
    .prop_map(|parts| parts.concat())
}

/// The `ParseResult` fields `fuzz_green_eq_red` compares — deliberately that
/// list and not "everything".
///
/// `syntax_root` is excluded, which Copilot was right to want said out loud:
/// both paths build the SAME lossless CST and only differ in how they walk it,
/// so comparing the tree would pass by construction while saying nothing about
/// the conversion under test. Mirroring the fuzz target's list also keeps the
/// two guards' notions of "the parity contract" from drifting apart, which is
/// the failure mode this whole file exists to catch.
///
/// Kept in one place so a new field on `ParseResult` is one edit rather than a
/// silent coverage hole. Compared via `Debug` for the same reason the fuzz
/// target does: it avoids requiring `PartialEq` on every field type.
fn observables(r: &rustledger_parser::ParseResult) -> Vec<(&'static str, String)> {
    vec![
        ("directives", format!("{:?}", r.directives)),
        ("errors", format!("{:?}", r.errors)),
        ("options", format!("{:?}", r.options)),
        ("comments", format!("{:?}", r.comments)),
        (
            "account_occurrences",
            format!("{:?}", r.account_occurrences),
        ),
        (
            "currency_occurrences",
            format!("{:?}", r.currency_occurrences),
        ),
        ("includes", format!("{:?}", r.includes)),
        ("plugins", format!("{:?}", r.plugins)),
        ("warnings", format!("{:?}", r.warnings)),
        ("has_leading_bom", format!("{:?}", r.has_leading_bom)),
        ("alignment", format!("{:?}", r.alignment)),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The green-wired `parse` must equal `parse_red_only` on every input.
    ///
    /// Reported field by field rather than as one blob: a divergence in
    /// `directives` and a divergence in `alignment` are different bugs, and a
    /// single `assert_eq!` over a joined string names neither.
    #[test]
    fn green_equals_red_on_generated_ledgers(source in ledger_source()) {
        let green = observables(&parse(&source));
        let red = observables(&parse_red_only(&source));

        for ((name, g), (_, r)) in green.iter().zip(red.iter()) {
            prop_assert_eq!(
                g, r,
                "green vs red diverged on `{}` for source:\n{}",
                name, source
            );
        }
    }

    /// The same, with a BOM in front.
    ///
    /// Separate rather than folded into the generator: a BOM shifts every
    /// span, so if it were one case in ten the shrinker would usually drop it
    /// and the counterexample would not say that the BOM was load-bearing.
    #[test]
    fn green_equals_red_with_a_leading_bom(source in ledger_source()) {
        let source = format!("\u{feff}{source}");
        let green = observables(&parse(&source));
        let red = observables(&parse_red_only(&source));

        for ((name, g), (_, r)) in green.iter().zip(red.iter()) {
            prop_assert_eq!(
                g, r,
                "green vs red diverged on `{}` with a BOM for source:\n{}",
                name, source
            );
        }
    }
}

/// The generator must actually reach the green path.
///
/// This is the whole premise: the byte fuzzer produces zero directives in
/// 20 000 tries, so if this generator also failed to produce parseable
/// transactions the property above would be a slower way of testing nothing.
///
/// Asserting on the OUTPUT rather than on green's internals, because the
/// converter's `Some`/`None` is not observable from here — a source that
/// yields a transaction with postings and no parse errors is the shape the
/// green path is the only consumer of.
#[test]
fn the_generator_reaches_well_formed_transactions() {
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

    const N: u32 = 500;

    let mut runner = TestRunner::deterministic();
    let strategy = ledger_source();
    let (mut parsed, mut clean_txns) = (0u32, 0u32);

    for _ in 0..N {
        let source = strategy.new_tree(&mut runner).expect("generates").current();
        let r = parse(&source);
        if !r.directives.is_empty() {
            parsed += 1;
        }
        if r.errors.is_empty()
            && r.directives.iter().any(|d| {
                matches!(&d.value, rustledger_core::Directive::Transaction(t)
                    if !t.postings.is_empty())
            })
        {
            clean_txns += 1;
        }
    }

    assert!(
        parsed * 10 >= N * 9,
        "generator should parse nearly always, got {parsed}/{N}"
    );
    assert!(
        clean_txns * 4 >= N,
        "at least a quarter of generated ledgers must be error-free \
         transactions with postings — the shape the green converter is the \
         only consumer of. Got {clean_txns}/{N}, so this suite would be \
         exercising red-fallback and error recovery, which the byte fuzzer \
         already covers."
    );
}
