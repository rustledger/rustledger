//! Integration tests for the typed-AST surface (`cst::ast`).
//!
//! Each test parses a Beancount source via `SourceFile::parse`,
//! walks the typed accessors, and asserts the read values match
//! the source text. The round-trip property (`syntax().text() ==
//! source`) is also asserted by every test so the typed layer
//! can never accidentally lose bytes.

#![allow(clippy::missing_panics_doc)]

use rustledger_parser::cst::ast::{
    Account, AstNode, AstToken, BoolFalse, BoolTrue, CostSpec, CurrencyName, Date, Directive,
    ErrorNode, Link, MetaKey, Number, PriceAnnotation, SourceFile, StringLit, Tag,
};

fn parse(source: &str) -> SourceFile {
    let f = SourceFile::parse(source);
    assert_eq!(f.syntax().text().to_string(), source, "round-trip");
    f
}

fn single_directive(f: &SourceFile) -> Directive {
    let ds: Vec<Directive> = f.directives().collect();
    assert_eq!(ds.len(), 1);
    ds.into_iter().next().unwrap()
}

// ---- 10 dated single-line directives -----------------------------

#[test]
fn open_directive_accessors() {
    let f = parse("2024-01-01 open Assets:Cash USD,EUR \"STRICT\"\n");
    let Directive::Open(d) = single_directive(&f) else {
        panic!("expected Open");
    };
    assert_eq!(d.date().unwrap().text(), "2024-01-01");
    assert_eq!(d.account().unwrap().text(), "Assets:Cash");
    let curs: Vec<String> = d.currencies().map(|c| c.text().to_string()).collect();
    assert_eq!(curs, vec!["USD", "EUR"]);
    // accessor still returns &str when called on a bound value
    let acct = d.account().unwrap();
    let _: &str = acct.text();
    assert_eq!(
        d.booking_method().unwrap().text_unquoted().unwrap(),
        "STRICT"
    );
}

#[test]
fn close_directive_accessors() {
    let f = parse("2024-12-31 close Assets:Cash\n");
    let Directive::Close(d) = single_directive(&f) else {
        panic!("expected Close");
    };
    assert_eq!(d.date().unwrap().text(), "2024-12-31");
    assert_eq!(d.account().unwrap().text(), "Assets:Cash");
}

#[test]
fn balance_directive_accessors() {
    let f = parse("2024-06-30 balance Assets:Cash 100.00 USD\n");
    let Directive::Balance(d) = single_directive(&f) else {
        panic!("expected Balance");
    };
    assert_eq!(d.date().unwrap().text(), "2024-06-30");
    assert_eq!(d.account().unwrap().text(), "Assets:Cash");
    assert_eq!(d.number().unwrap().text(), "100.00");
    assert_eq!(d.currency().unwrap().text(), "USD");
}

#[test]
fn pad_directive_accessors() {
    let f = parse("2024-01-01 pad Assets:Cash Equity:Opening\n");
    let Directive::Pad(d) = single_directive(&f) else {
        panic!("expected Pad");
    };
    assert_eq!(d.target_account().unwrap().text(), "Assets:Cash");
    assert_eq!(d.source_account().unwrap().text(), "Equity:Opening");
}

#[test]
fn event_directive_accessors() {
    let f = parse("2024-01-15 event \"location\" \"Berlin\"\n");
    let Directive::Event(d) = single_directive(&f) else {
        panic!("expected Event");
    };
    assert_eq!(d.event_type().unwrap().text_unquoted().unwrap(), "location");
    assert_eq!(d.value().unwrap().text_unquoted().unwrap(), "Berlin");
}

#[test]
fn query_directive_accessors() {
    let f = parse("2024-01-01 query \"income\" \"SELECT *\"\n");
    let Directive::Query(d) = single_directive(&f) else {
        panic!("expected Query");
    };
    assert_eq!(d.name().unwrap().text_unquoted().unwrap(), "income");
    assert_eq!(d.query().unwrap().text_unquoted().unwrap(), "SELECT *");
}

#[test]
fn note_directive_accessors() {
    let f = parse("2024-01-15 note Assets:Cash \"deposit\"\n");
    let Directive::Note(d) = single_directive(&f) else {
        panic!("expected Note");
    };
    assert_eq!(d.account().unwrap().text(), "Assets:Cash");
    assert_eq!(d.text().unwrap().text_unquoted().unwrap(), "deposit");
}

#[test]
fn document_directive_accessors() {
    let f = parse("2024-01-15 document Assets:Cash \"/path/file.pdf\"\n");
    let Directive::Document(d) = single_directive(&f) else {
        panic!("expected Document");
    };
    assert_eq!(d.account().unwrap().text(), "Assets:Cash");
    assert_eq!(d.path().unwrap().text_unquoted().unwrap(), "/path/file.pdf");
}

#[test]
fn price_directive_accessors() {
    let f = parse("2024-01-15 price USD 1.10 EUR\n");
    let Directive::Price(d) = single_directive(&f) else {
        panic!("expected Price");
    };
    assert_eq!(d.base_currency().unwrap().text(), "USD");
    assert_eq!(d.number().unwrap().text(), "1.10");
    assert_eq!(d.quote_currency().unwrap().text(), "EUR");
}

#[test]
fn commodity_directive_accessors() {
    let f = parse("2024-01-01 commodity HOOL\n");
    let Directive::Commodity(d) = single_directive(&f) else {
        panic!("expected Commodity");
    };
    assert_eq!(d.currency().unwrap().text(), "HOOL");
}

// ---- 4 standalone-keyword directives -----------------------------

#[test]
fn pushtag_directive_accessors() {
    let f = parse("pushtag #trip\n");
    let Directive::Pushtag(d) = single_directive(&f) else {
        panic!("expected Pushtag");
    };
    assert_eq!(d.tag().unwrap().text(), "#trip");
}

#[test]
fn poptag_directive_accessors() {
    let f = parse("poptag #trip\n");
    let Directive::Poptag(d) = single_directive(&f) else {
        panic!("expected Poptag");
    };
    assert_eq!(d.tag().unwrap().text(), "#trip");
}

#[test]
fn pushmeta_directive_accessors() {
    let f = parse("pushmeta location: \"Berlin\"\n");
    let Directive::Pushmeta(d) = single_directive(&f) else {
        panic!("expected Pushmeta");
    };
    assert_eq!(d.key().unwrap().text_without_colon(), "location");
}

#[test]
fn popmeta_directive_accessors() {
    let f = parse("popmeta location:\n");
    let Directive::Popmeta(d) = single_directive(&f) else {
        panic!("expected Popmeta");
    };
    assert_eq!(d.key().unwrap().text_without_colon(), "location");
}

// ---- 4 edge directives -------------------------------------------

#[test]
fn option_directive_accessors() {
    let f = parse("option \"title\" \"My Ledger\"\n");
    let Directive::Option(d) = single_directive(&f) else {
        panic!("expected Option");
    };
    assert_eq!(d.key().unwrap().text_unquoted().unwrap(), "title");
    assert_eq!(d.value().unwrap().text_unquoted().unwrap(), "My Ledger");
}

#[test]
fn include_directive_accessors() {
    let f = parse("include \"shared.beancount\"\n");
    let Directive::Include(d) = single_directive(&f) else {
        panic!("expected Include");
    };
    assert_eq!(
        d.path().unwrap().text_unquoted().unwrap(),
        "shared.beancount"
    );
}

#[test]
fn plugin_directive_accessors() {
    let f = parse("plugin \"my.plugin\" \"cfg\"\n");
    let Directive::Plugin(d) = single_directive(&f) else {
        panic!("expected Plugin");
    };
    assert_eq!(d.module().unwrap().text_unquoted().unwrap(), "my.plugin");
    assert_eq!(d.config().unwrap().text_unquoted().unwrap(), "cfg");
}

#[test]
fn custom_directive_accessors() {
    let f = parse("2024-01-01 custom \"budget\" \"food\" 500 USD\n");
    let Directive::Custom(d) = single_directive(&f) else {
        panic!("expected Custom");
    };
    assert_eq!(d.date().unwrap().text(), "2024-01-01");
    assert_eq!(d.custom_type().unwrap().text_unquoted().unwrap(), "budget");
}

// ---- TRANSACTION + POSTING + sub-structures ----------------------

#[test]
fn transaction_with_payee_narration_tags_links() {
    let f = parse(
        "2024-01-15 * \"Coffee Shop\" \"Morning coffee\" #daily ^trip1\n\
         \x20\x20Assets:Cash  -5.00 USD\n\
         \x20\x20Expenses:Food\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    assert_eq!(t.date().unwrap().text(), "2024-01-15");
    assert_eq!(t.flag().unwrap().text(), "*");
    assert_eq!(t.payee().unwrap().text_unquoted().unwrap(), "Coffee Shop");
    assert_eq!(
        t.narration().unwrap().text_unquoted().unwrap(),
        "Morning coffee"
    );
    let tags: Vec<String> = t.tags().map(|tg| tg.text().to_string()).collect();
    assert_eq!(tags, vec!["#daily"]);
    let links: Vec<String> = t.links().map(|l| l.text().to_string()).collect();
    assert_eq!(links, vec!["^trip1"]);
    assert_eq!(t.postings().count(), 2);
}

#[test]
fn transaction_with_narration_only_no_payee() {
    let f = parse("2024-01-15 * \"Coffee\"\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    assert!(t.payee().is_none());
    assert_eq!(t.narration().unwrap().text_unquoted().unwrap(), "Coffee");
}

#[test]
fn posting_accessors_basic() {
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  -5.00 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let p = t.postings().next().unwrap();
    assert!(p.flag().is_none());
    assert_eq!(p.account().unwrap().text(), "Assets:Cash");
    let amt = p.amount().unwrap();
    assert_eq!(amt.sign().unwrap().text(), "-");
    assert_eq!(amt.number().unwrap().text(), "5.00");
    assert_eq!(amt.currency().unwrap().text(), "USD");
}

#[test]
fn posting_with_flag() {
    let f = parse("2024-01-15 * \"x\"\n  ! Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let p = t.postings().next().unwrap();
    assert_eq!(p.flag().unwrap().text(), "!");
}

#[test]
fn posting_with_cost_and_price() {
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Inv  10 HOOL {500.00 USD} @ 510 USD\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let p = t.postings().next().unwrap();
    let cost = p.cost_spec().unwrap();
    assert!(!cost.is_total());
    assert!(!cost.is_per_unit_plus_total());
    assert_eq!(cost.number().unwrap().text(), "500.00");
    assert_eq!(cost.currency().unwrap().text(), "USD");

    let price = p.price_annotation().unwrap();
    assert!(!price.is_total());
    let inner = price.amount().unwrap();
    assert_eq!(inner.number().unwrap().text(), "510");
    assert_eq!(inner.currency().unwrap().text(), "USD");
}

#[test]
fn cost_spec_total_double_brace() {
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Inv  10 HOOL {{5000 USD, 2024-01-01, \"lot\"}}\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let cost = t.postings().next().unwrap().cost_spec().unwrap();
    assert!(cost.is_total());
    assert_eq!(cost.number().unwrap().text(), "5000");
    assert_eq!(cost.date().unwrap().text(), "2024-01-01");
    assert_eq!(cost.label().unwrap().text_unquoted().unwrap(), "lot");
}

#[test]
fn price_annotation_total_at_at() {
    let f = parse("2024-01-15 * \"x\"\n  Assets:Inv  10 HOOL @@ 5000 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let price = t.postings().next().unwrap().price_annotation().unwrap();
    assert!(price.is_total());
}

#[test]
fn amount_arithmetic_detected_and_currency_picked() {
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  100+5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    assert!(amt.is_arithmetic());
    // Leading number is the first NUMBER; currency is the trailing
    // CURRENCY (last one).
    assert_eq!(amt.number().unwrap().text(), "100");
    assert_eq!(amt.currency().unwrap().text(), "USD");
}

#[test]
fn meta_entry_typed_values() {
    let f = parse(
        "2024-01-01 open Assets:Cash\n\
         \x20\x20description: \"main\"\n\
         \x20\x20count: 42\n\
         \x20\x20since: 2024-01-01\n\
         \x20\x20active: TRUE\n\
         \x20\x20mirror: Assets:Mirror\n",
    );
    let dir = single_directive(&f);
    assert!(matches!(dir, Directive::Open(_)));
    let metas: Vec<_> = dir.meta_entries().collect();
    assert_eq!(metas.len(), 5);
    assert_eq!(metas[0].key().unwrap().text_without_colon(), "description");
    assert_eq!(
        metas[0].value_string().unwrap().text_unquoted().unwrap(),
        "main"
    );
    assert_eq!(metas[1].value_number().unwrap().text(), "42");
    assert_eq!(metas[2].value_date().unwrap().text(), "2024-01-01");
    assert!(metas[3].value_bool().unwrap());
    assert_eq!(metas[4].value_account().unwrap().text(), "Assets:Mirror");
}

// ---- ERROR_NODE --------------------------------------------------

#[test]
fn error_node_surfaces_through_typed_api() {
    let f = parse("bogus content here\n2024-01-01 open Assets:Cash\n");
    let errs: Vec<ErrorNode> = f.errors().collect();
    assert_eq!(errs.len(), 1);
    assert_eq!(errs[0].text(), "bogus content here\n");
    let ds: Vec<Directive> = f.directives().collect();
    assert_eq!(ds.len(), 1);
    assert!(matches!(ds[0], Directive::Open(_)));
}

// ---- AstNode / AstToken trait surface ----------------------------

#[test]
fn ast_node_cast_rejects_wrong_kind() {
    // Cast OPEN_DIRECTIVE node to CloseDirective — must return None.
    use rustledger_parser::cst::ast::{CloseDirective, OpenDirective};
    let f = parse("2024-01-01 open Assets:Cash\n");
    let Directive::Open(d) = single_directive(&f) else {
        unreachable!()
    };
    let node = d.syntax().clone();
    assert!(CloseDirective::cast(node.clone()).is_none());
    assert!(OpenDirective::cast(node).is_some());
}

#[test]
fn ast_token_cast_rejects_wrong_kind() {
    let f = parse("2024-01-01 open Assets:Cash\n");
    let Directive::Open(d) = single_directive(&f) else {
        unreachable!()
    };
    let acct_tok = d.account().unwrap().syntax().clone();
    assert!(Date::cast(acct_tok.clone()).is_none());
    assert!(Account::cast(acct_tok).is_some());
}

#[test]
fn string_lit_unquoted_handles_empty() {
    let f = parse("option \"\" \"\"\n");
    let Directive::Option(d) = single_directive(&f) else {
        unreachable!()
    };
    assert_eq!(d.key().unwrap().text_unquoted().unwrap(), "");
}

// Trait-import sanity: pull in everything from the public surface
// without using each (silences unused_imports without losing the
// re-export check).
#[test]
fn public_re_exports_exist() {
    fn t<T>() {}
    t::<BoolTrue>();
    t::<BoolFalse>();
    t::<CurrencyName>();
    t::<StringLit>();
    t::<Number>();
    t::<MetaKey>();
    t::<Tag>();
    t::<Link>();
    t::<CostSpec>();
    t::<PriceAnnotation>();
    t::<rustledger_parser::cst::ast::TransactionFlag>();
    t::<rustledger_parser::cst::ast::PostingFlag>();
    t::<rustledger_parser::cst::ast::Sign>();
}

// ---- Review-fix regressions --------------------------------------

#[test]
fn transaction_flag_recognizes_single_char_currency_letter() {
    // The ticker-letter transaction flag form (e.g. `T`). The CST
    // builder classifies single-char CURRENCY in the flag position
    // as a TRANSACTION; the typed accessor must surface it.
    let f = parse("2024-01-15 T \"AT&T dividend\"\n  Assets:Brokerage  10 T\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let flag = t.flag().expect("flag present");
    assert!(flag.is_currency_letter());
    assert_eq!(flag.text(), "T");
}

#[test]
fn transaction_flag_typed_discriminators() {
    let f = parse("2024-01-15 ! \"x\"\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let flag = t.flag().unwrap();
    assert!(flag.is_pending());
    assert!(!flag.is_star());
}

#[test]
fn posting_flag_typed_discriminators() {
    let f = parse("2024-01-15 * \"x\"\n  ! Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let p = t.postings().next().unwrap();
    let flag = p.flag().unwrap();
    assert!(flag.is_pending());
    assert_eq!(flag.text(), "!");
}

#[test]
fn amount_sign_typed_discriminators() {
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    let sign = amt.sign().unwrap();
    assert!(sign.is_minus());
    assert!(!sign.is_plus());
}

#[test]
fn cost_spec_is_merge_only_for_leading_star() {
    // `{*}` — leading STAR is a merge marker.
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Inv  10 HOOL {*}\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let cost = t.postings().next().unwrap().cost_spec().unwrap();
    assert!(cost.is_merge(), "leading STAR should be merge marker");
}

#[test]
fn cost_spec_is_not_merge_for_multiplication_star() {
    // `{500 * 2 USD}` — STAR is multiplication, NOT a merge
    // marker. This is the bug fixed in the review pass.
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Inv  10 HOOL {500 * 2 USD}\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let cost = t.postings().next().unwrap().cost_spec().unwrap();
    assert!(
        !cost.is_merge(),
        "multiplication * inside cost must not be classified as merge"
    );
}

#[test]
fn transaction_three_strings_payee_and_narration_return_none() {
    // 3+ strings is ambiguous; both accessors return None.
    // strings() exposes all three for lossless access.
    let f = parse("2024-01-15 * \"A\" \"B\" \"C\"\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    assert!(t.payee().is_none(), "3+ strings: payee ambiguous");
    assert!(t.narration().is_none(), "3+ strings: narration ambiguous");
    let all: Vec<String> = t
        .strings()
        .map(|s| s.text_unquoted().unwrap().to_string())
        .collect();
    assert_eq!(all, vec!["A", "B", "C"]);
}

#[test]
fn directive_implements_ast_node_trait() {
    use rustledger_parser::cst::SyntaxKind;
    // Generic over AstNode: confirms Directive participates in the
    // trait, not just its variant structs.
    fn syntax_kind_of<N: AstNode>(n: &N) -> SyntaxKind {
        n.syntax().kind()
    }
    let file = parse("2024-01-01 open Assets:Cash\n");
    let dir = single_directive(&file);
    assert_eq!(syntax_kind_of(&dir), SyntaxKind::OPEN_DIRECTIVE);
    // can_cast on the enum's trait
    assert!(Directive::can_cast(SyntaxKind::OPEN_DIRECTIVE));
    assert!(Directive::can_cast(SyntaxKind::TRANSACTION));
    assert!(!Directive::can_cast(SyntaxKind::POSTING));
}

#[test]
fn ast_token_text_is_borrowed_not_allocated() {
    // The trait method should return &str borrowed from the token,
    // confirming no per-call allocation. Compile-only check that
    // the return type is &str.
    let file = parse("2024-01-01 open Assets:Cash\n");
    let Directive::Open(open) = single_directive(&file) else {
        unreachable!()
    };
    let date = open.date().unwrap();
    let date_text: &str = date.text();
    assert_eq!(date_text, "2024-01-01");
    // text_unquoted returns Option<&str>
    let file2 = parse("option \"k\" \"v\"\n");
    let Directive::Option(opt) = single_directive(&file2) else {
        unreachable!()
    };
    let key = opt.key().unwrap();
    let key_text: &str = key.text_unquoted().unwrap();
    assert_eq!(key_text, "k");
    // text_without_colon returns &str
    let file3 = parse("pushmeta location:\n");
    let Directive::Pushmeta(pmeta) = single_directive(&file3) else {
        unreachable!()
    };
    let mkey = pmeta.key().unwrap();
    let stripped: &str = mkey.text_without_colon();
    assert_eq!(stripped, "location");
}

// ---- Round-2 review fixes ----------------------------------------

#[test]
fn transaction_strings_excludes_malformed_body_strings() {
    // emit_transaction_body's catch-all (parser.rs:396-401) emits
    // malformed indented body lines flat into TRANSACTION; their
    // STRING tokens would be siblings of the header STRING.
    // strings() / payee() / narration() must scope to the header
    // region (tokens before the first NEWLINE) and ignore body
    // strings.
    let f = parse(
        "2024-01-15 * \"header\"\n\
         \x20\x20\"stray body string\"\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let all: Vec<String> = t
        .strings()
        .map(|s| s.text_unquoted().unwrap().to_string())
        .collect();
    assert_eq!(all, vec!["header"]);
    assert!(t.payee().is_none());
    assert_eq!(t.narration().unwrap().text_unquoted().unwrap(), "header");
}

#[test]
fn transaction_flag_scoped_to_pre_string_region() {
    // A stray trailing single-char CURRENCY after the narration
    // STRING must NOT be misclassified as a ticker-letter flag.
    // The header is `DATE WS STRING WS CURRENCY NEWLINE`,
    // classified as TRANSACTION via the STRING-implied-flag arm.
    let f = parse("2024-01-15 \"narration\" T\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    assert!(
        t.flag().is_none(),
        "trailing stray CURRENCY 'T' must NOT be reported as a flag"
    );
    assert_eq!(t.narration().unwrap().text_unquoted().unwrap(), "narration");
}

#[test]
fn transaction_tags_links_excluded_from_body() {
    // Body tags/links (if any leak via catch-all) must not appear
    // in tags() / links() either.
    let f = parse(
        "2024-01-15 * \"x\" #header-tag ^header-link\n\
         \x20\x20#body-tag-stray\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let tags: Vec<String> = t.tags().map(|t| t.text().to_string()).collect();
    assert_eq!(tags, vec!["#header-tag"]);
    let links: Vec<String> = t.links().map(|l| l.text().to_string()).collect();
    assert_eq!(links, vec!["^header-link"]);
}

#[test]
fn amount_currency_unclosed_paren_returns_none() {
    // emit_amount_operand breaks on NEWLINE without emitting a
    // synthetic R_PAREN, so AMOUNT for `(1 USD\n` is
    // [L_PAREN, NUMBER, WS, CURRENCY] with unbalanced parens.
    // currency() must refuse rather than silently surface the
    // paren-internal USD.
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  (1 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    assert!(
        amt.currency().is_none(),
        "unclosed paren must yield None, not the inside-paren USD"
    );
}

#[test]
fn amount_currency_closed_paren_no_outer_currency_returns_none() {
    // `(10 + 5)` — closed paren with no trailing outer currency.
    // depth returns to 0 by end, but no CURRENCY was seen at
    // depth 0, so result is None.
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  (10 + 5)\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    assert!(amt.currency().is_none());
}

#[test]
fn amount_currency_paren_arithmetic_with_outer_currency() {
    // `(10 + 5) USD` — closed paren followed by outer USD.
    // Forward walk picks USD at depth 0.
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  (10 + 5) USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    assert_eq!(amt.currency().unwrap().text(), "USD");
}

#[test]
fn error_node_text_is_syntaxtext_zero_alloc() {
    // ErrorNode::text returns a rowan SyntaxText (rope view); the
    // implementation should not call to_string(). SyntaxText
    // impls PartialEq<&str>, so direct comparison still works.
    let f = parse("bogus content here\n2024-01-01 open Assets:Cash\n");
    let errs: Vec<ErrorNode> = f.errors().collect();
    assert_eq!(errs.len(), 1);
    let txt: rowan::SyntaxText = errs[0].text();
    assert_eq!(txt, "bogus content here\n");
    // Also verify Display works (LSP diagnostic path).
    assert_eq!(format!("{txt}"), "bogus content here\n");
}

#[test]
fn directive_enum_can_cast_and_cast_agree_for_every_kind() {
    // Pin lockstep between the macro-derived can_cast and cast.
    // If a contributor adds a Directive variant but forgets one
    // half of the match (which the macro now makes impossible),
    // this test catches the drift.
    use rustledger_parser::cst::SyntaxKind;
    let directive_kinds = [
        ("open", SyntaxKind::OPEN_DIRECTIVE),
        ("close", SyntaxKind::CLOSE_DIRECTIVE),
        ("balance", SyntaxKind::BALANCE_DIRECTIVE),
        ("pad", SyntaxKind::PAD_DIRECTIVE),
        ("event", SyntaxKind::EVENT_DIRECTIVE),
        ("query", SyntaxKind::QUERY_DIRECTIVE),
        ("note", SyntaxKind::NOTE_DIRECTIVE),
        ("document", SyntaxKind::DOCUMENT_DIRECTIVE),
        ("price", SyntaxKind::PRICE_DIRECTIVE),
        ("commodity", SyntaxKind::COMMODITY_DIRECTIVE),
        ("pushtag", SyntaxKind::PUSHTAG_DIRECTIVE),
        ("poptag", SyntaxKind::POPTAG_DIRECTIVE),
        ("pushmeta", SyntaxKind::PUSHMETA_DIRECTIVE),
        ("popmeta", SyntaxKind::POPMETA_DIRECTIVE),
        ("option", SyntaxKind::OPTION_DIRECTIVE),
        ("include", SyntaxKind::INCLUDE_DIRECTIVE),
        ("plugin", SyntaxKind::PLUGIN_DIRECTIVE),
        ("custom", SyntaxKind::CUSTOM_DIRECTIVE),
        ("transaction", SyntaxKind::TRANSACTION),
    ];
    for (name, kind) in directive_kinds {
        assert!(
            Directive::can_cast(kind),
            "can_cast must accept {name} ({kind:?})"
        );
    }
    // Negative cases — non-directive kinds must be rejected.
    for kind in [
        SyntaxKind::POSTING,
        SyntaxKind::AMOUNT,
        SyntaxKind::META_ENTRY,
        SyntaxKind::ERROR_NODE,
        SyntaxKind::SOURCE_FILE,
    ] {
        assert!(
            !Directive::can_cast(kind),
            "can_cast must reject non-directive {kind:?}"
        );
    }
}

#[test]
fn transaction_flag_classify_is_exhaustive() {
    use rustledger_parser::cst::ast::TransactionFlagKind;
    let f = parse("2024-01-15 ! \"x\"\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let flag = t.flag().unwrap();
    match flag.classify() {
        TransactionFlagKind::Pending => {} // expected
        other => panic!("expected Pending, got {other:?}"),
    }
}

#[test]
fn posting_flag_classify_is_exhaustive() {
    use rustledger_parser::cst::ast::PostingFlagKind;
    let f = parse("2024-01-15 * \"x\"\n  ! Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let p = t.postings().next().unwrap();
    let flag = p.flag().unwrap();
    match flag.classify() {
        PostingFlagKind::Pending => {} // expected
        other => panic!("expected Pending, got {other:?}"),
    }
}

#[test]
fn payee_narration_zero_strings_returns_none() {
    // Bareword `txn` keyword with no strings — header strings
    // count is 0; both accessors must return None.
    let f = parse("2024-01-15 txn\n  Assets:Cash  -5 USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    assert_eq!(t.strings().count(), 0);
    assert!(t.payee().is_none());
    assert!(t.narration().is_none());
}

// ---- Round-3 review fixes ----------------------------------------

#[test]
fn transaction_header_tokens_eof_without_newline() {
    // EOF-terminated transaction with no NEWLINE in the tree.
    // header_tokens (take_while != NEWLINE) walks ALL direct-child
    // tokens. Since there's no body, all tokens ARE header — the
    // accessors must still return the right answers, kind-filtered.
    let f = parse("2024-01-15 * \"Coffee\"");
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    assert_eq!(t.date().unwrap().text(), "2024-01-15");
    assert!(t.flag().unwrap().is_star());
    assert_eq!(t.narration().unwrap().text_unquoted().unwrap(), "Coffee");
    assert!(t.payee().is_none());
}

#[test]
fn amount_arithmetic_paren_contents_stay_flat_under_amount() {
    // Pin the structural invariant Amount::currency depends on:
    // emit_amount_operand keeps paren contents flat under AMOUNT,
    // so direct-token paren-depth tracking is sound. If a future
    // phase wraps parens in a PAREN_EXPR sub-node, currency()'s
    // depth tracking breaks silently — this test catches the
    // structural change.
    use rustledger_parser::cst::SyntaxKind;
    let f = parse("2024-01-15 * \"x\"\n  Assets:Cash  (10 + 5) USD\n");
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let amt = t.postings().next().unwrap().amount().unwrap();
    let has_node_children = amt
        .syntax()
        .children()
        .any(|n| n.kind() != SyntaxKind::AMOUNT);
    assert!(
        !has_node_children,
        "AMOUNT must keep paren contents as direct tokens, no sub-nodes"
    );
    // And the L_PAREN/R_PAREN tokens must be direct children:
    let token_kinds: Vec<SyntaxKind> = amt
        .syntax()
        .children_with_tokens()
        .filter_map(|el| el.into_token().map(|t| t.kind()))
        .collect();
    assert!(token_kinds.contains(&SyntaxKind::L_PAREN));
    assert!(token_kinds.contains(&SyntaxKind::R_PAREN));
}

#[test]
fn transaction_strings_excludes_catch_all_body_leak() {
    // Pin the round-2 body-pollution fix against the exact builder
    // shape that structured_directives.rs::catch_all_indented_
    // unknown_content_closes_posting_and_emits_flat exercises:
    // a stray indented STRING line between postings lands as a
    // flat direct child of TRANSACTION. strings()/payee()/
    // narration() must ignore it.
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Cash 1 USD\n\
         \x20\x20\"stray string on own line\"\n\
         \x20\x20Expenses:Food 1 USD\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        panic!("expected Transaction");
    };
    let all: Vec<String> = t
        .strings()
        .map(|s| s.text_unquoted().unwrap().to_string())
        .collect();
    assert_eq!(all, vec!["x"], "only the header string");
    assert_eq!(t.narration().unwrap().text_unquoted().unwrap(), "x");
    assert!(t.payee().is_none());
}

#[test]
fn cost_spec_per_unit_plus_total_positive() {
    // Positive test for is_per_unit_plus_total. Existing tests
    // only assert NOT-per-unit-plus-total for normal `{...}`
    // costs; this pins the `{# ... }` form.
    let f = parse(
        "2024-01-15 * \"x\"\n\
         \x20\x20Assets:Inv  10 HOOL {# 500.00 USD}\n",
    );
    let Directive::Transaction(t) = single_directive(&f) else {
        unreachable!()
    };
    let cost = t.postings().next().unwrap().cost_spec().unwrap();
    assert!(cost.is_per_unit_plus_total());
    assert!(!cost.is_total());
    assert!(!cost.is_merge());
}

#[test]
fn syntax_text_is_reexported_from_ast() {
    // Re-export sanity: ErrorNode::text returns SyntaxText, and
    // SyntaxText is reachable as rustledger_parser::cst::ast::
    // SyntaxText so downstream code doesn't need a direct rowan
    // dep.
    fn t<T>() {}
    t::<rustledger_parser::cst::ast::SyntaxText>();
}
