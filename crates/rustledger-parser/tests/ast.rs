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
    let curs: Vec<String> = d.currencies().map(|c| c.text()).collect();
    assert_eq!(curs, vec!["USD", "EUR"]);
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
    let tags: Vec<String> = t.tags().map(|tg| tg.text()).collect();
    assert_eq!(tags, vec!["#daily"]);
    let links: Vec<String> = t.links().map(|l| l.text()).collect();
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
    matches!(ds[0], Directive::Open(_));
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
}
