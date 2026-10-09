//! Transaction account sets across filtering, grouping and synthesised rows.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_query::executor::PostingContext;
use rustledger_query::{Executor, Value, parse};

fn fixture() -> Vec<Directive> {
    let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
    vec![
        Directive::Transaction(
            Transaction::new(date, "repeat")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(1), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(1), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-2), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(rustledger_core::naive_date(2024, 1, 10).unwrap(), "salary")
                .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(2), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-2), "USD"),
                )),
        ),
    ]
}

fn strings(names: &[&str]) -> Vec<Vec<Value>> {
    names
        .iter()
        .map(|name| vec![Value::String((*name).into())])
        .collect()
}

#[test]
fn test_account_sets_in_from_and_where_exclude_only_the_current_posting() {
    let directives = fixture();
    let mut executor = Executor::new(&directives);
    for sql in [
        "SELECT account FROM 'Expenses:Food' IN other_accounts",
        "SELECT account WHERE 'Expenses:Food' IN accounts",
        "SELECT account FROM 'Expenses:Food' IN other_accounts WHERE 'Assets:Bank' IN accounts",
    ] {
        assert_eq!(
            executor.execute(&parse(sql).unwrap()).unwrap().rows,
            strings(&["Expenses:Food", "Expenses:Food", "Assets:Bank"]),
            "{sql}"
        );
    }
}

#[test]
fn test_account_sets_in_grouping_having_and_hidden_ordering() {
    let directives = fixture();
    let mut executor = Executor::new(&directives);
    let grouped = executor
        .execute(&parse("SELECT accounts, count(*) GROUP BY accounts ORDER BY accounts").unwrap())
        .unwrap();
    assert_eq!(
        grouped.rows,
        vec![
            vec![
                Value::StringSet(vec!["Assets:Bank".into(), "Expenses:Food".into()]),
                Value::Integer(3)
            ],
            vec![
                Value::StringSet(vec!["Assets:Bank".into(), "Income:Salary".into()]),
                Value::Integer(2)
            ],
        ]
    );
    let having = executor
        .execute(
            &parse(
                "SELECT accounts, count(*) GROUP BY accounts HAVING 'Expenses:Food' IN accounts",
            )
            .unwrap(),
        )
        .unwrap();
    assert_eq!(
        having.rows,
        vec![vec![
            Value::StringSet(vec!["Assets:Bank".into(), "Expenses:Food".into()]),
            Value::Integer(3),
        ]]
    );

    let hidden = executor
        .execute(&parse("SELECT narration ORDER BY other_accounts, narration").unwrap())
        .unwrap();
    let visible = executor
        .execute(
            &parse("SELECT narration, other_accounts ORDER BY other_accounts, narration").unwrap(),
        )
        .unwrap();
    let expected: Vec<_> = visible
        .rows
        .into_iter()
        .map(|row| vec![row[0].clone()])
        .collect();
    assert_eq!(hidden.rows, expected);
}

#[test]
fn test_account_sets_in_windows_and_inner_subqueries() {
    let directives = fixture();
    let mut executor = Executor::new(&directives);
    let window = executor
        .execute(
            &parse(
                "SELECT account, row_number() OVER (PARTITION BY accounts ORDER BY account) \
         AS rn ORDER BY narration, account, rn",
            )
            .unwrap(),
        )
        .unwrap();
    assert_eq!(
        window.rows,
        vec![
            vec![Value::String("Assets:Bank".into()), Value::Integer(1)],
            vec![Value::String("Expenses:Food".into()), Value::Integer(2)],
            vec![Value::String("Expenses:Food".into()), Value::Integer(3)],
            vec![Value::String("Assets:Bank".into()), Value::Integer(1)],
            vec![Value::String("Income:Salary".into()), Value::Integer(2)],
        ]
    );
    let inner = executor
        .execute(
            &parse(
                "SELECT account FROM (SELECT account, other_accounts) \
         WHERE 'Expenses:Food' IN other_accounts",
            )
            .unwrap(),
        )
        .unwrap();
    assert_eq!(
        inner.rows,
        strings(&["Expenses:Food", "Expenses:Food", "Assets:Bank"])
    );
}

#[test]
fn test_synthesized_account_sets_do_not_survive_between_queries() {
    let directives = fixture();
    let mut executor = Executor::new(&directives);
    let original = executor
        .execute(&parse("SELECT account, accounts, other_accounts").unwrap())
        .unwrap();
    for date in ["2024-01-02", "2024-02-01"] {
        let result = executor
            .execute(
                &parse(&format!(
                    "SELECT account, accounts, other_accounts \
             FROM accounts IS NOT NULL AND other_accounts IS NOT NULL OPEN ON {date}"
                ))
                .unwrap(),
            )
            .unwrap();
        if date == "2024-01-02" {
            assert!(!result.rows.is_empty());
        }
        let unfiltered = executor
            .execute(
                &parse(&format!(
                    "SELECT account, accounts, other_accounts FROM OPEN ON {date}"
                ))
                .unwrap(),
            )
            .unwrap();
        assert_eq!(result.rows, unfiltered.rows, "OPEN ON {date}");
        assert_eq!(
            executor
                .execute(&parse("SELECT account, accounts, other_accounts").unwrap())
                .unwrap()
                .rows,
            original.rows
        );
    }
}

#[test]
fn test_parallel_account_set_projection_matches_one_thread() {
    let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
    let mut txn = Transaction::new(date, "parallel");
    for _ in 0..600 {
        txn = txn
            .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(-1), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(1), "USD")));
    }
    let directives = vec![Directive::Transaction(txn)];
    let query = parse("SELECT account, accounts, other_accounts").unwrap();
    let run = |threads| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(|| Executor::new(&directives).execute(&query).unwrap().rows)
    };
    let sequential = run(1);
    assert_eq!(sequential.len(), 1200);
    assert_eq!(run(4), sequential);
}

#[test]
fn test_public_posting_context_struct_literal_remains_valid() {
    let directives = fixture();
    let Directive::Transaction(txn) = &directives[0] else {
        panic!("expected transaction")
    };
    let context = PostingContext {
        transaction: txn.into(),
        posting_index: 0,
        balance: None,
        account_balance: None,
        directive_index: None,
    };
    assert_eq!(context.transaction.narration.as_ref(), "repeat");
}
