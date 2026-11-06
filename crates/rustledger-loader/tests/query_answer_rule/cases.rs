// The ledger shapes that pin the one rule for whether a query answers despite
// load errors (#2861): `LoadError::blocks_queries` and
// `LedgerError::blocks_queries`.
//
// Shared, through `include!`, by the drift-guard tests of every query surface:
//
// - `rustledger-loader/tests/query_answer_rule_test.rs` (the predicates),
// - `rustledger/tests/query_answer_rule_test.rs` (`rledger query`),
// - `rustledger-ffi-component` (`query-file`, `batch-file`,
//   `session.from-file`),
// - `rustledger-wasm/tests/wasm_query_sources.rs` (`queryMultiFile`,
//   `Ledger.fromFiles`).
//
// Each surface must answer or refuse exactly as `answers` says. The expected
// values are bean-query 0.2.0's (it answers in every case, reporting the load
// error), except for the parse and booking errors, where every rledger surface
// deliberately refuses (#1908, #1987).

/// One ledger: its files (path relative to a root, contents), the entry file,
/// and whether a query over it answers.
pub struct QueryRuleCase {
    /// What the ledger shows, named in a failing assertion.
    pub name: &'static str,
    /// The entry file, relative to the root.
    pub entry: &'static str,
    /// Every file: its path relative to the root, and its contents.
    pub files: &'static [(&'static str, &'static str)],
    /// Whether a query over the ledger answers (else it refuses).
    pub answers: bool,
}

/// The query each surface runs. It returns a row exactly when it answers:
/// every case's entry file holds a posting to `Assets:Cash`.
#[allow(dead_code)] // the predicate-level test runs no query
pub const QUERY_RULE_QUERY: &str = "SELECT narration FROM postings WHERE account = 'Assets:Cash'";

const BASE: &str = "2024-01-01 open Assets:Cash
2024-01-01 open Income:Salary
2024-01-02 * \"pay\"
  Assets:Cash  100 USD
  Income:Salary
";

const TXN: &str = "2024-01-06 * \"more\"
  Assets:Cash  7 USD
  Income:Salary
";

/// The ledgers, each with the answer every query surface must give.
pub const QUERY_RULE_CASES: &[QueryRuleCase] = &[
    QueryRuleCase {
        name: "clean",
        entry: "main.beancount",
        files: &[("main.beancount", BASE)],
        answers: true,
    },
    QueryRuleCase {
        name: "missing include",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "include \"nope.beancount\"\n",
                "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        answers: true,
    },
    QueryRuleCase {
        name: "include cycle",
        entry: "main.beancount",
        files: &[
            (
                "main.beancount",
                concat!(
                    "include \"a.beancount\"\n",
                    "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                    "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                ),
            ),
            ("a.beancount", "include \"main.beancount\"\n"),
        ],
        answers: true,
    },
    QueryRuleCase {
        name: "duplicate include",
        entry: "main.beancount",
        files: &[
            (
                "main.beancount",
                concat!(
                    "include \"a.beancount\"\ninclude \"a.beancount\"\n",
                    "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                    "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                ),
            ),
            ("a.beancount", TXN),
        ],
        answers: true,
    },
    QueryRuleCase {
        name: "empty glob",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "include \"none/*.beancount\"\n",
                "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        answers: true,
    },
    QueryRuleCase {
        name: "include outside the root",
        entry: "root/main.beancount",
        files: &[
            (
                "root/main.beancount",
                concat!(
                    "include \"../other.beancount\"\n",
                    "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                    "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                ),
            ),
            ("other.beancount", TXN),
        ],
        answers: true,
    },
    QueryRuleCase {
        name: "parse error",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                "2024-01-03 * \"bad\"\n  Assets:Cash  10 USD USD @@@\n  Income:Salary\n",
            ),
        )],
        answers: false,
    },
    QueryRuleCase {
        name: "booking error",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock \"STRICT\"\n",
                "2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"buy1\"\n  Assets:Stock  10 AAPL {100 USD}\n  Assets:Cash  -1000 USD\n",
                "2024-01-03 * \"buy2\"\n  Assets:Stock  10 AAPL {110 USD}\n  Assets:Cash  -1100 USD\n",
                "2024-01-05 * \"sell\"\n  Assets:Stock  -5 AAPL {}\n  Assets:Cash  500 USD\n  Income:Salary\n",
            ),
        )],
        answers: false,
    },
];
