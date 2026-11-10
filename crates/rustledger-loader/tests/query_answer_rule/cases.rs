// The ledger shapes that pin the rule for whether a query answers despite load
// errors (#2861, #2882): `LoadError::blocks_queries` and
// `LedgerError::blocks_queries`.
//
// Shared, through `include!`, by the drift-guard tests of every query surface:
//
// - `rustledger-loader/tests/query_answer_rule_test.rs` (the predicates),
// - `rustledger/tests/query_answer_rule_test.rs` (`rledger query`),
// - `rustledger-ffi-component` (`query-file`, `batch-file`,
//   `session.from-file`; and, from source text, `query`, `batch` and a
//   session from source),
// - `rustledger-wasm/tests/wasm_query_sources.rs` (`queryMultiFile`,
//   `Ledger.fromFiles`; and, from source text, `query` and
//   `ParsedLedger.query`).
//
// The MCP server's `query` tool is built on WASM `query`; its own tests
// (`packages/mcp-server`) cannot include this file, and repeat the
// source-text cases' answers.
//
// Each surface runs `QUERY_RULE_QUERY` and must return exactly `rows` (or
// refuse, for `None`), with `error` among the errors it reports. The expected
// values are bean-query 0.2.0's, except where noted: bean-query answers over a
// parse error and a booking error, dropping the entry, and every rledger
// surface deliberately refuses there (#1908, #1987); and bean-query does not
// confine includes, so the confined case is rledger's own.

/// Which surfaces a case applies to, by whether they confine includes to the
/// entry file's directory tree.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Confinement {
    /// Every surface.
    Any,
    /// Only a surface that confines includes (FFI `query-file`, `batch-file`,
    /// `session.from-file` without `allow-unrestricted-includes`).
    ConfinedOnly,
    /// Only a surface that does not (`rledger query`, WASM, an unrestricted
    /// FFI session, the loader's default).
    UnconfinedOnly,
}

/// One ledger and the answer every surface it applies to must give.
#[allow(dead_code)] // each surface reads the fields it needs
pub struct QueryRuleCase {
    /// What the ledger shows, named in a failing assertion.
    pub name: &'static str,
    /// The entry file, relative to the root.
    pub entry: &'static str,
    /// Every file: its path relative to the root, and its contents.
    pub files: &'static [(&'static str, &'static str)],
    /// The rows (`narration`, in date order) the query returns when it
    /// answers, or `None` when it refuses.
    pub rows: Option<&'static [&'static str]>,
    /// Text the reported errors must contain, if the case has a load error a
    /// surface can name the same way.
    pub error: Option<&'static str>,
    /// Which surfaces the case applies to.
    pub confinement: Confinement,
    /// Whether the case needs a real filesystem (a directory, a file to
    /// decrypt). WASM's in-memory filesystem has neither, so it skips these.
    pub disk_only: bool,
    /// Whether the source-text surfaces run the case too, the entry file's
    /// text passed as the source: only a case whose ledger is that one file
    /// and includes nothing. Source text has no files beside it to include:
    /// the FFI lists an `include` there unresolved and reports nothing, and
    /// WASM reports it as a missing file, so the include cases' answers are
    /// the file surfaces' alone.
    pub source_text: bool,
}

/// The query each surface runs: the narration of every posting to
/// `Assets:Cash`, in date order. Every case's entry file holds one, `pay`.
#[allow(dead_code)] // the predicate-level test runs no query
pub const QUERY_RULE_QUERY: &str =
    "SELECT narration FROM postings WHERE account = 'Assets:Cash' ORDER BY date";

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

/// `BASE`, as a literal for `concat!`.
macro_rules! base_ledger {
    () => {
        concat!(
            "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
            "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
        )
    };
}

/// `BASE` after the given `include` line(s).
macro_rules! with_include {
    ($include:literal) => {
        concat!(
            $include,
            "\n2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
            "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
        )
    };
}

/// The ledgers, each with the answer every query surface must give.
pub const QUERY_RULE_CASES: &[QueryRuleCase] = &[
    QueryRuleCase {
        name: "clean",
        entry: "main.beancount",
        files: &[("main.beancount", BASE)],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // bean-query: `File glob "nope.beancount" does not match any files`, then
    // the rows.
    QueryRuleCase {
        name: "include of a missing file",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            with_include!("include \"nope.beancount\""),
        )],
        rows: Some(&["pay"]),
        error: Some("nope.beancount"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: false,
    },
    // bean-query: `Duplicate filename parsed`, then the rows.
    QueryRuleCase {
        name: "include cycle",
        entry: "main.beancount",
        files: &[
            ("main.beancount", with_include!("include \"a.beancount\"")),
            ("a.beancount", "include \"main.beancount\"\n"),
        ],
        rows: Some(&["pay"]),
        error: Some("Duplicate filename parsed"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: false,
    },
    // bean-query: `Duplicate filename parsed`, then the rows, `more` once.
    QueryRuleCase {
        name: "duplicate include",
        entry: "main.beancount",
        files: &[
            (
                "main.beancount",
                with_include!("include \"a.beancount\"\ninclude \"a.beancount\""),
            ),
            ("a.beancount", TXN),
        ],
        rows: Some(&["pay", "more"]),
        error: Some("Duplicate filename parsed"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: false,
    },
    // bean-query: `File glob "none/*.beancount" does not match any files`,
    // then the rows.
    QueryRuleCase {
        name: "empty glob",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            with_include!("include \"none/*.beancount\""),
        )],
        rows: Some(&["pay"]),
        error: Some("none/*.beancount"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: false,
    },
    // Unconfined, the file outside the root is read, as bean-query reads it:
    // no error, its rows included.
    QueryRuleCase {
        name: "include outside the root, unconfined",
        entry: "root/main.beancount",
        files: &[
            (
                "root/main.beancount",
                with_include!("include \"../other.beancount\""),
            ),
            ("other.beancount", TXN),
        ],
        rows: Some(&["pay", "more"]),
        error: None,
        confinement: Confinement::UnconfinedOnly,
        disk_only: false,
        source_text: false,
    },
    // rledger's own: confined, the include is reported and left unread, and
    // the query answers without it. (bean-query does not confine.)
    QueryRuleCase {
        name: "include outside the root, confined",
        entry: "root/main.beancount",
        files: &[
            (
                "root/main.beancount",
                with_include!("include \"../other.beancount\""),
            ),
            ("other.beancount", TXN),
        ],
        rows: Some(&["pay"]),
        error: Some("path traversal"),
        confinement: Confinement::ConfinedOnly,
        disk_only: false,
        source_text: false,
    },
    // bean-query: an uncaught `IsADirectoryError`, exit 1, no rows.
    QueryRuleCase {
        name: "include naming a directory",
        entry: "main.beancount",
        files: &[
            ("main.beancount", with_include!("include \"sub\"")),
            ("sub/placeholder.txt", ""),
        ],
        rows: None,
        error: Some("sub"),
        confinement: Confinement::Any,
        disk_only: true,
        source_text: false,
    },
    // bean-query: an uncaught `OSError: Could not decrypt file`, exit 1, no
    // rows. (Garbage under a `.gpg` name: gpg fails, or is absent, and the
    // loader reports a decryption failure either way.)
    QueryRuleCase {
        name: "decryption failure",
        entry: "main.beancount",
        files: &[
            (
                "main.beancount",
                with_include!("include \"secret.beancount.gpg\""),
            ),
            ("secret.beancount.gpg", "not an encrypted file\n"),
        ],
        rows: None,
        error: Some("decrypt"),
        confinement: Confinement::Any,
        disk_only: true,
        source_text: false,
    },
    // bean-query answers, dropping the bad entry; rledger refuses (#1908).
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
        rows: None,
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // bean-query answers, dropping the sale; rledger refuses (#1987). Were
    // the gate gone, the rows would be `pay`, `buy1`, `buy2`, `sell`.
    QueryRuleCase {
        name: "booking error",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock \"STRICT\"\n",
                "2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                "2024-01-02 * \"buy1\"\n  Assets:Stock  10 AAPL {100 USD}\n  Assets:Cash  -1000 USD\n",
                "2024-01-03 * \"buy2\"\n  Assets:Stock  10 AAPL {110 USD}\n  Assets:Cash  -1100 USD\n",
                "2024-01-05 * \"sell\"\n  Assets:Stock  -5 AAPL {}\n  Assets:Cash  500 USD\n  Income:Salary\n",
            ),
        )],
        rows: None,
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // bean-query: `<check_commodity>:0: Missing Commodity directive for 'USD'
    // in 'Assets:Cash'`, then the rows. A plugin's error never stopped a
    // file query; the source-text surfaces refused over it before #2882.
    QueryRuleCase {
        name: "plugin error",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "plugin \"beancount.plugins.check_commodity\"\n",
                "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        rows: Some(&["pay"]),
        error: Some("Missing Commodity directive for 'USD' in 'Assets:Cash'"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // bean-query: `Error for option 'booking_method': 'fifo'`, then the rows,
    // booked STRICT. rledger refuses (#2911): beancount's `Booking[...]`
    // rejects the lowercase name, so the option keeps STRICT, and the figures
    // would be booked with a method the ledger did not ask for. Stricter than
    // Python, deliberately: see `Options::query_refusal`.
    QueryRuleCase {
        name: "invalid booking_method",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"booking_method\" \"fifo\"\n", base_ledger!()),
        )],
        rows: None,
        error: Some("booking_method"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // The same option, valid: answers.
    QueryRuleCase {
        name: "valid booking_method",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"booking_method\" \"FIFO\"\n", base_ledger!()),
        )],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // Any other rejected option keeps its default and answers, as in
    // bean-query: none of them changes which lots a sale consumes (#2911).
    QueryRuleCase {
        name: "invalid account_rounding",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"account_rounding\" \"bad:leaf\"\n", base_ledger!()),
        )],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // The last value wins: the accepted `FIFO` clears the rejected `fifo`, the
    // ledger books FIFO as it asks, and every surface answers, as bean-query does.
    QueryRuleCase {
        name: "booking_method fifo then FIFO",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"booking_method\" \"fifo\"\noption \"booking_method\" \"FIFO\"\n", base_ledger!()),
        )],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // The last value wins: the accepted `FIFO` clears the rejected `bogus`,
    // which names no method, so only that clearing lets it answer.
    QueryRuleCase {
        name: "booking_method bogus then FIFO",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!(
                "option \"booking_method\" \"bogus\"\noption \"booking_method\" \"FIFO\"\n",
                base_ledger!()
            ),
        )],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // `fifo` is rejected and `FIFO` kept, which is what `fifo` asks for read
    // case-insensitively: the booking is what the ledger asks, so it answers.
    QueryRuleCase {
        name: "booking_method FIFO then fifo",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"booking_method\" \"FIFO\"\noption \"booking_method\" \"fifo\"\n", base_ledger!()),
        )],
        rows: Some(&["pay"]),
        error: None,
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
    // `bogus` asks for no method, and the ledger books FIFO: it refuses.
    QueryRuleCase {
        name: "booking_method FIFO then bogus",
        entry: "main.beancount",
        files: &[(
            "main.beancount",
            concat!("option \"booking_method\" \"FIFO\"\noption \"booking_method\" \"bogus\"\n", base_ledger!()),
        )],
        rows: None,
        error: Some("booking_method"),
        confinement: Confinement::Any,
        disk_only: false,
        source_text: true,
    },
];
