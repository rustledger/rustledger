// The ledgers that pin what the FFI component's `load`, `load-file`,
// `validate` and `validate-file` report against what `rledger check` reports
// for the same ledger (#2929, #2935): every diagnostic's code, severity,
// message, file and line.
//
// Shared, through `include!`, by:
//
// - `rustledger/tests/ffi_check_parity_test.rs` (`rledger check --format
//   json`),
// - `rustledger-ffi-component` (the four surfaces natively, and the
//   `rustledger-ffi-wasi` errors they are built from, which carry the code and
//   file the WIT `error` record has no field for),
// - `rustledger-ffi-component-tests/tests/parity.rs` (the four surfaces through
//   the built wasip2 component).
//
// Each side must report exactly `diagnostics`, so a change on either side
// trips its own test against this one list.
//
// A diagnostic with no location (`file` and `line` are `None`, such as a
// plugin that could not be resolved) is printed by `rledger check` at the
// entry file's line 1, its JSON's stand-in for "no location"; the FFI reports
// no file and no line. Every option diagnostic has its option's location
// (#2925).
//
// Each case also closes an account with a balance, the advisory-only E1004
// that `rledger check` leaves out (bean-check does not flag it): no surface
// may report it.

/// One diagnostic as every surface must report it.
#[allow(dead_code)]
#[derive(Clone, Copy)]
pub struct ExpectedDiagnostic {
    /// The diagnostic code (`E2001`).
    pub code: &'static str,
    /// `error` or `warning`.
    pub severity: &'static str,
    /// The file, relative to the case's directory; `None` for no location.
    pub file: Option<&'static str>,
    /// The 1-based line in `file`; `None` for no location.
    pub line: Option<u32>,
    /// The message, exactly.
    pub message: &'static str,
}

/// A ledger and what it must report.
#[allow(dead_code)]
pub struct CheckParityCase {
    /// Named in assertion messages.
    pub name: &'static str,
    /// `(path, text)`, relative to the case's directory.
    pub files: &'static [(&'static str, &'static str)],
    /// The file to load, among `files`.
    pub entry: &'static str,
    /// Exactly what every surface reports, in any order.
    pub diagnostics: &'static [ExpectedDiagnostic],
}

#[allow(dead_code)]
impl CheckParityCase {
    /// Whether the case is one file, so the source-text surfaces (`load`,
    /// `validate`) can run it too: they do not resolve includes.
    pub const fn is_single_file(&self) -> bool {
        self.files.len() == 1
    }

    /// The entry file's text.
    pub fn entry_text(&self) -> &'static str {
        self.files
            .iter()
            .find(|(path, _)| *path == self.entry)
            .map(|(_, text)| *text)
            .expect("the entry is among the files")
    }
}

/// The option diagnostics both ledgers raise, at their options' lines in
/// `main.beancount`: a rejected
/// `booking_method` (whose ledger is then booked STRICT, so a query refuses,
/// #2911), a rejected `name_equity`, and a duplicate `title` (a warning).
#[allow(dead_code)]
const OPTION_DIAGNOSTICS: [ExpectedDiagnostic; 3] = [
    ExpectedDiagnostic {
        code: "E7002",
        severity: "error",
        file: Some("main.beancount"),
        line: Some(2),
        message: "Invalid value \"fifo\" for option \"booking_method\": expected one of \
                  STRICT, STRICT_WITH_SIZE, FIFO, LIFO, HIFO, AVERAGE, NONE",
    },
    ExpectedDiagnostic {
        code: "E7008",
        severity: "error",
        file: Some("main.beancount"),
        line: Some(3),
        message: "Invalid account type name: 'x' cannot begin an account name, so the \
                  option keeps its previous value",
    },
    ExpectedDiagnostic {
        code: "E7003",
        severity: "warning",
        file: Some("main.beancount"),
        line: Some(5),
        message: DUPLICATE_TITLE,
    },
];

#[allow(dead_code)]
const DUPLICATE_TITLE: &str = "Option \"title\" is set more than once; the last value wins";

#[allow(dead_code)]
const PAD_WITH_COST: &str =
    "Attempt to pad an entry with cost for balance: (10 HOOL {5 USD, 2024-01-02})";

#[allow(dead_code)]
const BALANCE_FAILED: &str = "Balance failed for Assets:Bank: expected 100 USD, got -50 USD";

/// The cases every surface runs.
#[allow(dead_code)]
pub const CHECK_PARITY_CASES: &[CheckParityCase] = &[
    CheckParityCase {
        name: "multi-file",
        files: &[
            (
                "main.beancount",
                "option \"operating_currency\" \"USD\"\n\
                 option \"booking_method\" \"fifo\"\n\
                 option \"name_equity\" \"x\"\n\
                 option \"title\" \"A\"\n\
                 option \"title\" \"B\"\n\
                 include \"accounts.beancount\"\n\
                 \n\
                 2024-01-02 * \"buy\"\n  \
                   Assets:Brokerage  10 HOOL {5 USD}\n  \
                   Assets:Bank      -50 USD\n\
                 \n\
                 2024-01-03 pad Assets:Brokerage Equity:Opening-Balances\n\
                 2024-01-04 balance Assets:Brokerage 12 HOOL\n",
            ),
            (
                "accounts.beancount",
                "2024-01-01 open Assets:Bank USD\n\
                 2024-01-01 open Assets:Brokerage\n\
                 2024-01-01 open Equity:Opening-Balances\n\
                 \n\
                 2024-01-05 balance Assets:Bank 100 USD\n\
                 2024-01-06 close Assets:Bank\n",
            ),
        ],
        entry: "main.beancount",
        diagnostics: &[
            OPTION_DIAGNOSTICS[0],
            OPTION_DIAGNOSTICS[1],
            OPTION_DIAGNOSTICS[2],
            ExpectedDiagnostic {
                code: "E2005",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(13),
                message: PAD_WITH_COST,
            },
            // In the included file, at its line there: the line alone would
            // name a line of the entry file.
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("accounts.beancount"),
                line: Some(5),
                message: BALANCE_FAILED,
            },
        ],
    },
    CheckParityCase {
        name: "single-file",
        files: &[(
            "main.beancount",
            "option \"operating_currency\" \"USD\"\n\
             option \"booking_method\" \"fifo\"\n\
             option \"name_equity\" \"x\"\n\
             option \"title\" \"A\"\n\
             option \"title\" \"B\"\n\
             2024-01-01 open Assets:Bank USD\n\
             2024-01-01 open Assets:Brokerage\n\
             2024-01-01 open Equity:Opening-Balances\n\
             \n\
             2024-01-02 * \"buy\"\n  \
               Assets:Brokerage  10 HOOL {5 USD}\n  \
               Assets:Bank      -50 USD\n\
             \n\
             2024-01-03 pad Assets:Brokerage Equity:Opening-Balances\n\
             2024-01-04 balance Assets:Brokerage 12 HOOL\n\
             2024-01-05 balance Assets:Bank 100 USD\n\
             2024-01-06 close Assets:Bank\n",
        )],
        entry: "main.beancount",
        diagnostics: &[
            OPTION_DIAGNOSTICS[0],
            OPTION_DIAGNOSTICS[1],
            OPTION_DIAGNOSTICS[2],
            ExpectedDiagnostic {
                code: "E2005",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(15),
                message: PAD_WITH_COST,
            },
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(16),
                message: BALANCE_FAILED,
            },
        ],
    },
    // A declared plugin that is not run: `rledger check` still validates,
    // and reports an account the plugin might have opened as E1001 beside the
    // plugin error, and so does every FFI surface. Unresolved here (E8001),
    // which every build reports alike; a Python plugin the component cannot
    // run (E8005, or E8004 by module name) takes the same path, pinned in the
    // component's own tests.
    CheckParityCase {
        name: "unresolved-plugin",
        files: &[(
            "main.beancount",
            "plugin \"no_such_plugin\"\n\
             \n\
             2024-01-02 * \"x\"\n  \
               Assets:A  10 USD\n  \
               Income:X\n",
        )],
        entry: "main.beancount",
        diagnostics: &[
            ExpectedDiagnostic {
                code: "E8001",
                severity: "error",
                file: None,
                line: None,
                message: "Plugin not found: \"no_such_plugin\"",
            },
            ExpectedDiagnostic {
                code: "E1001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                message: "Account Assets:A was never opened",
            },
            ExpectedDiagnostic {
                code: "E1001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                message: "Account Income:X was never opened",
            },
        ],
    },
];
