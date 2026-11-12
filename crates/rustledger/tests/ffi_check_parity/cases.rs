// The ledgers that pin what the FFI component's `load`, `load-file`,
// `validate` and `validate-file` report against what `rledger check` reports
// for the same ledger (#2929, #2935): every diagnostic's code, severity,
// message, file, line and column.
//
// Shared, through `include!`, by:
//
// - `rustledger/tests/ffi_check_parity_test.rs` (`rledger check --format
//   json`),
// - `rustledger-ffi-component` (the four surfaces natively, on the WIT
//   `error` record itself, which carries `code` and `filename` since 4.0.0),
// - `rustledger-ffi-component-tests/tests/parity.rs` (the four surfaces through
//   the built wasip2 component).
//
// Each side must report exactly `diagnostics`, so a change on either side
// trips its own test against this one list.
//
// A diagnostic with no location (`file`, `line` and `column` are `None`, such
// as a plugin that could not be resolved) is printed by `rledger check` at the
// entry file's line 1, column 1, its JSON's stand-in for "no location"; the
// FFI reports no file, no line and no column. Every option diagnostic has its
// option's location (#2925).
//
// The option cases also close an account with a balance, the advisory-only E1004
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
    /// The 1-based column on `line`; `None` for no location.
    pub column: Option<u32>,
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

    /// The `parse-error-count` and `validate-error-count` a `validate` of the
    /// case gives: its `P` codes are parse errors; its option diagnostics are
    /// counted in neither (#2929); every other is a validate-phase one.
    pub fn counts(&self) -> (u32, u32) {
        let parse = self.diagnostics.iter().filter(|d| d.code.starts_with('P')).count();
        let options = self.diagnostics.iter().filter(|d| d.code.starts_with("E70")).count();
        let parse = u32::try_from(parse).expect("small");
        let rest = u32::try_from(self.diagnostics.len() - options).expect("small") - parse;
        (parse, rest)
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
        column: Some(1),
        message: "Invalid value \"fifo\" for option \"booking_method\": expected one of \
                  STRICT, STRICT_WITH_SIZE, FIFO, LIFO, HIFO, AVERAGE, NONE",
    },
    ExpectedDiagnostic {
        code: "E7008",
        severity: "error",
        file: Some("main.beancount"),
        line: Some(3),
        column: Some(1),
        message: "Invalid account type name: 'x' cannot begin an account name, so the \
                  option keeps its previous value",
    },
    ExpectedDiagnostic {
        code: "E7003",
        severity: "warning",
        file: Some("main.beancount"),
        line: Some(5),
        column: Some(1),
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
                column: Some(1),
                message: PAD_WITH_COST,
            },
            // In the included file, at its line there: the line alone would
            // name a line of the entry file.
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("accounts.beancount"),
                line: Some(5),
                column: Some(1),
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
                column: Some(1),
                message: PAD_WITH_COST,
            },
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(16),
                column: Some(1),
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
                column: None,
                message: "Plugin not found: \"no_such_plugin\"",
            },
            ExpectedDiagnostic {
                code: "E1001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                column: Some(1),
                message: "Account Assets:A was never opened",
            },
            ExpectedDiagnostic {
                code: "E1001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                column: Some(1),
                message: "Account Income:X was never opened",
            },
        ],
    },
    // A parse error in an included file: reported at its own file, line and
    // column with its code (`P0012`), not as one line-less `parse errors in
    // <path>`, and the entries that did parse are still validated, as
    // `rledger check` does (review of #2946).
    CheckParityCase {
        name: "parse-error-in-include",
        files: &[
            (
                "main.beancount",
                "include \"inc.beancount\"\n\
                 2024-01-01 open Assets:A\n\
                 2024-01-05 balance Assets:A 1 USD\n",
            ),
            (
                "inc.beancount",
                "2024-01-01 open Assets:B\n\
                 \n\
                 2024-01-03 open\n\
                 2024-01-03 open Assets:Ü 10\n\
                 2024-01-04 * \"x\"\n  \
                   Assets:B  10 USD\n  \
                   Assets:A\n",
            ),
        ],
        entry: "main.beancount",
        diagnostics: &[
            ExpectedDiagnostic {
                code: "P0012",
                severity: "error",
                file: Some("inc.beancount"),
                line: Some(3),
                column: Some(1),
                message: "parse error: unexpected input",
            },
            // Its column counts characters, not bytes, as `check` counts them:
            // the `Ü` before it is two bytes.
            ExpectedDiagnostic {
                code: "P0012",
                severity: "error",
                file: Some("inc.beancount"),
                line: Some(4),
                column: Some(26),
                message: "parse error: unexpected \"10\" in the open directive: expected the \
                          end of the line",
            },
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                column: Some(1),
                message: "Balance failed for Assets:A: expected 1 USD, got -10 USD",
            },
        ],
    },
    // A parse error in a single file: the source-text surfaces (`load`,
    // `validate`) run it too. The entries that did parse are still validated
    // (#2949), so the balance after the bad line fails, as `check` reports.
    CheckParityCase {
        name: "parse-error-single-file",
        files: &[(
            "main.beancount",
            "2024-01-01 open Assets:A\n\
             2024-01-03 open\n\
             2024-01-05 balance Assets:A 1 USD\n",
        )],
        entry: "main.beancount",
        diagnostics: &[
            ExpectedDiagnostic {
                code: "P0012",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(2),
                column: Some(1),
                message: "parse error: unexpected input",
            },
            ExpectedDiagnostic {
                code: "E2001",
                severity: "error",
                file: Some("main.beancount"),
                line: Some(3),
                column: Some(1),
                message: "Balance failed for Assets:A: expected 1 USD, got 0 USD",
            },
        ],
    },
    // A BOM before line 1: three bytes, one character, so a finding there is
    // at column 2, as `check` counts it. Every other case's columns are 1, so
    // a surface that set the column to 1 (or counted bytes, 4) passed them
    // (review of #2946).
    CheckParityCase {
        name: "bom",
        files: &[(
            "main.beancount",
            "\u{FEFF}2024-01-02 balance Assets:X 1 USD\n\
             2024-01-01 open Assets:Y\n",
        )],
        entry: "main.beancount",
        diagnostics: &BOM_DIAGNOSTICS,
    },
    // The same with CRLF line endings.
    CheckParityCase {
        name: "bom-crlf",
        files: &[(
            "main.beancount",
            "\u{FEFF}2024-01-02 balance Assets:X 1 USD\r\n\
             2024-01-01 open Assets:Y\r\n",
        )],
        entry: "main.beancount",
        diagnostics: &BOM_DIAGNOSTICS,
    },
];

/// What the `bom` cases report: both findings on line 1, at column 2.
#[allow(dead_code)]
const BOM_DIAGNOSTICS: [ExpectedDiagnostic; 2] = [
    ExpectedDiagnostic {
        code: "E1001",
        severity: "error",
        file: Some("main.beancount"),
        line: Some(1),
        column: Some(2),
        message: "Account Assets:X was never opened",
    },
    ExpectedDiagnostic {
        code: "E2001",
        severity: "error",
        file: Some("main.beancount"),
        line: Some(1),
        column: Some(2),
        message: "Balance failed for Assets:X: expected 1 USD, got 0 USD",
    },
];
