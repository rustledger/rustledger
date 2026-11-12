// Ledgers on which every query surface must list the same errors for a query
// (#2911, #2929): the option diagnostics as a query lists them, through the
// canonical `rustledger_loader::Ledger::query_option_errors`, in which a
// rejected `booking_method`'s E7002 is the refusal that says why the query
// does not answer.
//
// Shared, through `include!`, by the drift-guard test of each surface:
//
// - `rustledger-loader/tests/query_option_errors_test.rs` (the canonical
//   itself),
// - `rustledger-ffi-component` (`query`, `session.query` from source,
//   `query-file`, `session.query` from a file),
// - `rustledger-wasm/tests/wasm_query_option_errors.rs` (`query`,
//   `ParsedLedger.query`, `queryMultiFile`, `Ledger.query`, the last two
//   restored from cache too).
//
// Each surface must list exactly `errors`, in order: code, message, file and
// line, the parse errors a query lists before them (`parse_errors`) too.
// WASM's free `query` listed the plain E7002 where the refusal belongs,
// `queryMultiFile` the refusal alone and no other option diagnostic, and
// `ParsedLedger.query` and `Ledger.query` the plain E7002 (review of #2946).

/// One error a query must list.
#[allow(dead_code)] // each surface reads the fields it needs
pub struct QueryError {
    /// The diagnostic code (`E7002`).
    pub code: &'static str,
    /// The message, exactly, with `{main}` for the name the surface gives the
    /// entry file in it (`<string>` for source text).
    pub message: &'static str,
    /// The file, relative to the case's directory; `MAIN` for the entry file,
    /// which a source-text surface names its own way.
    pub file: &'static str,
    /// The 1-based line.
    pub line: u32,
}

/// The entry file's name in `QueryError::file`.
#[allow(dead_code)]
pub const MAIN: &str = "main.beancount";

/// One ledger and what a query over it must list.
#[allow(dead_code)]
pub struct QueryOptionCase {
    /// Named in assertion messages.
    pub name: &'static str,
    /// `(path, text)`, relative to the case's directory; the first is the
    /// entry, `MAIN`.
    pub files: &'static [(&'static str, &'static str)],
    /// Whether the query answers (has rows) or refuses.
    pub answers: bool,
    /// The parse errors a query lists, before `errors`: they are not
    /// option diagnostics, so the canonical's side leaves them out
    /// ([`Self::expected_option_errors`]).
    pub parse_errors: &'static [QueryError],
    /// Exactly what every query surface lists, in order.
    pub errors: &'static [QueryError],
}

#[allow(dead_code)]
impl QueryOptionCase {
    /// Whether the case is one file, so the source-text surfaces can run it
    /// too: they do not resolve includes.
    pub const fn is_single_file(&self) -> bool {
        self.files.len() == 1
    }

    /// The entry file's text.
    pub const fn entry_text(&self) -> &'static str {
        self.files[0].1
    }

    /// What a query surface lists, `parse_errors` then `errors`, as
    /// `(code, message, file, line)` rows, the entry file named `entry_as`
    /// (`None` where a surface names no file) and named `main_in_message` in
    /// the messages.
    pub fn expected(
        &self,
        entry_as: Option<&str>,
        main_in_message: &str,
    ) -> Vec<(String, String, Option<String>, Option<u32>)> {
        Self::rows(
            self.parse_errors.iter().chain(self.errors),
            entry_as,
            main_in_message,
        )
    }

    /// `errors` alone, as [`Self::expected`] gives them: what the canonical
    /// `Ledger::query_option_errors` lists.
    pub fn expected_option_errors(
        &self,
        entry_as: Option<&str>,
        main_in_message: &str,
    ) -> Vec<(String, String, Option<String>, Option<u32>)> {
        Self::rows(self.errors, entry_as, main_in_message)
    }

    fn rows<'a>(
        errors: impl IntoIterator<Item = &'a QueryError>,
        entry_as: Option<&str>,
        main_in_message: &str,
    ) -> Vec<(String, String, Option<String>, Option<u32>)> {
        errors
            .into_iter()
            .map(|e| {
                (
                    e.code.to_string(),
                    e.message.replace("{main}", main_in_message),
                    if e.file == MAIN {
                        entry_as.map(str::to_string)
                    } else {
                        Some(e.file.to_string())
                    },
                    Some(e.line),
                )
            })
            .collect()
    }
}

/// The query every surface runs.
#[allow(dead_code)]
pub const QUERY: &str = "SELECT narration";

#[allow(dead_code)]
const REFUSAL: &str = "option \"booking_method\" at {main}:1: \"fifo\" is not a booking \
     method (E7002); refusing to derive figures, which would be booked with STRICT";

#[allow(dead_code)]
const INVALID_FIFO: &str = "Invalid value \"fifo\" for option \"booking_method\": expected one \
     of STRICT, STRICT_WITH_SIZE, FIFO, LIFO, HIFO, AVERAGE, NONE";

/// The cases every query surface runs.
#[allow(dead_code)]
pub const QUERY_OPTION_CASES: &[QueryOptionCase] = &[
    // The rejected `booking_method` refuses the query: the refusal is listed
    // in its E7002's place, once.
    QueryOptionCase {
        name: "refused-booking-method",
        files: &[(
            MAIN,
            concat!(
                "option \"booking_method\" \"fifo\"\n",
                "2024-01-01 open Assets:Cash\n",
                "2024-01-01 open Income:Salary\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        answers: false,
        parse_errors: &[],
        errors: &[QueryError {
            code: "E7002",
            message: REFUSAL,
            file: MAIN,
            line: 1,
        }],
    },
    // The same option in an included file: an include's options are not
    // applied, so nothing refuses, and its E7002 is listed at its own file
    // and line.
    QueryOptionCase {
        name: "invalid-option-in-include",
        files: &[
            (
                MAIN,
                concat!(
                    "include \"inc.beancount\"\n",
                    "2024-01-01 open Assets:Cash\n",
                    "2024-01-01 open Income:Salary\n",
                    "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                ),
            ),
            ("inc.beancount", "option \"booking_method\" \"fifo\"\n"),
        ],
        answers: true,
        parse_errors: &[],
        errors: &[QueryError {
            code: "E7002",
            message: INVALID_FIFO,
            file: "inc.beancount",
            line: 1,
        }],
    },
    // Both: the refusal is at the main file's option, and the include's
    // E7002 is listed as it is.
    QueryOptionCase {
        name: "refused-in-main-and-include",
        files: &[
            (
                MAIN,
                concat!(
                    "option \"booking_method\" \"fifo\"\n",
                    "include \"inc.beancount\"\n",
                    "2024-01-01 open Assets:Cash\n",
                    "2024-01-01 open Income:Salary\n",
                    "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
                ),
            ),
            ("inc.beancount", "option \"booking_method\" \"fifo\"\n"),
        ],
        answers: false,
        parse_errors: &[],
        errors: &[
            QueryError {
                code: "E7002",
                message: REFUSAL,
                file: MAIN,
                line: 1,
            },
            QueryError {
                code: "E7002",
                message: INVALID_FIFO,
                file: "inc.beancount",
                line: 1,
            },
        ],
    },
    // A refused `booking_method` in a source that also fails to parse. The
    // load goes on past the parse error (#2949), so a query lists the parse
    // error first and then the refusal, as on a source that parses. Not run
    // through WASM `queryMultiFile`, which refuses on a parse error before a
    // `Ledger` exists and lists no option diagnostic (issue #2960).
    QueryOptionCase {
        name: "refused-booking-method-with-parse-error",
        files: &[(
            MAIN,
            concat!(
                "option \"booking_method\" \"fifo\"\n",
                "2024-01-01 open Assets:Cash\n",
                "2024-01-01 open Income:Salary\n",
                "2024-01-03 open\n",
                "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        answers: false,
        parse_errors: &[QueryError {
            code: "P0012",
            message: "parse error: unexpected input",
            file: MAIN,
            line: 4,
        }],
        errors: &[QueryError {
            code: "E7002",
            message: REFUSAL,
            file: MAIN,
            line: 1,
        }],
    },
    // A parse error and no option diagnostic: the parse error alone refuses
    // the query, though the entries that did parse would give rows (review
    // of #2946). WASM `queryMultiFile` runs it too: it refuses on a parse
    // error before a `Ledger` exists, but there are no option diagnostics to
    // miss (issue #2960).
    QueryOptionCase {
        name: "refused-by-parse-error-alone",
        files: &[(
            MAIN,
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-01 open Income:Salary\n",
                "2024-01-03 open\n",
                "2024-01-04 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
            ),
        )],
        answers: false,
        parse_errors: &[QueryError {
            code: "P0012",
            message: "parse error: unexpected input",
            file: MAIN,
            line: 3,
        }],
        errors: &[],
    },
];
