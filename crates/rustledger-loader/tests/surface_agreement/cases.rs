// Ledgers on which every diagnostic surface must report the same findings
// (#2937): `rledger check`, WASM (`validateSource`, `ParsedLedger`,
// `Ledger.fromFiles`), the FFI component (`validate`, `load`, `validate-file`,
// `load-file`) and the LSP.
//
// Shared, through `include!`, by the drift-guard test of each surface:
//
// - `rustledger/tests/surface_agreement_test.rs` (`rledger check --format json`),
// - `rustledger-wasm/tests/wasm_surface_agreement.rs` (`validateSource`,
//   `ParsedLedger`, `Ledger.fromFiles`, the last two also from cache),
// - `rustledger-ffi-component` (`validate`, `load`, `validate-file`,
//   `load-file`),
// - `rustledger-lsp` (`all_diagnostics`).
//
// Each surface must report exactly `findings`, in any order: the same code,
// on the same 1-based line, with a message starting with the given text.
// The expected findings are bean-check 3.2.3's:
//
// - bean-check does not flag closing an account that still holds a balance,
//   with or without `auto_accounts` / `currency_accounts`; `check` stays
//   silent on E1004 to match it, and `rledger lint closed-nonempty` reports
//   it (`ErrorCode::is_advisory_only`). The FFI, WASM and LSP reported it.
// - bean-check reports an ambiguous STRICT reduction AND the balance
//   assertion that fails after it, the refused transaction left out of the
//   balance (`-2100 USD`). WASM skipped validation after the booking error.
//   (bean-check places the booking error on the transaction's line, 14;
//   every rledger surface places it on the posting's, 15, #2330.)

/// One finding every surface must report.
#[allow(dead_code)] // each surface reads the fields it needs
pub struct Finding {
    /// The diagnostic code (`E2001`, ...).
    pub code: &'static str,
    /// The 1-based line it is reported on.
    pub line: u32,
    /// The start of its message.
    pub message: &'static str,
}

/// One ledger and the findings every surface must report for it.
#[allow(dead_code)] // each surface reads the fields it needs
pub struct SurfaceCase {
    /// What the ledger shows, named in a failing assertion.
    pub name: &'static str,
    /// The ledger's text.
    pub source: &'static str,
    /// Exactly the findings reported, in any order.
    pub findings: &'static [Finding],
    /// Whether the ledger closes an account with a balance, which the
    /// validator raises (E1004) and no surface reports: `rledger lint
    /// closed-nonempty` must find it, so the case is not passing vacuously.
    pub closes_nonempty: bool,
}

/// The cases.
#[allow(dead_code)] // not every including test runs every case
pub const SURFACE_CASES: &[SurfaceCase] = &[
    SurfaceCase {
        name: "close with a balance",
        source: "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening

2024-01-02 * \"fund\"
  Assets:Bank      100 USD
  Equity:Opening

2024-02-01 close Assets:Bank
",
        findings: &[],
        closes_nonempty: true,
    },
    SurfaceCase {
        name: "close with a balance under auto_accounts",
        source: "plugin \"beancount.plugins.auto_accounts\"

2024-01-02 * \"fund\"
  Assets:Bank      100 USD
  Equity:Opening

2024-02-01 close Assets:Bank
",
        findings: &[],
        closes_nonempty: true,
    },
    SurfaceCase {
        name: "close with a balance under currency_accounts",
        source: "plugin \"beancount.plugins.currency_accounts\" \"Equity:CurrencyAccounts\"

2024-01-01 open Assets:Bank
2024-01-01 open Assets:Euro
2024-01-01 open Equity:Opening

2024-01-02 * \"fund\"
  Assets:Bank      100 USD
  Equity:Opening

2024-01-03 * \"fx\"
  Assets:Euro      90 EUR @ 1.10 USD
  Assets:Bank     -99 USD

2024-02-01 close Assets:Bank
",
        findings: &[],
        closes_nonempty: true,
    },
    SurfaceCase {
        name: "validation after a STRICT booking error",
        source: "option \"booking_method\" \"STRICT\"

2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash

2024-01-01 * \"buy\"
  Assets:Stock   10 HOOL {100 USD}
  Assets:Cash

2024-01-02 * \"buy\"
  Assets:Stock   10 HOOL {110 USD}
  Assets:Cash

2024-01-03 * \"sell\"
  Assets:Stock   -5 HOOL {}
  Assets:Cash   500 USD

2024-01-04 balance Assets:Cash 0 USD
",
        findings: &[
            Finding {
                code: "E4003",
                line: 15,
                message: "Ambiguous lot match for HOOL: 2 lots match in Assets:Stock",
            },
            Finding {
                code: "E2001",
                line: 18,
                message: "Balance failed for Assets:Cash: expected 0 USD, got -2100 USD",
            },
        ],
        closes_nonempty: false,
    },
];
