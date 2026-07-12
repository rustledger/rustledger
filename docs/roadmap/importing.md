# Importing & Ingestion

> Part of the [rustledger roadmap](./index.md). This is the engine room of
> [bet #2 — make ingestion painless](./index.md#2-make-ingestion-painless--the-real-adoption-barrier).

For plain-text accounting, the ledger format is the easy part; the friction is
getting bank data *in* and trusting that it's complete and correct. The shipped
baseline already covers the mechanics — `rledger extract` with `importers.toml`
profiles, sandboxed WASM importers, rule-based + Naive-Bayes categorization, and
balance-directive generation. What's left is making it **work out of the box**
for common cases and **earn trust** that nothing was missed.

Guiding principles: **local-first** (no data leaves the machine unless the user
opts in), **declarative** (banks described by data, not code), and
**trust-building** (surface uncertainty rather than silently importing).

## Now / In progress

The clear next steps. Re-prioritized after the 2026-07 import review, which
found that the biggest problem is not a missing feature but an integration
gap: **the Rust import engine is unreachable from every GUI surface.**
rustfava's import UI is upstream Fava's Python-beangulp flow (an optional
extra requiring user-authored Python importers), and the WASI component —
the primary embedding surface — exposes no import interface at all. None of
the engine's auto-inference, WASM importers, ML categorization, or fuzzy
dedup is visible to a web/desktop user.

| Item | Why it matters | Approach |
|------|----------------|----------|
| **Import over the component boundary** | Converts the import engine from a CLI feature into the product's ingestion layer — every GUI surface (rustfava, desktop) inherits it. | Add an `extract`/`identify` interface to the `rustledger:ledger` WIT world (additive minor bump), implemented in `rustledger-ffi-component` on top of `rustledger-importer`. Config rides as the existing `importers.toml` entry schema so the CLI and component share one canonical config parser. Then a rustfava ingest backend that consumes it — beangulp stays as the escape hatch for existing Python importers. |
| **Expose the finished-but-unwired ops** | `rustledger-ops::reconcile()` (statement-vs-import comparison) is tested but has no consumer — the CLI only calls `create_balance_directive`. `transfer.rs` has a consumer in `rledger lint transfers`, but the *import* flow never uses it: extraction/dedup can't pair a transfer's two legs across sources. | Wire the reconciliation *comparison* (not just balance-directive generation) into `extract` output, and reuse the transfer-pairing engine in import dedup/multi-source matching. Days of work that deliver part of the "Reconciliation / review UX" row early. |
| **Automatic balance extraction — OFX first** | `--balance` exists but the amount is hand-typed, so the assertion only catches *your* typos, not import gaps. **OFX statements already carry `<LEDGERBAL>` with an as-of date; the parser currently drops it.** | Phase 1: surface the OFX ledger balance during extraction and feed it to the existing `reconcile()` — nearly free, and every OFX import becomes verified-complete. Phase 2: CSV via an institution-profile field. This is what turns importing from "hope it's complete" into "proven complete". |
| **Declarative institution profiles — fixtures first** | Per-user CSV column-mapping is the #1 setup friction. But the repo ships **zero** built-in profiles and has **no real-institution fixture files** (tests use inline synthetic CSV/OFX), so there is nothing to pin a contributed profile against. | Sequence: (1) an anonymized per-institution statement-fixture corpus with snapshot tests — for an importer, fixtures *are* the spec; (2) a profile catalog on top of the existing `importers.toml` loader (`--bank <name>`); (3) only then the community registry, so a contributed profile is verifiably correct before others rely on it. |

## Next

Well-scoped, but sequenced behind the items above.

| Item | Why it matters | Approach |
|------|----------------|----------|
| **Online-learning categorization** | The model trains once on the existing ledger and never improves from use (`train()`/`predict()` only — no feedback path). | Feed accept/correct decisions back into the Naive-Bayes model so suggestions get better the more you import. Sequenced behind the component boundary so corrections made in the fava UI have a path back to the model, and it needs a decisions store. |
| **camt.053 native importer** | The ISO 20022 statement format is *the* EU bank-statement standard; today the native parsers are CSV and OFX only (no QIF/MT940/camt). | A native camt.053 reader alongside CSV/OFX. QIF is cheap legacy coverage to add opportunistically; MT940 stays WASM-importer territory. |
| **Flagship WASM importer: IBKR** ([#923](https://github.com/rustledger/rustledger/issues/923)) | Exercises the plugin path end-to-end and produces the template a community registry needs. | Ship the IBKR importer as a maintained example WASM importer rather than a native built-in. Also close the WASM config-projection gap (`use_merchant_dict`, regex mappings aren't carried across the boundary or exposed in `importers.toml`). |
| **Reconciliation / review UX** | Imports need a confirmation step, not blind trust. | A per-account, per-period view: opening/closing balances, what each source agrees on, and a queue to resolve mismatches before they hit the ledger. Pairs with balance extraction; the `reconcile()`/`transfer.rs` wiring above is its data source. |
| **Bank-API sync (SimpleFIN first)** | CSV/PDF is manual and lossy; an API is the difference between weekly chores and continuous. | Start with **SimpleFIN** (open protocol, low cost, no per-bank engineering). Plaid/Teller as optional, user-keyed backends behind the same interface later. Strictly opt-in. |
| **Recurring / expected-transaction detection** | Plain-text accounting silently *omits* what's missing; nobody notices a skipped paycheck import. | Let users declare expected recurring entries (rent, salary) and alert when an expected transaction doesn't show up — catches gaps the balance check can't. |
| **Multi-source matching** | Once there are two sources (CSV + API, or statement + export), naive dedup produces doubles or drops. | Match on amount + a date window with field-level scoring and a confidence output, producing match *groups* rather than binary yes/no. Builds on `transfer.rs`; feeds the review queue rather than auto-resolving. |
| **Community importer registry** | Every user re-deriving the same bank profile is wasted effort. | A shareable registry of `importers.toml` profiles, with automated tests against the fixture corpus so a contributed profile is verifiably correct before others rely on it. |
| **PDF statement extraction** | Many institutions only provide PDFs. | Phase 0 (shipped): the `preprocess` config hook — a user-specified external command (e.g. `pdftotext` + a table script) whose stdout feeds the normal pipeline. Phase 1: a native text-layer parser (most digital statements need no OCR). Phase 2, demand-gated: local OCR (layout/table detection) with a declarative parser registry; see below for the cloud escape hatch. |
| **Document filing (beangulp `archive`/`file` parity)** | beancount users with beangulp document-filing workflows have no migration path: the `Importer` trait deliberately omits `account()`/`date()`/`filename()` and there are no `archive`/`file` verbs. | Decide deliberately — adopt a filing surface (it dovetails with the attestation layer's `source_hash` provenance story) or document it as out of scope. The current silence is the only wrong option. |

## Exploring / Later

Genuinely uncertain — pursued only if the simpler items above prove insufficient
and there's real demand.

| Item | Open question |
|------|---------------|
| **Opt-in cloud / LLM extraction fallback** | For PDF pages local extraction can't parse confidently, a user-chosen cloud Document-AI or vision-LLM pass. The whole point is local-first, so this stays strictly opt-in and per-document — is the accuracy gain worth introducing a network dependency at all? |
| **LLM-assisted categorization** | An MCP-driven account suggestion for what rules + ML leave uncategorized. Useful, but only if it beats the (free, local, private) statistical model often enough to justify the dependency. |
| **Long-term source archive** | An append-only, content-hash-keyed store of original statements with extraction history — valuable for audit and re-extraction. The detailed design (storage, integrity, any regulatory framing) lives in [import-architecture.md](../development/import-architecture.md); it's deliberately *not* committed roadmap until there's a concrete user need. |

---

Shipped import features (trait system, CSV/OFX importers, auto-inference, the
`rustledger-ops` crate, rules engine + merchant dictionary, fingerprinting/dedup,
ML categorization, WASM plugins, balance-directive generation): see the
[CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md).
Detailed design notes: [import-architecture.md](../development/import-architecture.md).
