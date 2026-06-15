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

The clear next steps, building directly on the shipped pipeline.

| Item | Why it matters | Approach |
|------|----------------|----------|
| **Declarative institution profiles** | Per-user CSV column-mapping is the #1 setup friction. | A profile loader: a bank described by its source format (CSV/OFX layout), date/amount conventions, and default categorization rules — so a known bank "just works". Ships with built-in profiles for the most common US institutions on top of the loader. |
| **Automatic balance extraction** | `--balance` exists but the amount is hand-typed, so the assertion only catches *your* typos, not import gaps. | Pull the statement's opening/closing balance during extraction and compare it against the computed ledger balance; emit a diagnostic on mismatch. This is what turns importing from "hope it's complete" into "proven complete". |
| **Online-learning categorization** | The model trains once on the existing ledger and never improves from use. | Feed accept/correct decisions back into the Naive-Bayes model so suggestions get better the more you import. |

## Next

Well-scoped, but sequenced behind the items above.

| Item | Why it matters | Approach |
|------|----------------|----------|
| **Reconciliation / review UX** | Imports need a confirmation step, not blind trust. | A per-account, per-period view: opening/closing balances, what each source agrees on, and a queue to resolve mismatches before they hit the ledger. Pairs with balance extraction. |
| **Bank-API sync (SimpleFIN first)** | CSV/PDF is manual and lossy; an API is the difference between weekly chores and continuous. | Start with **SimpleFIN** (open protocol, low cost, no per-bank engineering). Plaid/Teller as optional, user-keyed backends behind the same interface later. Strictly opt-in. |
| **Recurring / expected-transaction detection** | Plain-text accounting silently *omits* what's missing; nobody notices a skipped paycheck import. | Let users declare expected recurring entries (rent, salary) and alert when an expected transaction doesn't show up — catches gaps the balance check can't. |
| **Multi-source matching** | Once there are two sources (CSV + API, or statement + export), naive dedup produces doubles or drops. | Match on amount + a date window with field-level scoring and a confidence output, producing match *groups* rather than binary yes/no. Feeds the review queue rather than auto-resolving. |
| **Community importer registry** | Every user re-deriving the same bank profile is wasted effort. | A shareable registry of `importers.toml` profiles, with automated tests against sample data so a contributed profile is verifiably correct before others rely on it. |
| **PDF statement extraction** | Many institutions only provide PDFs. | A local-first pipeline (text or OCR → layout/table detection → parse) with a declarative parser registry keyed by statement format. Local OCR by default; see below for the cloud escape hatch. |

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
