# Importing & Ingestion

Forward-looking roadmap for getting transactions into rustledger: parsing, multi-source validation, extraction, API sync, and the source archive.

> Part of the [rustledger roadmap](./index.md).

The shipped baseline is `rledger extract` driven by `importers.toml` profiles, sandboxed WASM importers, rule-based + Naive Bayes categorization, and user-supplied balance-assertion generation. Everything below is **not yet built**.

## Now / In progress

Work that is partially done or is the clear next thing to pick up.

| Item | Notes |
|------|-------|
| Automatic balance extraction | `--balance` exists but the amount is user-supplied; extract opening/closing balance from the statement and compare against the computed ledger balance, flagging mismatches with diagnostics. |
| Institution profile loader | Load declarative bank profiles (CSV/PDF/API source definitions + categorization rules) so common banks work without per-user column mapping. |
| Top-20 US bank profiles | Ship built-in profiles for the most common institutions on top of the loader. |
| Online-learning categorization | The Naive Bayes model trains on the existing ledger; feed user corrections back in to improve over time. |

## Next

Committed, well-scoped future items.

| Item | Notes |
|------|-------|
| Multi-source matching engine | Probabilistic (Fellegi-Sunter-style) matching: blocking on amount + date window, field scoring, confidence output, and match groups instead of binary yes/no. |
| Confidence scoring & trust ladder | Score transactions by source agreement (single source → corroborated → reconciled); route low-confidence items to a review queue. |
| SimpleFIN API integration | Open-protocol bank sync; candidate default given low cost. |
| Plaid API integration (issue ref) | Optional, user-supplied key; transaction enrichment + merchant normalization. |
| Teller API integration | Optional direct bank API. |
| IBKR importer (#923) | Interactive Brokers activity/statement importer. |
| Recurring / expected-transaction detection | Declare expected recurring transactions (rent, salary) and alert on missing bills or anomalies. |
| Reconciliation / review UX | Per-account period view showing opening/closing balances, per-source agreement, and a queue to resolve mismatches. |
| PDF statement extraction | Local-first pipeline (text/OCR → layout → table detection → parse), with a declarative parser registry per statement format. |
| Cloud/LLM extraction fallback | Optional cloud Document AI or vision-LLM extraction for low-confidence pages; privacy/accuracy is a user-chosen tradeoff (local-only vs. local+cloud). |
| Source archive (audit trail) | Append-only SQLite store of original source documents keyed by content hash, with extraction history and integrity verification. Compliance design (SEC 17a-4 / GoBD / GDPR audit trail) is captured separately. |

## Exploring / Later

Aspirational / brainstorm — not committed.

| Item | Notes |
|------|-------|
| Community importer registry (NEW) | A shareable, community-maintained `importers.toml` / institution-profile registry so users can pull and contribute bank importers with automated testing against sample data. |
| OCR ensemble | Multi-engine OCR (Tesseract / PaddleOCR / ONNX-exported models) with consensus voting to cut extraction errors; ONNX (`ort`) as the pure-Rust escape hatch. |
| LLM/MCP-assisted categorization | LLM-assisted account suggestion via MCP for transactions rules + ML leave uncategorized. |
| Compliance / audit attestation | Multi-jurisdiction compliance modes, transparency-log (Sigstore-style) attestation, and a path to third-party SEC 17a-4 assessment for regulated users. |
| Background sync daemon | Scheduled API sync with push notifications and anomaly detection for new transactions. |
| Statement-from-photo import | Import statements captured from a phone photo (mobile/HITL workflow). |

---

Shipped import features (trait system, CSV/OFX importers, auto-inference, ops crate, rules engine + merchant dictionary, fingerprinting/dedup, ML categorization, WASM plugins, user-supplied balance generation): see CHANGELOG.
