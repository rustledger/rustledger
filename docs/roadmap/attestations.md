# Verifiable Ledger Statements Roadmap

> Part of the [rustledger roadmap](./index.md).

Forward-looking plan for **attestations**: signed, selectively-disclosable,
machine-verifiable statements of *computed* ledger state (balances as of a
date, covenant conditions) that a user can hand to an accountant, lender, or
counterparty. Items here are not-yet-done; shipped work lives in the
changelog.

## Why this layer exists

The plain-text file is the *input*, not the results. Signing a `.beancount`
file (or its git history) attests "these are the transactions I wrote down" —
it cannot attest "Assets:Checking held 12,340.12 USD on June 30" without
handing the verifier the entire ledger plus the obligation to recompute it
with the same engine version and plugins. An attestation seals the computed
result instead, and makes it verifiable offline by software that knows
nothing about beancount.

Two constraints define the layer:

- **Plain text stays the only source of truth.** Attestations store nothing
  the user authored — delete every statement and you lose signatures, not
  data.
- **Standards over invention.** The envelope, the disclosure mechanism, and
  the field semantics all come from published standards; nothing here should
  require trusting a rustledger-specific format to be verifiable.

## The chosen stack (and why)

| Layer | Choice | Rationale |
|-------|--------|-----------|
| Selective disclosure | SD-JWT ([RFC 9901](https://www.rfc-editor.org/info/rfc9901)) | Finalized IETF Proposed Standard (Nov 2025). Salted per-claim digests; the holder reveals only chosen claims — maps 1:1 onto "show the lender one account balance, not the whole books". |
| Credential envelope | SD-JWT VC ([draft-ietf-oauth-sd-jwt-vc](https://datatracker.ietf.org/doc/draft-ietf-oauth-sd-jwt-vc/), at IESG) | One of the two attestation formats the EU mandates for eIDAS 2.0 / EUDI Wallet (CIR (EU) 2024/2977, presented over OpenID4VP); the other is ISO mdoc. W3C VCDM-wholesale was rejected: no implementing regulation references VCDM 2.0, and the pending amendment drops it. |
| Rust base | [`sd-jwt-payload`](https://crates.io/crates/sd-jwt-payload) (IOTA) + a thin in-house SD-JWT VC layer | Implements final RFC 9901 including key-binding JWTs and decoy digests; actively maintained. The alternatives are draft-era and dormant. The VC layer (`vct`, type metadata) is deliberately small. |
| eIDAS upgrade path | JAdES ([ETSI TS 119 182-1](https://www.etsi.org/deliver/etsi_ts/119100_119199/11918201/01.02.01_60/ts_11918201v010201p.pdf)) | Profiles plain JWS to carry full AdES semantics — an Advanced/Qualified signature is a *wrap of the same JWS stack*, not a format migration. Cited in CIR (EU) 2024/2979 Annex IV; EC's DSS library produces it. Deferred until the qualified path is worth its QTSP cost. |
| Export semantics | OECD SAF-T 2.0 general-ledger concepts | Statement fields are named so they map mechanically onto SAF-T GL (AccountID, Period, Debit/CreditAmount). A minimal Header + GeneralLedgerEntries SAF-T file is schema-valid at the OECD level, giving the accountant/auditor export a bounded target. |

US context needs no format work at all: federal evidence law (FRE
902(13)/(14)) is signature-format-agnostic — a qualified person's
certification plus hash-based identification is what matters — so a
self-issued or accountant-issued SD-JWT VC is as usable as anything else.

## v1 statement — balances only (draft spec)

One statement = one SD-JWT VC whose payload is computed from the **booked**
ledger. Transaction-level detail is deliberately out of v1; the schema is
versioned so a detail extension can come later without breaking verifiers.

**Always-disclosed claims** (the statement is meaningless without them):

| Claim | Content |
|-------|---------|
| `vct` | Statement type URI, versioned (e.g. `…/ledger-statement/v1`). |
| `as_of` / `period` | The date the balances are computed at; optionally the covered period. |
| `engine` | `rustledger` version that computed the statement. |
| `source_hash` | SHA-256 over the ledger source files. The reproducibility anchor: a verifier who is *also* given the plaintext can recompute and compare, but no verifier is obligated to. |
| `iss` / `iat` / `cnf` | Standard SD-JWT VC issuer, issuance time, and holder key binding. |

**Selectively-disclosable claims** (each independently concealable):

| Claim | Content |
|-------|---------|
| `balances[]` | One claim per account: account name, currency, amount. Disclosure granularity is the account — "show `Assets:Checking`, conceal everything else" is the core UX. |
| `covenants[]` | Issuer-computed booleans (`net_worth_above_100k: true`) with a definition reference. This is the `age_over_NN` pattern from ISO mdoc: neither SD-JWT nor mdoc supports predicates ("prove balance > X without revealing it"), so the *issuer* evaluates the condition and attests the boolean. |

**Rules:**

- Amounts are **strings**, never JSON numbers — the same decimal-fidelity
  discipline as the rest of the pipeline, rendered via `DisplayContext`.
- Balance fields carry SAF-T-GL-mappable names so export is a transform, not
  a redesign.
- Key-binding JWT is required when a statement is presented to a third
  party.
- Two issuance modes over the *identical* payload: **self-issued** (the
  user's key) and **third-party** (e.g. an accountant signs what the engine
  computed) — the latter upgrades credibility with zero format change.
- Verification requires only an RFC 9901 library: no rustledger, no network.

## Now / In progress

| Item | Notes |
|------|-------|
| Harden this draft into a spec page | Claims table with exact JSON shapes, disclosure semantics, verification rules, and test vectors, under `spec/`. The published spec *is* part of the product promise. |

## Next

| Item | Notes |
|------|-------|
| `rustledger-attest` crate | Statement model (balances-only), SD-JWT VC issuance and verification on `sd-jwt-payload`, exposed as `rledger attest issue` / `rledger attest verify`. |
| Browser verifier | A small wasm build of the verifier so a counterparty can check a statement without installing anything. Doubles as the demo surface. |
| Accountant export | CSV trial balance plus OECD-baseline SAF-T GL XML (Header + GeneralLedgerEntries with control totals) computed from the same statement model. |

## Exploring / Later

| Item | Notes |
|------|-------|
| National SAF-T variants | *(On demand)* National schemas tighten the OECD baseline (PT, NO, PL, RO, …). First candidate: Norway (Skatteetaten hosts a clean XSD). Ship per-country transforms only when a real user needs one. |
| JAdES / qualified signatures | *(Gated)* Wrap the same JWS in JAdES baseline levels for eIDAS AdES; qualified status additionally needs a QTSP-issued certificate + QSCD. Gated on the unresolved question of what legal effect a QEAA with financial attributes actually has (eIDAS 2.0 Art. 45d) — do not build a QTSP integration before that answer exists. |
| mdoc / CBOR profile | *(Exploratory)* The second eIDAS-mandated format (deterministic CBOR + COSE, ISO 18013-5). Worth a profile only when an EUDI-wallet consumer is concrete. |
| Transaction-detail extension | *(Exploratory)* A v2 statement carrying disclosable journal lines — a SAF-T-grade audit artifact. Excluded from v1 to keep payloads small and the disclosure story crisp. |
| Batch issuance | *(Exploratory)* SD-JWT presentations are linkable across verifiers unless statements are issued in batches with unique salts. Matters once statements are presented repeatedly to distinct counterparties. |

## Design principles

1. **Derived-only.** The attestation layer never stores user-authored data;
   plaintext remains canonical and sufficient.
2. **Verify anywhere.** A statement must be checkable with off-the-shelf
   standard libraries — a verifier who distrusts rustledger entirely can
   still verify the signature and read the claims.
3. **No bespoke cryptography.** Envelope and disclosure come from IETF/ETSI
   standards; rustledger contributes the *semantics* (what a balance claim
   means and how it was computed), not new crypto.
4. **Decimal fidelity end to end.** Amounts are strings in the payload and
   rendered through the same `DisplayContext` canonicals as every other
   egress.
5. **Covenants are issuer-computed.** The formats can't do predicates;
   pretending otherwise (custom ZK) is out of scope. The boolean-claim
   pattern is deployed practice (mdoc `age_over_NN`).
