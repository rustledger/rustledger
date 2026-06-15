# Rustledger Import System Roadmap

> **⚠️ Implemented interface vs. aspirational design**
>
> The **shipped** import interface is the `rledger extract` command
> (`crates/rustledger/src/cmd/extract_cmd/`) configured via **`importers.toml`**
> profiles (selected with `--importer`), plus sandboxed WASM importers. ML
> account suggestion (`--suggest-categories`) and balance-assertion generation
> (`--balance` / `--balance-date`) are part of this shipped interface.
>
> Much of this document describes an **aspirational design** that has **not been
> built**. In particular, the `rledger import add/sync/status/validate/review`
> command family, the `rledger sources …` and `rledger import log …` commands,
> and the `import.yaml` / `institutions/*.yaml` / `sources.yaml` / `parsers/*.yaml`
> config formats are **design sketches, not implemented**. They are preserved
> here as planned/future work — treat any `rledger import …` invocation or YAML
> config below as not-yet-implemented unless this note says otherwise.

## Current Status

| Component | Status | Details |
|-----------|--------|---------|
| Import Trait System | ✅ Done | `Importer` trait, `ImportResult`, registry |
| CSV Importer | ✅ Done | Column mapping, date formats, debit/credit split |
| OFX Importer | ✅ Done | OFX/QFX file parsing |
| CSV Auto-Inference | ✅ Done | Delimiter, date format, column role detection (`--auto` flag) |
| Ops Crate (`rustledger-ops`) | ✅ Done | Pure operations: dedup, categorize, fingerprint, reconcile, merchants, transfer |
| Rules Engine | ✅ Done | Substring, regex, and exact match rules with priority ordering |
| Merchant Dictionary | ✅ Done | ~230 built-in patterns (groceries, dining, transport, subscriptions, etc.) |
| Transaction Fingerprinting | ✅ Done | Structural hashing via blake3 for stable dedup |
| Enriched Import Results | ✅ Done | `EnrichedImportResult` with confidence scores and categorization method |
| Institution Profiles | 🔮 Future | YAML-based bank definitions |
| Balance Validation | 🟡 Partial | `--balance`/`--balance-date` generate a `balance` directive via `rustledger-ops::reconcile` (amount is **user-supplied**); automatic balance *extraction from the statement* is still future |
| Multi-Source Matching | 🔮 Future | Cross-validate sources |
| PDF Extraction | 🔮 Future | Document AI / local OCR |
| API Integration | 🔮 Future | SimpleFIN, Plaid |
| ML Categorization | ✅ Done | Naive Bayes model (`rustledger-ops::ml::CategorizationModel`) trained on the user's existing ledger, wired into `rledger extract --suggest-categories` |
| LLM/MCP Categorization | 🔮 Future | LLM-assisted via MCP |
| WASM Import Plugins | ✅ Done | Third-party importers as sandboxed `.wasm` modules ([`WasmImporter`][wasm-importer], [`wasm_importer_main!`][wasm-macro], [example][wasm-csv-example]) |
| Source Archive | 🔮 Future | SQLite append-only store |

[wasm-importer]: https://github.com/rustledger/rustledger/blob/main/crates/rustledger-importer/src/wasm.rs
[wasm-macro]: https://github.com/rustledger/rustledger/blob/main/crates/rustledger-plugin-types/src/guest.rs
[wasm-csv-example]: https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example

**Current version**: Enrichment pipeline (Phase 1 complete, Phase 4.1 partial)

______________________________________________________________________

## Vision

Build a **dependable, multi-source validated** import system that eliminates the brittleness of traditional PTA import tools. Instead of trusting a single CSV, we cross-validate against multiple data sources to achieve high confidence in imported data.

**Key Insight**: Reconciliation is the killer feature, not parsing. Two independent sources agreeing provides exponentially higher confidence than one source alone.

______________________________________________________________________

## The Problem with Current Import Tools

| Issue | Description |
|-------|-------------|
| **Single source** | Trust one CSV/PDF blindly |
| **No validation** | Imported data never verified against bank |
| **Brittle parsers** | Break when formats change |
| **Code required** | Users must write Python for each bank |
| **No reconciliation** | No way to know if data is correct |

**Goal**: Import with confidence, not hope.

______________________________________________________________________

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                     DATA SOURCES                                 │
├─────────────────────────────────────────────────────────────────┤
│  SimpleFIN/   │  PDF Statements  │  CSV Exports  │  Manual     │
│  Plaid API    │  (Document AI)   │  (parsers)    │  Entry      │
└───────┬───────┴────────┬─────────┴───────┬───────┴──────┬──────┘
        │                │                 │              │
        ▼                ▼                 ▼              ▼
┌─────────────────────────────────────────────────────────────────┐
│              NORMALIZATION LAYER                                 │
│  Standardized Transaction Schema + Source Metadata               │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────────┐
│              MATCHING ENGINE (Probabilistic)                     │
│  • Blocking: same account + amount + date±3 days                 │
│  • Scoring: Fellegi-Sunter probabilistic field comparison        │
│  • Output: match groups with confidence scores                   │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────────┐
│              VALIDATION ENGINE                                   │
│  • Balance assertions (statement ending balance)                 │
│  • Completeness (expected transactions present)                  │
│  • Consistency (multi-source agreement)                          │
└─────────────────────────────────────────────────────────────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────────┐
│              CONFIDENCE SCORER                                   │
│  • Single source: 60%        • Balance verified: +20%            │
│  • Two sources agree: 90%    • Sources disagree: FLAG            │
│  • Three sources: 99%                                            │
└─────────────────────────────────────────────────────────────────┘
        │
        ├──────────────────┬───────────────────┐
        ▼                  ▼                   ▼
┌──────────────┐   ┌──────────────┐    ┌──────────────┐
│   AUTO       │   │   REVIEW     │    │   REJECTED   │
│   IMPORT     │   │   QUEUE      │    │   (errors)   │
│  (high conf) │   │  (low conf)  │    │              │
└──────────────┘   └──────────────┘    └──────────────┘
```

______________________________________________________________________

## Design Principles

> **⚠️ Aspirational design.** The remaining sections of this document
> (Design Principles, Architecture, Core Concepts, Data Model, User Experience,
> and the later Implementation Phases) describe planned/future work. The YAML
> config files (`import.yaml`, `institutions/*.yaml`, `sources.yaml`,
> `parsers/*.yaml`) and the `rledger import …` / `rledger sources …` command
> surfaces shown below are **not implemented** — the shipped interface is
> `rledger extract` + `importers.toml`. See the note at the top of this document.
> Genuinely-planned future items (PDF/OCR extraction, SimpleFIN/Plaid API
> integration, LLM/MCP categorization, the SQLite source archive, and compliance
> tooling) remain valid roadmap targets.

### 1. Privacy-First with User Choice

Users choose their privacy/accuracy tradeoff:

```yaml
# ~/.config/rledger/import.yaml
extraction:
  mode: local-only  # or "local-and-cloud"

  # Local-only: runs entirely on device
  local:
    ocr_engines: [doctr, tesseract, paddleocr]
    llm: null  # or local model like llama.cpp

  # Cloud-augmented: higher accuracy, sends documents to cloud
  cloud:
    provider: anthropic  # or openai, azure, google
    api_key_env: ANTHROPIC_API_KEY
    send_images: true  # false = send only extracted text
```

| Mode | Privacy | Accuracy | Speed |
|------|---------|----------|-------|
| **Local-only** | Maximum | ~90-95% | Slower |
| **Local + Cloud LLM** | Moderate | ~97-99% | Fast |
| **Cloud Document AI** | Lower | ~99%+ | Fastest |

### 2. Evolvable Extraction Ensemble

The extraction pipeline is **pluggable** - new engines can be added without changing core code:

```rust
/// Extraction engines are registered at runtime
pub trait ExtractionEngine: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn capabilities(&self) -> Capabilities;  // PDF, CSV, image, etc.

    fn extract(&self, source: &[u8]) -> Result<ExtractionResult>;
    fn confidence(&self) -> f64;
}

/// Ensemble coordinator runs multiple engines and merges results
pub struct ExtractionEnsemble {
    engines: Vec<Box<dyn ExtractionEngine>>,
    merger: Box<dyn ResultMerger>,
}
```

**Adding new engines**:

```bash
# Install community engine
rledger import engine add calamari-ocr

# Or via WASM plugin
rledger import engine add ./my-custom-engine.wasm
```

### Extraction Engine Candidates

#### Local Engines

| Engine | Language | Rust Integration | Accuracy | Table Support | Notes |
|--------|----------|------------------|----------|---------------|-------|
| [**Tesseract**](https://github.com/tesseract-ocr/tesseract) | C++ | ✅ [`tesseract-rs`](https://github.com/cafercangundogdu/tesseract-rs) (bundled) | ~85% | ❌ Poor | Classic, fast, auto-downloads deps |
| [**PaddleOCR**](https://github.com/PaddlePaddle/PaddleOCR) | Python/C++ | ✅ [`rust-paddle-ocr`](https://github.com/zibo-chen/rust-paddle-ocr) (MNN backend) | ~94% | ✅ Excellent | Best open-source table recognition |
| [**DocTR**](https://github.com/mindee/doctr) | Python | ✅ [OnnxTR](https://github.com/felixdittrich92/OnnxTR) (ONNX export) | ~87-95% | ⚠️ Basic | Good balance, portable models |
| [**EasyOCR**](https://github.com/JaidedAI/EasyOCR) | Python | ⚠️ ONNX export possible | ~85-90% | ❌ Poor | 80+ languages, GPU fast |
| [**Surya**](https://github.com/datalab-to/surya) | Python | ⚠️ ONNX export possible | ~90-95% | ✅ Good | 90+ langs, reading order, layout |
| [**Calamari**](https://github.com/Calamari-OCR/calamari) | Python | ❌ Python only | ~99.5% (ensemble) | ❌ None | Best for ensemble voting |

#### Cloud APIs

| Provider | Model | Accuracy | Pricing | Bank Statement Model | Notes |
|----------|-------|----------|---------|---------------------|-------|
| [**Claude Vision**](https://docs.anthropic.com/en/docs/build-with-claude/vision) | Sonnet 4 | ~90-97% | ~$0.005-0.02/page | ❌ Generic | Best JSON consistency |
| [**GPT-4o Vision**](https://platform.openai.com/docs/guides/vision) | GPT-4o-mini | ~91% | ~$0.01/page | ❌ Generic | Good value with mini |
| [**Google Document AI**](https://cloud.google.com/document-ai) | Bank Statement Parser | ~95%+ | ~$0.03/page | ✅ Pre-trained | 17 field types |
| [**Azure Doc Intelligence**](https://azure.microsoft.com/en-us/products/ai-services/ai-document-intelligence) | Bank Statement US | ~95%+ | ~$0.0125/page | ✅ Pre-trained | Cheapest, check tables |
| [**Gemini Vision**](https://ai.google.dev/gemini-api) | Gemini 2.5 Pro | ~94% | ~$0.002-0.01/page | ❌ Generic | Best on scanned docs |

#### Proven Local Vision LLM Configuration

Based on real-world testing with bank statements:

```yaml
# Recommended configuration (tested on RTX 3090)
local_vision_llm:
  model: qwen3-vl:8b          # Via Ollama - best accuracy
  fast_alternative: minicpm-v  # 5-7x faster, less accurate

  image_params:
    dpi: 150                   # Sweet spot for OCR clarity
    max_dimension: 1600        # Larger = better, but diminishing returns
    format: PNG                # Lossless - JPEG artifacts hurt accuracy

  inference:
    temperature: 0.0           # Deterministic output (critical!)
    timeout: 300s              # ~150s/page typical for qwen3-vl
    num_predict: 8000          # Allow long responses for many transactions

  prompt_tricks:
    - "/no_think prefix forces Qwen3 to output to content field"
    - "Simple direct prompts outperform complex chain-of-thought"
    - "Explicitly say 'Skip summary rows like Total or Balance'"
```

**Extraction prompt that works:**

```
/no_think
List each individual transaction line from this statement (not summary totals).
Each transaction has a date, description/merchant, and dollar amount.
Format as JSON: [{"date": "MM/DD", "merchant": "description text", "amount": number}]
Copy amounts exactly as shown. Skip summary rows like "Total" or "Balance".
```

**Performance benchmarks (RTX 3090):**

| Model | DPI | Speed | Accuracy | Use Case |
|-------|-----|-------|----------|----------|
| qwen3-vl:8b | 150 | ~150s/page | High | Production |
| minicpm-v | 100 | ~20-30s/page | Medium | Preview/draft |

**Implementation notes:**

- Use `pdfplumber` for PDF→image (not pdf2image or PyMuPDF)
- Qwen3 sometimes outputs to `thinking` field instead of `content` - check both
- Sign handling: auto-detect from account type (`Liabilities:` → negate positive)
- Year inference: parse from filename pattern like `2024-01` when dates are MM/DD only

#### Integration Strategy: ONNX as the Escape Hatch

Instead of wrapping Python libraries via subprocess, we export models to **ONNX** and run with [`ort`](https://github.com/pykeio/ort) (Rust ONNX Runtime):

```rust
use ort::{Session, Value};

// Load ONNX model (DocTR, PaddleOCR, Surya, etc.)
let session = Session::builder()?
    .with_model_from_file("doctr-detection.onnx")?;

let outputs = session.run(inputs)?;
```

**Benefits**:

- Pure Rust inference, no Python subprocess
- Models are portable files
- Same interface for all engines
- GPU acceleration via ONNX Runtime

### Recommended Ensemble Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    EXTRACTION ENSEMBLE                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  TIER 1: Native Rust (fastest, always available, offline)       │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  • tesseract-rs (bundled, no system deps)               │    │
│  │  • rust-paddle-ocr (MNN backend, pure Rust)             │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
│  TIER 2: ONNX Models (portable, good accuracy, offline)         │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  • OnnxTR (DocTR models exported to ONNX)               │    │
│  │  • PaddleOCR table detection (ONNX export)              │    │
│  │  • Surya layout analysis (ONNX export)                  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
│  TIER 3: Cloud APIs (highest accuracy, optional, user choice)   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  • Azure Document Intelligence (bank statement model)    │    │
│  │  • Google Document AI (bank statement parser)           │    │
│  │  • Claude/GPT-4o Vision (complex layouts, reasoning)    │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Cost Comparison (1000 pages/month)

| Configuration | Monthly Cost | Accuracy | Privacy |
|--------------|--------------|----------|---------|
| **Local only** (Tier 1) | $0 | ~90-94% | Maximum |
| **Local + ONNX** (Tier 1+2) | $0 | ~92-96% | Maximum |
| **Local + Cloud fallback** (~10% to cloud) | ~$1-3 | ~97-99% | High |
| **Azure/Google all pages** | $12-30 | ~95-99% | Medium |
| **GPT-4o all pages** | $50-70 | ~95-99% | Medium |

**Default recommendation**: Tier 1+2 (local ONNX ensemble) with optional Tier 3 for low-confidence extractions.

### 3. Immutable Statement Archive (SQLite Database)

**Architecture Decision**: Store all source documents in a **single SQLite database** as the authoritative source of truth. This is a proven pattern used by Git, Fossil, IPFS block stores, and CT logs.

**Key constraint**: The database is **append-only**. Never UPDATE or DELETE. Re-extractions are new rows, not modifications.

#### Database Location

```
~/.local/share/rledger/
├── sources.db              # Append-only source archive
├── sources.db-wal          # Write-ahead log (SQLite)
└── hardcopies/             # Optional: user-managed file copies
    └── 2024/
        └── chase-2024-01.pdf  # Validated against sources.db
```

#### Schema

```sql
-- Source documents (PDFs, CSVs, screenshots, etc.)
-- APPEND-ONLY: never UPDATE or DELETE rows
-- Designed for SEC 17a-4(f) Audit Trail Alternative compliance
CREATE TABLE sources (
    -- Content-addressed primary key
    hash TEXT PRIMARY KEY,              -- SHA-256 of content
    content BLOB NOT NULL,              -- Compressed original file (zstd)

    -- Metadata
    original_filename TEXT,             -- e.g., "eStmt_2024-01-31.pdf"
    mime_type TEXT,                     -- e.g., "application/pdf"
    account TEXT,                       -- e.g., "Assets:Chase:Checking"
    period_start DATE,                  -- Statement period start
    period_end DATE,                    -- Statement period end

    -- SEC 17a-4 compliance fields
    serial_number INTEGER UNIQUE NOT NULL,  -- Sequential, never reused, no gaps
    recorded_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    recorded_by TEXT NOT NULL,          -- Identity of user/system adding record
    hash_algorithm TEXT NOT NULL DEFAULT 'sha256',
    retention_expires DATE,             -- NULL = permanent retention

    -- Integrity (optional additional verification)
    signature BLOB                      -- Optional cryptographic signature
);

-- Extraction results (one source → many extractions over time)
-- APPEND-ONLY: new extractions are new rows, never updates
CREATE TABLE extractions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    source_hash TEXT NOT NULL REFERENCES sources(hash),
    extractor TEXT NOT NULL,            -- e.g., "qwen3-vl:8b", "azure-doc-intel"
    extractor_version TEXT,             -- e.g., "0.8.1"
    extractor_config_hash TEXT,         -- Hash of config used
    output_hash TEXT NOT NULL,          -- SHA-256 of extraction output
    output TEXT NOT NULL,               -- JSON: transactions, balances, etc.
    confidence REAL,                    -- 0.0-1.0
    extracted_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    extracted_by TEXT NOT NULL          -- Identity for audit trail
);

-- Validation checkpoints (computed at runtime, logged for audit)
-- APPEND-ONLY: each validation run is a new row
CREATE TABLE validations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    account TEXT NOT NULL,
    period_start DATE NOT NULL,
    period_end DATE NOT NULL,
    ledger_hash TEXT NOT NULL,          -- Hash of ledger state
    sources_used TEXT NOT NULL,         -- JSON array of source hashes
    validation_type TEXT NOT NULL,      -- "balance", "multi-source", "coverage"
    result TEXT NOT NULL,               -- "pass", "fail", "warning"
    details TEXT,                       -- JSON: explanation, discrepancies
    validated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    validated_by TEXT NOT NULL          -- Identity for audit trail
);

-- Complete audit log for SEC 17a-4 compliance
-- Tracks ALL operations: creates, reads (optional), exports
-- Merkle chain ensures tamper detection
CREATE TABLE audit_log (
    sequence INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    actor TEXT NOT NULL,                -- Identity of user/system
    action TEXT NOT NULL,               -- 'create', 'read', 'export', 'verify'
    target_type TEXT NOT NULL,          -- 'source', 'extraction', 'validation'
    target_id TEXT NOT NULL,            -- Hash or ID of affected record
    details TEXT,                       -- JSON: additional context
    previous_hash TEXT NOT NULL,        -- Hash of previous log entry (Merkle chain)
    entry_hash TEXT NOT NULL            -- Hash of this entry for verification
);

-- Retention policy tracking
CREATE VIEW retention_status AS
SELECT
    hash,
    serial_number,
    original_filename,
    recorded_at,
    retention_expires,
    CASE
        WHEN retention_expires IS NULL THEN 'permanent'
        WHEN retention_expires > date('now') THEN 'active'
        ELSE 'retention_complete'
    END as status,
    CASE
        WHEN retention_expires IS NULL THEN NULL
        ELSE julianday(retention_expires) - julianday('now')
    END as days_remaining
FROM sources;

-- Indexes for common queries
CREATE INDEX idx_sources_account ON sources(account);
CREATE INDEX idx_sources_period ON sources(period_start, period_end);
CREATE INDEX idx_sources_serial ON sources(serial_number);
CREATE INDEX idx_sources_retention ON sources(retention_expires);
CREATE INDEX idx_extractions_source ON extractions(source_hash);
CREATE INDEX idx_validations_account ON validations(account, period_start);
CREATE INDEX idx_audit_target ON audit_log(target_type, target_id);
CREATE INDEX idx_audit_actor ON audit_log(actor);
```

#### Append-Only Enforcement (SEC 17a-4 Compliant API)

```rust
/// Source archive with SEC 17a-4(f) Audit Trail Alternative compliance
///
/// Key compliance properties:
/// - Append-only: no UPDATE or DELETE operations exposed
/// - Complete audit trail: every action logged with actor identity
/// - Sequential serials: no gaps, proves completeness
/// - Merkle chain: tamper detection via hash linking
pub struct SourceArchive {
    db: rusqlite::Connection,
    actor: String,              // Identity for audit trail
    config: ArchiveConfig,
}

pub struct ArchiveConfig {
    pub log_reads: bool,        // Log read operations (compliance mode)
    pub default_retention_years: Option<u32>,  // e.g., 7 for SEC compliance
}

impl SourceArchive {
    /// Add a source document with full audit trail
    /// Returns existing record if content already archived (deduplication)
    pub fn add_source(&self, content: &[u8], meta: SourceMetadata) -> Result<SourceRecord> {
        let hash = sha256(content);

        // Check if already exists (deduplication)
        if let Some(existing) = self.get_by_hash(&hash)? {
            self.log_action("create_duplicate", "source", &hash, json!({
                "existing_serial": existing.serial_number,
                "note": "Content already archived, returning existing record"
            }))?;
            return Ok(existing);
        }

        let serial = self.next_serial()?;
        let compressed = zstd::encode(content)?;
        let retention = self.config.default_retention_years
            .map(|y| Utc::now() + Duration::days(y as i64 * 365));

        self.db.execute(
            "INSERT INTO sources (hash, content, serial_number, recorded_by,
             original_filename, account, retention_expires, ...)
             VALUES (?, ?, ?, ?, ?, ?, ?, ...)",
            params![hash, compressed, serial, self.actor,
                    meta.filename, meta.account, retention, ...],
        )?;

        self.log_action("create", "source", &hash, json!({
            "serial_number": serial,
            "filename": meta.filename,
            "account": meta.account
        }))?;

        self.get_by_hash(&hash)
    }

    /// Retrieve a source - optionally logged for compliance
    pub fn get_source(&self, hash: &str) -> Result<SourceRecord> {
        let record = self.db.query_row(
            "SELECT * FROM sources WHERE hash = ?",
            params![hash],
            |row| SourceRecord::from_row(row),
        )?;

        // In compliance mode, log all reads
        if self.config.log_reads {
            self.log_action("read", "source", hash, None)?;
        }

        Ok(record)
    }

    /// Export source in human-readable format (required by SEC 17a-4)
    pub fn export(&self, hash: &str, format: ExportFormat) -> Result<ExportResult> {
        let source = self.get_source(hash)?;
        let content = zstd::decode(&source.content)?;

        let (data, mime) = match format {
            ExportFormat::Original => (content, source.mime_type),
            ExportFormat::Pdf => (render_to_pdf(&source)?, "application/pdf".into()),
            ExportFormat::Json => (serialize_full_record(&source)?, "application/json".into()),
        };

        self.log_action("export", "source", hash, json!({
            "format": format,
            "size_bytes": data.len()
        }))?;

        Ok(ExportResult { data, mime_type: mime })
    }

    /// Verify integrity of entire archive
    /// Returns detailed report suitable for auditors
    pub fn verify_integrity(&self) -> Result<IntegrityReport> {
        let mut report = IntegrityReport::new();

        // 1. Verify all content hashes match stored content
        report.content_verification = self.verify_all_content_hashes()?;

        // 2. Verify Merkle chain in audit_log (no tampering)
        report.audit_chain = self.verify_audit_chain()?;

        // 3. Check for gaps in serial numbers (completeness)
        report.serial_continuity = self.verify_serial_continuity()?;

        // 4. Verify all foreign key references valid
        report.referential_integrity = self.verify_references()?;

        self.log_action("verify", "archive", "full", json!({
            "passed": report.all_passed(),
            "checks": report.summary()
        }))?;

        Ok(report)
    }

    /// Generate compliance report for auditors/examiners
    pub fn generate_compliance_report(&self, period: DateRange) -> Result<ComplianceReport> {
        ComplianceReport {
            period,
            total_records: self.count_sources_in_period(period)?,
            serial_range: self.serial_range_in_period(period)?,
            retention_summary: self.retention_summary()?,
            integrity_status: self.verify_integrity()?,
            audit_log_excerpt: self.audit_log_for_period(period)?,
        }
    }

    // ══════════════════════════════════════════════════════════════════
    // FORBIDDEN OPERATIONS - These methods intentionally do not exist
    // ══════════════════════════════════════════════════════════════════
    // pub fn update_source(...) - DOES NOT EXIST (violates immutability)
    // pub fn delete_source(...) - DOES NOT EXIST (violates retention)
    // pub fn modify_audit_log(...) - DOES NOT EXIST (violates chain)
}
```

#### Hardcopy Validation

Users can optionally keep files outside the database. These are validated against the DB:

```bash
# Import a statement (stores in DB, optionally copies to hardcopies/)
rledger import add ~/Downloads/chase-2024-01.pdf --keep-hardcopy

# Validate hardcopies match database
rledger import verify-hardcopies
✅ hardcopies/2024/chase-2024-01.pdf matches sources.db (sha256:a1b2c3...)
⚠️  hardcopies/2024/amex-2024-01.pdf NOT in database - orphan file
❌ hardcopies/2024/discover-2024-01.pdf HASH MISMATCH - file modified!
```

#### Benefits of SQLite Approach

| Benefit | Description |
|---------|-------------|
| **Single file** | Easy backup, sync, migration |
| **Atomic writes** | WAL mode ensures no corruption |
| **Portable** | Works on any OS, no server needed |
| **Query-able** | SQL for complex lookups |
| **Proven pattern** | Fossil, Git (conceptually), IPFS block stores |
| **Deduplication** | Same file uploaded twice = stored once |
| **Compression** | zstd in BLOBs saves 50-80% space |
| **Tamper-evident** | Merkle chain in audit_log detects changes |

#### CLI Commands

```bash
# Add source document
rledger sources add ~/Downloads/chase-2024-01.pdf \
  --account Assets:Chase:Checking \
  --period 2024-01

# List sources for account
rledger sources list --account Assets:Chase:Checking
HASH        ADDED       PERIOD      FILE
a1b2c3d4    2024-02-01  2024-01     chase-2024-01.pdf
e5f6g7h8    2024-03-01  2024-02     chase-2024-02.pdf

# Show extraction history for a source
rledger sources history a1b2c3d4
EXTRACTED    EXTRACTOR        CONFIDENCE  OUTPUT_HASH
2024-02-01   qwen3-vl:8b      0.94        def456...
2024-06-15   claude-sonnet    0.99        def456...  (same result!)

# Verify database integrity (Merkle chain)
rledger sources verify
✅ Audit log integrity verified: 1,234 entries
✅ All source hashes valid
✅ No orphan extractions

# Export source document (decompress from DB)
rledger sources export a1b2c3d4 -o ~/recovered/chase-2024-01.pdf
```

### 4. Transparency Log (Sigstore-style)

Inspired by [Sigstore Rekor](https://docs.sigstore.dev/logging/overview/), we maintain an **append-only Merkle tree** of all import operations:

```
┌─────────────────────────────────────────────────────────────────┐
│                    TRANSPARENCY LOG                              │
├─────────────────────────────────────────────────────────────────┤
│  Entry 0: Genesis (log creation)                                │
│  Entry 1: Statement import (chase-2024-01.pdf)                  │
│  Entry 2: Statement import (amex-2024-01.pdf)                   │
│  Entry 3: Extraction re-run (chase-2024-01.pdf, new engine)     │
│  Entry 4: Balance assertion added                               │
│  Entry 5: User correction (manual edit)                         │
│  ...                                                            │
│  Entry N: Current head                                          │
└─────────────────────────────────────────────────────────────────┘
         │
         ▼
    Merkle Root: sha256:abc123...
    Signed by: user's key (optional)
```

**Log entry structure**:

```rust
pub struct LogEntry {
    pub sequence: u64,
    pub timestamp: DateTime<Utc>,
    pub previous_hash: Hash,  // Chain integrity
    pub entry_type: EntryType,
    pub payload: EntryPayload,
    pub merkle_proof: Option<MerkleProof>,
}

pub enum EntryType {
    StatementImport {
        file_hash: Hash,
        account: String,
        period: DateRange,
        extraction_engine: String,
        transactions_hash: Hash,
        balance_verified: bool,
    },
    ExtractionRerun {
        file_hash: Hash,
        old_engine: String,
        new_engine: String,
        result_changed: bool,
    },
    BalanceAssertion {
        account: String,
        date: NaiveDate,
        amount: Decimal,
        verified_against: Vec<Hash>,  // Statement hashes
    },
    UserCorrection {
        original_hash: Hash,
        corrected_hash: Hash,
        reason: String,
    },
    LedgerCheckpoint {
        ledger_hash: Hash,
        entry_count: u64,
    },
}
```

**What this enables**:

- **Tamper detection**: Any modification breaks the hash chain
- **Audit trail**: Complete history of all import operations
- **Consistency proofs**: Prove log hasn't been rewritten
- **Non-repudiation**: Can prove a statement was imported at a specific time
- **Disaster recovery**: Reconstruct ledger from log + original statements

**CLI commands**:

```bash
# Verify log integrity
rledger import log verify
✅ Log integrity verified: 1,234 entries, root=sha256:abc123...

# Show log history
rledger import log show --account Assets:Chase:Checking
2024-01-15 10:23  IMPORT   chase-2024-01.pdf   47 txns  ✓ balanced
2024-02-01 08:15  IMPORT   chase-2024-02.pdf   52 txns  ✓ balanced
2024-06-15 12:00  RE-RUN   chase-2024-01.pdf   (claude-vision) no changes

# Export inclusion proof for specific entry
rledger import log proof --entry 42 > proof.json
```

**Optional: Public attestation** (for businesses/compliance):

```bash
# Publish log root to public transparency log (e.g., Sigstore Rekor)
rledger import log attest --publish
Published to rekor.sigstore.dev: entry 12345678
```

### 5. SEC 17a-4 Compatible Architecture

The source archive is designed to meet **SEC Rule 17a-4(f) Audit Trail Alternative** requirements, enabling optional third-party attestation for regulated users while providing robust data integrity for everyone.

#### Why Design to This Standard?

Even if you're not a broker-dealer, SEC 17a-4 represents **battle-tested requirements** for financial record integrity developed over decades. By meeting this standard:

| Benefit | For Personal Users | For Businesses |
|---------|-------------------|----------------|
| **Immutability** | Can't accidentally delete statements | Regulatory compliance |
| **Audit trail** | See when/how data was imported | Examiner-ready logs |
| **Integrity verification** | Detect corruption | Prove no tampering |
| **Sequential serials** | Know if anything missing | Completeness proof |
| **Retention policies** | Auto-cleanup after N years | Meet retention requirements |
| **Export formats** | Get data out easily | Human-readable for regulators |

#### The 17 Technical Requirements (SEC 17a-4(f))

Per [Cohasset Associates assessments](https://d1.awsstatic.com/r2018/b/S3-Object-Lock/Amazon-S3-Compliance-Assessment.pdf):

| Category | Requirement | Our Implementation |
|----------|-------------|-------------------|
| **Recording** | Serialize records | `serial_number` - sequential, no gaps |
| | Time-date stamp | `recorded_at` with UTC timestamp |
| | Verify record integrity | SHA-256 content hash verified on add |
| **Storage** | WORM *or* Audit Trail | Audit Trail (append-only + complete history) |
| | Prevent alteration | No UPDATE/DELETE in API |
| | Preserve for retention period | `retention_expires` field + policy enforcement |
| **Retrieval** | Immediate access (2 years) | SQLite indexed queries |
| | Non-immediate access (6 years) | Same DB, no cold storage needed |
| | Download in readable format | `export` command: PDF, JSON, original |
| **Audit Trail** | Track all modifications | `audit_log` table with Merkle chain |
| | Record date/time of actions | `timestamp` on all log entries |
| | Record identity of actor | `actor` field on all operations |
| | Preserve original + all versions | Never delete; re-extractions are new rows |
| **Management** | Index for search | SQLite FTS5 full-text search |
| | Duplicate at off-site | `backup` command to S3/local |
| | Quality control | `verify` command checks all integrity |

#### Compliance Mode Configuration

```yaml
# ~/.config/rledger/sources.yaml
compliance:
  mode: sec-17a-4              # or "standard" for personal use

  # SEC 17a-4 specific settings
  retention_years: 7           # 6 years required + 1 buffer
  log_read_access: true        # Log all reads (required for full audit)
  require_actor_identity: true # Every operation must have identity

  # Backup for off-site requirement
  backup:
    enabled: true
    destination: s3://my-bucket/rledger-backup/
    frequency: daily
    verify_after_backup: true
```

#### CLI Commands for Compliance

```bash
# Standard operations (automatically compliant)
rledger sources add statement.pdf --account Assets:Chase

# Compliance-specific commands
rledger sources verify --full              # Verify all hashes + Merkle chain
rledger sources verify --serial-continuity # Check for gaps in serials

# Audit and reporting
rledger sources audit-report --period 2024 # Generate compliance report
rledger sources audit-log --actor "john"   # Filter audit log by user
rledger sources audit-log --export json    # Export for examiners

# Retention management
rledger sources retention set a1b2c3 --years 7
rledger sources retention report           # Show status of all records
rledger sources retention expiring --days 90  # What's expiring soon

# Backup for off-site requirement (SEC 17a-4(f)(3)(iii))
rledger sources backup --to s3://bucket/backup/
rledger sources backup --verify            # Verify backup integrity
```

#### Sample Compliance Report

```
══════════════════════════════════════════════════════════════════
           RLEDGER SOURCE ARCHIVE COMPLIANCE REPORT
══════════════════════════════════════════════════════════════════
Report Generated: 2024-12-15T10:30:00Z
Archive Location: ~/.local/share/rledger/sources.db
Report Period:    2024-01-01 to 2024-12-15

SUMMARY
───────────────────────────────────────────────────────────────────
Total Source Records:     156
Serial Number Range:      1 - 156 (no gaps ✓)
Retention Policy:         7 years
Records in Retention:     156 (100%)
Records Past Retention:   0

INTEGRITY VERIFICATION
───────────────────────────────────────────────────────────────────
Content Hash Verification:    156/156 PASSED ✓
Audit Log Chain Verification: 1,847 entries, chain intact ✓
Serial Continuity:            No gaps detected ✓
Referential Integrity:        All references valid ✓

AUDIT LOG SUMMARY
───────────────────────────────────────────────────────────────────
Total Operations:         1,847
  - create:               156
  - read:                 1,423
  - export:               45
  - verify:               223

Unique Actors:            2
  - john@example.com:     1,203 operations
  - system:               644 operations

RETENTION STATUS
───────────────────────────────────────────────────────────────────
Permanent:                0
Active (in retention):    156
Expiring < 90 days:       0
Retention complete:       0

ATTESTATION
───────────────────────────────────────────────────────────────────
Archive Hash:             sha256:a1b2c3d4e5f6...
Audit Log Root:           sha256:f6e5d4c3b2a1...

This report was generated by rledger v0.8.0
Architecture compliant with SEC Rule 17a-4(f) Audit Trail Alternative
══════════════════════════════════════════════════════════════════
```

#### Path to Third-Party Attestation

If a user or business needs formal SEC 17a-4 compliance certification:

1. **Documentation** - We provide architecture docs mapping each SEC requirement to implementation
1. **Configuration Guide** - How to deploy in compliance mode with proper settings
1. **Assessment Engagement** - User engages [Cohasset Associates](https://www.cohasset.com/) (or similar firm)
1. **Testing** - Assessor verifies claims against actual implementation
1. **Report** - Assessor issues compliance assessment letter

**What rledger provides**:

- Compliant architecture (this document)
- `--compliance-mode` configuration
- `verify` and `audit-report` commands
- Export formats suitable for examiners

**What the user must arrange**:

- Third-party assessment engagement (~$10-50k typically)
- Designated Third Party (D3P) or Designated Executive Officer filing with SEC
- Off-site backup infrastructure
- Access controls and operational procedures

#### Regulatory References

- [SEC Rule 17a-4](https://www.sec.gov/rules/final/34-38245.txt) - Electronic recordkeeping requirements
- [SEC 2023 Amendment](https://www.sec.gov/rules/final/2022/34-96034.pdf) - Added Audit Trail Alternative
- [FINRA Rule 4511](https://www.finra.org/rules-guidance/rulebooks/finra-rules/4511) - Books and records requirements
- [Cohasset SEC 17a-4 Assessments](https://d1.awsstatic.com/r2018/b/S3-Object-Lock/Amazon-S3-Compliance-Assessment.pdf) - Example assessment methodology
- [AWS SEC Compliance](https://aws.amazon.com/compliance/secrule17a-4f/) - How cloud providers approach compliance

### 6. Multi-Jurisdiction Compliance

The source archive supports compliance with multiple regulatory frameworks beyond SEC 17a-4. Different jurisdictions have varying requirements for financial record retention and data integrity.

#### Supported Compliance Frameworks

| Framework | Jurisdiction | Retention | Key Requirements | Status |
|-----------|--------------|-----------|------------------|--------|
| **[SEC 17a-4](https://www.sec.gov/rules/final/34-38245.txt)** | US (Securities) | 6-7 years | WORM or Audit Trail, immediate access | ✅ Full support |
| **[SOX](https://pathlock.com/learn/sox-data-retention-requirements/)** | US (Public Companies) | 7 years | Audit records, internal controls, tamper-proof | ✅ Full support |
| **[GoBD](https://www.fiskaly.com/blog/understanding-gobd-compliant-archiving)** | Germany | 10 years | Immutability, traceability, original format | ✅ Full support |
| **[MiFID II](https://www.skillcast.com/blog/mifid-data-retention-compliance)** | EU (Financial) | 5-7 years | WORM format, transaction records | ✅ Full support |
| **[IRS](https://www.uschamber.com/co/start/strategy/how-long-to-keep-business-documents)** | US (Tax) | 3-7 years | Tax returns, supporting documentation | ✅ Full support |
| **[HIPAA](https://signoz.io/guides/log-retention/)** | US (Healthcare) | 6 years | PHI protection, secure disposal | ⚠️ Partial (no PHI features) |
| **[GDPR](https://bigid.com/blog/what-is-data-retention/)** | EU (Privacy) | Minimize | Data minimization, right to erasure | ⚠️ Special handling |
| **[ISO 15489](https://www.iso.org/standard/62542.html)** | International | Varies | Records management framework | ✅ Aligned |
| **[DoD 5015.02](https://www.laserfiche.com/resources/blog/why-you-need-to-care-about-dod-5015-2/)** | US Government | Varies | Electronic records management | ⚠️ Not certified |

#### GoBD (Germany) - Strictest Standard

GoBD (Grundsätze zur ordnungsmäßigen Führung und Aufbewahrung von Büchern) is particularly relevant as it represents the **strictest** widely-applicable standard:

| GoBD Requirement | Our Implementation |
|------------------|-------------------|
| **Immutability** (Unveränderbarkeit) | Append-only database, no UPDATE/DELETE |
| **Traceability** (Nachvollziehbarkeit) | Complete audit trail with actor identity |
| **Timely recording** (Zeitgerechte Erfassung) | Timestamp on all operations |
| **10-year retention** | Configurable `retention_years: 10` |
| **Original format preserved** | Store original file content, not just metadata |
| **Procedural documentation** | Architecture docs + verification commands |
| **Audit-ready export** | Human-readable export in multiple formats |

**Key GoBD principle**: "The original document must be retained for the entire storage period in unaltered form." This validates our design of storing actual file content with cryptographic hash verification.

#### GDPR Compatibility: Right to Erasure

GDPR presents a unique challenge: it requires honoring "right to erasure" requests, but our architecture is append-only. We resolve this through **cryptographic erasure**:

```sql
-- Extended schema for GDPR compliance
ALTER TABLE sources ADD COLUMN pii_status TEXT DEFAULT 'none';
  -- 'none': No PII in this document
  -- 'present': Contains PII, encrypted with pii_key_id
  -- 'erased': PII cryptographically erased

ALTER TABLE sources ADD COLUMN pii_key_id TEXT;
  -- Reference to encryption key for PII fields

-- Separate table for PII encryption keys (can be deleted)
CREATE TABLE pii_keys (
    key_id TEXT PRIMARY KEY,
    encrypted_key BLOB NOT NULL,     -- Wrapped with master key
    created_at TIMESTAMP NOT NULL,
    deleted_at TIMESTAMP,            -- Non-null = key destroyed = PII erased
    deletion_reason TEXT             -- 'gdpr_request', 'retention_expired', etc.
);

-- Audit log entry for erasure (proves compliance)
-- Note: We log that erasure happened, not what was erased
```

**How cryptographic erasure works**:

1. PII in documents is encrypted with a per-record key
1. Keys are stored in `pii_keys` table
1. On erasure request, the key is deleted (not the document)
1. Document remains for audit trail, but PII is unrecoverable
1. Audit log records that erasure was performed

```rust
impl SourceArchive {
    /// Process GDPR erasure request
    /// The document remains but PII becomes cryptographically inaccessible
    pub fn process_erasure_request(&self, source_hash: &str, reason: &str) -> Result<()> {
        let source = self.get_source(source_hash)?;

        if source.pii_status != "present" {
            return Err(Error::NoPiiToErase);
        }

        // Delete the encryption key (cryptographic erasure)
        self.db.execute(
            "UPDATE pii_keys SET deleted_at = ?, deletion_reason = ? WHERE key_id = ?",
            params![Utc::now(), reason, source.pii_key_id],
        )?;

        // Update source status
        self.db.execute(
            "UPDATE sources SET pii_status = 'erased' WHERE hash = ?",
            params![source_hash],
        )?;

        // Audit log (proves we complied with request)
        self.log_action("pii_erasure", "source", source_hash, json!({
            "reason": reason,
            "key_id": source.pii_key_id,
            "note": "PII cryptographically erased per GDPR Article 17"
        }))?;

        Ok(())
    }
}
```

#### Compliance Mode Configuration

```yaml
# ~/.config/rledger/sources.yaml
compliance:
  # Primary compliance framework
  mode: gobd                    # Options: standard, sec-17a-4, gobd, mifid2, sox

  # Retention (uses maximum of mode default and this value)
  retention_years: 10           # GoBD requires 10 years

  # Audit trail settings
  log_read_access: true         # Required for full compliance audit
  require_actor_identity: true  # Every operation tagged with user

  # GDPR settings (can be enabled alongside other modes)
  gdpr:
    enabled: true               # Enable GDPR features
    pii_encryption: true        # Encrypt PII fields
    erasure_support: true       # Allow cryptographic erasure
    data_minimization_warnings: true  # Warn about unnecessary data

  # Multi-jurisdiction: apply strictest requirement from all
  frameworks:
    - sec-17a-4
    - gobd
    - gdpr
```

#### CLI Commands

```bash
# Set compliance mode
rledger sources config --compliance-mode gobd

# Check compliance status
rledger sources compliance-check
✅ GoBD Compliance Check
   Immutability:     PASS (no UPDATE/DELETE in audit log)
   Traceability:     PASS (all operations have actor identity)
   Retention:        PASS (10 year policy, 0 records expired early)
   Original format:  PASS (all sources have content + hash)
   Serial continuity: PASS (no gaps in sequence)

# GDPR erasure request
rledger sources gdpr-erase a1b2c3d4 --reason "Subject request Art. 17"
⚠️  This will cryptographically erase PII from source a1b2c3d4
    The document structure remains for audit purposes.
    This action cannot be undone.
    Proceed? [y/N] y
✅ PII erased. Audit log entry created.

# Generate multi-framework compliance report
rledger sources compliance-report --frameworks sec-17a-4,gobd,gdpr
```

#### Retention Policy Priority

When multiple frameworks apply, use the **strictest** requirement:

```
User configures: [SEC 17a-4, GoBD, GDPR]

SEC 17a-4: 7 years retention
GoBD:      10 years retention  ← Winner (longest)
GDPR:      Minimize retention  ← Conflicts resolved via crypto-erasure

Result: 10 year retention with GDPR erasure support
```

#### Framework-Specific References

**Financial Regulations:**

- [SEC Rule 17a-4](https://www.sec.gov/rules/final/34-38245.txt) - US Securities electronic recordkeeping
- [SOX Section 802](https://pathlock.com/learn/sox-data-retention-requirements/) - US corporate audit records
- [MiFID II Article 16(7)](https://www.skillcast.com/blog/mifid-data-retention-compliance) - EU financial transaction records
- [GoBD](https://www.fiskaly.com/blog/understanding-gobd-compliant-archiving) - German electronic bookkeeping

**Privacy Regulations:**

- [GDPR Article 17](https://bigid.com/blog/what-is-data-retention/) - Right to erasure
- [GDPR Article 5(1)(e)](https://gdpr-info.eu/art-5-gdpr/) - Storage limitation principle

**Records Management Standards:**

- [ISO 15489-1:2016](https://www.iso.org/standard/62542.html) - Records management concepts
- [DoD 5015.02](https://www.laserfiche.com/resources/blog/why-you-need-to-care-about-dod-5015-2/) - US government electronic records

**Audit Standards:**

- [SOC 2 Type II](https://drata.com/grc-central/soc-2/type-2) - Processing integrity controls
- [AICPA Trust Services Criteria](https://www.aicpa.org/) - Security, availability, integrity

______________________________________________________________________

## Core Concepts

### 1. Multi-Source Validation

Every transaction can come from multiple sources:

| Source | Reliability | Typical Use |
|--------|-------------|-------------|
| **Bank API** (Plaid/SimpleFIN) | High | Real-time sync |
| **PDF Statement** | Highest | Monthly verification |
| **CSV Export** | Medium | Manual download |
| **Email notifications** | Low | Supplementary |
| **Manual entry** | Variable | Edge cases |

**Confidence increases with agreement**:

- 1 source = 60% confidence (could be parsing error)
- 2 sources agree = 90% confidence (unlikely both wrong)
- 3 sources agree = 99% confidence (verified)
- Sources disagree = FLAG for review

### 2. Balance Assertions as Ground Truth

Every statement has an **ending balance**. This is the ultimate validation:

```
Statement says: $4,523.17 on 2024-01-31
Ledger computes: $4,523.17 on 2024-01-31
✅ VERIFIED - all transactions in this period are correct
```

If balances don't match, something is wrong. Find it.

### 3. Statement Linking via Document + Balance Directives

The audit trail lives **in the ledger itself** using Beancount's native `document` directive for statement metadata, and `balance` for verification provenance:

```beancount
; Statement archived with extraction metadata
2024-01-31 document Assets:Chase:Checking "statements/chase-2024-01.pdf"
  hash: "sha256:a1b2c3d4e5f6..."
  period: "2024-01-01 to 2024-01-31"
  extracted-by: "qwen3-vl:8b"
  extraction-confidence: "0.97"
  transactions-extracted: "47"

; Balance with verification provenance (WHY it's verified)
2024-01-31 balance Assets:Chase:Checking  4523.17 USD
  verified-by: "sha256:a1b2c3d4e5f6..."
  verification: "opening 3521.45 + 47 txns = 4523.17"
  sources: "csv, pdf, api"
```

**Document directive metadata:**

| Field | Description |
|-------|-------------|
| `hash` | SHA-256 of original PDF/CSV (immutable reference) |
| `period` | Date range covered by statement |
| `extracted-by` | Engine used (e.g., `qwen3-vl:8b`, `azure-doc-intel`) |
| `extraction-confidence` | Ensemble confidence score (0.0-1.0) |
| `transactions-extracted` | Number of transactions extracted |

**Balance directive metadata:**

| Field | Description |
|-------|-------------|
| `verified-by` | Hash linking to document directive (provenance) |
| `verification` | Human-readable explanation of WHY it's verified |
| `sources` | Which sources agreed (e.g., "csv, pdf, api") |

**Benefits:**

- **Native Beancount**: Uses existing `document` directive
- **Separation of concerns**: Extraction metadata on document, verification on balance
- **Provenance chain**: Balance → hash → document → archived file
- **Self-explanatory**: `verification` field shows the math
- **Query-able**: `SELECT * FROM balance WHERE meta('sources') LIKE '%api%'`

### 4. Probabilistic Transaction Matching

Different sources describe the same transaction differently:

| Source | Description |
|--------|-------------|
| CSV | `AMZN MKTP US*2X4K7F9` |
| PDF | `AMAZON.COM AMZN.COM/BILL` |
| API | `Amazon` |

**Matching algorithm** (inspired by Splink/Plaid):

- **Blocking**: Only compare transactions with same amount + date±3 days
- **Field scoring**: Exact amount match (required), date proximity, description similarity
- **Probabilistic output**: 95% match confidence, not binary yes/no

### 5. Declarative Institution Profiles (No Code)

```yaml
# institutions/chase-checking.yaml
institution:
  name: Chase Bank
  country: US
  bic: CHASUS33

sources:
  csv:
    encoding: utf-8
    delimiter: ","
    skip_rows: 1
    columns:
      date: { index: 0, format: "MM/DD/YYYY" }
      description: { index: 2 }
      amount: { index: 3 }
      balance: { index: 4 }

  pdf:
    parser: chase-statement-v2
    balance_location: "Ending Balance"

  api:
    provider: plaid
    institution_id: ins_3

validation:
  balance_assertions: required
  minimum_sources: 1
  preferred_sources: [api, pdf, csv]

categorization:
  rules:
    - match: "AMAZON|AMZN"
      account: Expenses:Shopping:Amazon
    - match: "WHOLE FOODS|TRADER JOE"
      account: Expenses:Food:Groceries
    - match: "NETFLIX"
      account: Expenses:Subscriptions
```

**Community-maintained registry** of institution profiles.

### 6. The Trust Ladder

```
Level 0: UNVERIFIED
  └─ Single source, no validation

Level 1: PARSED
  └─ Successfully extracted from source

Level 2: BALANCED
  └─ Running balance matches statement

Level 3: CORROBORATED
  └─ 2+ sources agree on transactions

Level 4: RECONCILED
  └─ User reviewed and confirmed period

Level 5: AUDITED
  └─ External verification (tax filing accepted)
```

______________________________________________________________________

## Prior Art & Inspiration

### Data Matching & Reconciliation

| Project | What We Learn |
|---------|---------------|
| [**Splink**](https://github.com/moj-analytical-services/splink) | Fellegi-Sunter probabilistic matching, blocking rules, unsupervised learning |
| [**Plaid**](https://plaid.com/blog/finding-the-right-fit-how-plaid-reconciles-pending-and-posted-transactions/) | Boosted ML for pending→posted matching, fuzzy merchant extraction |
| [**Great Expectations**](https://greatexpectations.io/) | Declarative data validation, expectation suites |
| [**dbt**](https://docs.getdbt.com/docs/build/data-tests) | Tests as SQL queries, source-of-truth as code |

### Bank Data APIs

| Project | What We Learn |
|---------|---------------|
| [**SimpleFIN**](https://www.simplefin.org/) | Open protocol for bank data, standardized format |
| [**Plaid**](https://plaid.com/) | Transaction enrichment, merchant normalization |
| [**Teller**](https://teller.io/) | Direct bank API integration (no scraping) |

### Beancount Import Ecosystem

| Project | What We Learn |
|---------|---------------|
| [**beangulp**](https://github.com/beancount/beangulp) | Official Beancount importer framework: `identify()`, `account()`, `extract()` pattern, self-running importers with subcommands |
| [**smart_importer**](https://github.com/beancount/smart_importer) | ML-augmented importers using scikit-learn SVM for account/payee prediction, hooks system for wrapping importers |

### Document Extraction

| Project | What We Learn |
|---------|---------------|
| [**Reducto**](https://reducto.ai/) | Hybrid architecture: CV + VLM + Agentic OCR multi-pass correction |
| [**LayoutLMv3**](https://huggingface.co/docs/transformers/en/model_doc/layoutlm) | Document transformer combining text + layout + vision |
| [**DocTR**](https://github.com/mindee/doctr) | Open source, local-first OCR with table detection |
| [**Calamari**](https://github.com/Calamari-OCR/calamari) | Ensemble voting reduces OCR errors by 7x |
| [**Google Document AI**](https://cloud.google.com/document-ai) | Pre-trained bank statement models, HITL support |
| [**Azure Document Intelligence**](https://azure.microsoft.com/en-us/products/ai-services/ai-document-intelligence) | Bank statement extraction, confidence scoring |

### Transparency & Integrity

| Project | What We Learn |
|---------|---------------|
| [**Sigstore Rekor**](https://docs.sigstore.dev/logging/overview/) | Append-only transparency log, Merkle tree proofs |
| [**Git**](https://git-scm.com/) | Content-addressable storage, hash chains |
| [**IPFS**](https://ipfs.tech/) | Content-addressed immutable storage |

### Append-Only / Content-Addressed Database Patterns

These projects use similar patterns to what we need for source document storage:

#### Git Object Store

Git's object database is the canonical example of content-addressed storage:

| Aspect | Git's Approach | Our Application |
|--------|---------------|-----------------|
| **Object ID** | SHA-1/SHA-256 of content | SHA-256 of source document |
| **Storage** | `.git/objects/{hash[0:2]}/{hash[2:]}` | SQLite BLOB table keyed by hash |
| **Deduplication** | Identical content = same hash | Same statement uploaded twice = no duplication |
| **Immutability** | Objects never modified, only added | Sources never modified, extractions are new rows |
| **Compression** | zlib + delta encoding in pack files | zstd compression in SQLite |

**Key insight**: "The object store is like a database table with two columns: the object ID and the object content. The object ID is the hash of the object content and acts like a primary key." ([Git Internals](https://git-scm.com/book/en/v2/Git-Internals-Git-Objects))

#### Certificate Transparency Logs

CT logs solve a similar problem: immutable, append-only storage with cryptographic verification:

| Feature | CT Log | Our Source Archive |
|---------|--------|-------------------|
| **Structure** | Append-only Merkle tree | Append-only SQLite + Merkle root |
| **Entries** | TLS certificates | Source documents + extractions |
| **Proofs** | Inclusion proofs, consistency proofs | Same - prove document was archived at time T |
| **Guarantee** | Log can only grow, never shrink/rewrite | Database can only INSERT, never UPDATE/DELETE |

**Key insight**: "Logs are append-only — certificates can only be added to a log, not deleted, modified, or retroactively inserted." ([RFC 6962](https://www.rfc-editor.org/rfc/rfc6962.html))

Rust implementation: [`ct-merkle`](https://github.com/rozbb/ct-merkle) - append-only Merkle tree with inclusion/consistency proofs.

#### immudb (Immutable Database)

[immudb](https://github.com/codenotary/immudb) is purpose-built for exactly this use case:

```
Key features:
• Append-only: add new versions, never change/delete
• Merkle tree verification: cryptographic proof of integrity
• Time-travel: query state at any point in history
• Audit trail: complete history of all changes
• Embedded mode: can be linked as a library (like SQLite)
```

**Why we might use SQLite instead**:

- immudb is Go-only (no Rust bindings)
- SQLite is ubiquitous, battle-tested, single-file
- We can enforce append-only semantics at application layer
- immudb is overkill for single-user local use case

**What we learn from immudb**:

- Schema design: separate tables for data vs. audit entries
- Verification: periodically verify Merkle root integrity
- Time-travel queries: `SELECT * FROM sources AS OF TIMESTAMP '2024-01-15'`

#### Dolt (Git for Data)

[Dolt](https://github.com/dolthub/dolt) is MySQL-compatible with Git semantics:

| Feature | Dolt | Our Approach |
|---------|------|--------------|
| **Storage** | Content-addressed Merkle tree | Content-addressed by hash in SQLite |
| **Versioning** | Commits, branches, merges | Append-only rows with timestamps |
| **Diff** | `dolt diff` shows table changes | Compare extraction outputs by hash |
| **Query** | Standard SQL + version functions | Standard SQL |

**Key insight**: "The entire dataset is content-addressed as a Merkle Tree of component blocks... stored in write-once table files." ([Dolt Docs](https://docs.dolthub.com/))

#### Fossil (SQLite's VCS)

[Fossil](https://fossil-scm.org/) is the version control system used by SQLite itself:

```
"At its lowest level, a Fossil repository consists of an unordered
set of immutable 'artifacts'. The set of canonical artifacts for a
project is intended to be an append-only database."
```

**Key insight**: Fossil stores everything in a single SQLite file, proving that SQLite + append-only semantics is a viable architecture. Compression ratio of ~74:1 achieved through zlib + delta compression.

#### Event Sourcing Pattern

The [Event Sourcing pattern](https://microservices.io/patterns/data/event-sourcing.html) from Domain-Driven Design is philosophically identical:

```
Traditional DB:  Store current state, mutate in place
Event Sourcing:  Store all events, derive state by replay

Our system:      Store all source documents + extractions,
                 derive ledger by re-processing
```

**Benefits we inherit**:

- Complete audit trail (required for accounting!)
- Point-in-time reconstruction
- Debug by replaying events
- No data loss from "updates"

**Key insight**: "Instead of storing just the current state... you store the full series of actions taken on an object in an append-only store." ([Microsoft Azure Docs](https://learn.microsoft.com/en-us/azure/architecture/patterns/event-sourcing))

#### Content-Addressable SQLite (Textile)

[Textile's research](https://blog.textile.io/the-quest-for-a-content-addressable-sqlite) on content-addressable SQLite:

```
"Cloning or forking databases becomes as easy as copying a tiny
cryptographic hash. We also get extremely high concurrency because
the SQLite database is now a persistent, immutable data structure."
```

Uses a custom SQLite VFS that stores pages in content-addressable storage.

#### IPFS SQLite Block Store

[`ipfs-sqlite-block-store`](https://github.com/Actyx/ipfs-sqlite-block-store) - Rust crate for storing IPFS blocks in SQLite:

```rust
// Example: content-addressed storage in SQLite
pub struct BlockStore {
    db: Connection,
}

impl BlockStore {
    pub fn put(&self, cid: &Cid, data: &[u8]) -> Result<()> {
        // INSERT OR IGNORE - idempotent, deduplicating
        self.db.execute(
            "INSERT OR IGNORE INTO blocks (cid, data) VALUES (?, ?)",
            params![cid.to_bytes(), data],
        )
    }
}
```

**What we learn**: SQLite is a proven backend for content-addressed storage in Rust.

### Key Research

| Paper | Insight |
|-------|---------|
| [Fellegi-Sunter (1969)](https://www.tandfonline.com/doi/abs/10.1080/01621459.1969.10501049) | Probabilistic record linkage theory |
| [Consensus OCR Voting](https://dl.acm.org/doi/10.1006/cviu.1996.0502) | 20-50% error reduction with 3+ OCR engines |
| [HITL for IDP](https://www.intelligentdocumentprocessing.com/can-idp-achieve-100-accuracy-yes-and-no/) | 82% → 98% accuracy with human review of low-confidence items |

______________________________________________________________________

## Implementation Phases

### Phase 1: Foundation (v0.7.x) - COMPLETE

**Goal**: Basic import with balance validation

#### 1.1 Transaction Schema ✅

```rust
pub struct ImportedTransaction {
    // Core fields
    pub date: NaiveDate,
    pub description: String,
    pub amount: Decimal,
    pub balance: Option<Decimal>,  // Running balance if available

    // Source tracking
    pub source: DataSource,
    pub source_id: Option<String>,  // Bank's transaction ID
    pub raw_data: Option<String>,   // Original line/record

    // Matching
    pub fingerprint: TransactionFingerprint,
    pub confidence: f64,
}

pub struct TransactionFingerprint {
    pub date_hash: u64,      // date ± 1 day
    pub amount_hash: u64,    // exact amount
    pub desc_tokens: Vec<String>,  // normalized tokens
}
```

#### 1.2 CSV Parser Framework

- [x] Generic CSV parser with column mapping ✅
- [x] OFX/QFX parser ✅
- [x] CSV auto-inference (`--auto` flag) ✅
- [x] Enrichment pipeline (fingerprinting, categorization, confidence) ✅
- [ ] Institution profile loader (YAML/TOML)
- [ ] Built-in profiles for top 20 US banks
- [ ] Balance extraction and validation

#### 1.3 Balance Assertions

- [ ] Extract ending balance from CSV/statement
- [ ] Compare against ledger computed balance
- [x] Generate `balance` directives ✅ — `rledger extract --balance <AMOUNT> [--balance-date <DATE>]` appends a `balance` directive via `rustledger-ops::reconcile::create_balance_directive`. **Note:** the amount is user-supplied; automatic extraction from the statement is still future.
- [ ] Flag mismatches with diagnostic info

#### 1.4 CLI Commands

> **⚠️ Not implemented — aspirational design.** The `rledger import add/sync/status/validate`
> command family below was never built. The shipped interface is a single
> `rledger extract` command driven by `importers.toml` profiles (`--importer`)
> and WASM importers. See the note at the top of this document.

```bash
# Aspirational design (NOT implemented):
rledger import add <account>           # Configure new account
rledger import sync [account]          # Sync from configured sources
rledger import status                  # Show import status per account
rledger import validate <file>         # Validate CSV against ledger
```

**Deliverable**: Import CSVs with balance validation, no code required.

______________________________________________________________________

### Phase 2: Multi-Source Matching (v0.8.x)

**Goal**: Cross-validate transactions from multiple sources

#### 2.1 Matching Engine

- [ ] Blocking rules (same amount + date window)
- [ ] Probabilistic field comparison
- [ ] Confidence scoring
- [ ] Match group output

```rust
pub struct MatchResult {
    pub transactions: Vec<ImportedTransaction>,  // All sources
    pub confidence: f64,
    pub status: MatchStatus,
}

pub enum MatchStatus {
    Matched { sources: usize },     // 2+ sources agree
    SingleSource,                    // Only one source
    Conflict { reason: String },     // Sources disagree
}
```

#### 2.2 API Integration

- [ ] SimpleFIN client
- [ ] Plaid client (optional, requires API key)
- [ ] Teller client (optional)
- [ ] Rate limiting and caching

#### 2.3 Reconciliation UI

```
┌─────────────────────────────────────────────────────────────┐
│ Chase Checking - January 2024                    [Verified] │
├─────────────────────────────────────────────────────────────┤
│ Opening: $3,521.45  │  Closing: $4,523.17  │  Diff: ✅ $0   │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│ 01/05  Amazon          -$45.67   [CSV ✓] [API ✓]   95%     │
│ 01/07  Whole Foods    -$123.45   [CSV ✓] [API ✓]   98%     │
│ 01/10  Unknown         -$50.00   [CSV ✓] [API ✗]   ⚠️ 60%  │
│ 01/15  Payroll       +$2,500.00  [CSV ✓] [API ✓]   99%     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**Deliverable**: Import from multiple sources with cross-validation.

______________________________________________________________________

### Phase 3: Document Intelligence (v0.9.x)

**Goal**: Extract transactions from PDF statements

#### 3.1 PDF Processing Pipeline

```
PDF → OCR/Text Extract → Layout Analysis → Table Detection → Parsing
```

Options:

- **Local**: `pdfplumber` + heuristics
- **Cloud**: Azure Document AI / Google Document AI
- **LLM**: Vision model for complex layouts

#### 3.2 Statement Parser

- [ ] Detect transaction tables
- [ ] Extract header row
- [ ] Parse transaction rows
- [ ] Extract opening/closing balance
- [ ] Handle multi-page statements

#### 3.3 Parser Registry

```yaml
# parsers/chase-statement.yaml
name: chase-statement-v2
since: 2023-01-01

detection:
  - text_contains: "JPMorgan Chase Bank"
  - text_contains: "Account Summary"

layout:
  balance_opening:
    search: "Beginning Balance"
    offset: [+1, 0]  # Next cell
  balance_closing:
    search: "Ending Balance"
    offset: [+1, 0]
  transactions:
    table_header: ["Date", "Description", "Amount", "Balance"]

fields:
  date: { column: 0, format: "MM/DD" }
  description: { column: 1 }
  amount: { column: 2 }
  balance: { column: 3 }
```

**Deliverable**: Parse PDF statements without code.

______________________________________________________________________

### Phase 4: Intelligent Categorization (v1.0.x)

**Goal**: Auto-categorize transactions accurately

#### 4.1 Rule-Based Categorization ✅ IMPLEMENTED

Implemented in `rustledger-ops::categorize::RulesEngine`:

- Substring matching (case-insensitive)
- Regex patterns (compiled, case-insensitive)
- Exact matching
- Priority ordering (user rules > merchant dictionary)
- Built-in merchant dictionary with ~230 common patterns (`rustledger-ops::merchants`)

The importer integrates the rules engine via `CsvConfigBuilder::use_merchant_dict()` and
`CsvConfigBuilder::regex_mappings()`. User-defined `[importers.mappings]` in TOML config
are loaded as substring rules at priority 0, while merchant dictionary entries use
priority -1000 (always lower than user rules).

#### 4.2 ML-Assisted Categorization ✅ IMPLEMENTED

Implemented as a Naive Bayes classifier in `rustledger-ops::ml::CategorizationModel`
(`train` / `predict`), wired into the CLI via `rledger extract --suggest-categories`
(`crates/rustledger/src/cmd/extract_cmd/suggest.rs`). The model trains on the
`--existing` ledger and replaces fallback contra-accounts with its prediction for
transactions the rules engine left uncategorized.

- [x] Learn from user's existing ledger ✅
- [x] Suggest categories for new merchants ✅
- [ ] Improve with corrections (online learning) — still future

#### 4.3 Expected Transactions

```yaml
expected:
  - name: "Rent"
    amount: -2500.00
    day_of_month: 1
    account: Expenses:Housing:Rent
    alert_if_missing: true

  - name: "Salary"
    amount: 5000.00
    day_of_month: [1, 15]
    account: Income:Salary
```

**Deliverable**: Minimal manual categorization required.

______________________________________________________________________

### Phase 5: Ecosystem (v1.1.x+)

#### 5.1 Institution Registry

- [ ] Public GitHub repo of institution profiles
- [ ] Version control for parser changes
- [ ] Community contributions
- [ ] Automated testing against sample data

#### 5.2 Plugin System (WASM)

For edge cases that need custom logic:

```rust
#[wasm_bindgen]
pub trait ImportPlugin {
    fn name(&self) -> String;
    fn can_handle(&self, source: &DataSource) -> bool;
    fn parse(&self, data: &[u8]) -> Result<Vec<Transaction>>;
    fn validate(&self, txns: &[Transaction]) -> ValidationResult;
}
```

#### 5.3 Sync Daemon

- [ ] Background sync from APIs
- [ ] Push notifications for new transactions
- [ ] Anomaly detection (unusual amounts, new merchants)

______________________________________________________________________

## Data Model

### ImportConfig (per account)

```rust
pub struct ImportConfig {
    pub account: Account,
    pub institution: InstitutionProfile,
    pub sources: Vec<SourceConfig>,
    pub validation: ValidationConfig,
    pub categorization: CategorizationRules,
}
```

### SourceConfig

```rust
pub enum SourceConfig {
    Csv {
        path_pattern: String,  // e.g., "~/Downloads/chase-*.csv"
        profile: String,       // e.g., "chase-checking"
    },
    Api {
        provider: ApiProvider,
        credentials: CredentialRef,  // Reference to secure storage
        account_id: String,
    },
    Pdf {
        path_pattern: String,
        parser: String,
    },
}
```

### ValidationConfig

```rust
pub struct ValidationConfig {
    pub require_balance_match: bool,
    pub minimum_confidence: f64,      // e.g., 0.8
    pub minimum_sources: usize,       // e.g., 1
    pub flag_threshold: f64,          // Below this = review queue
}
```

______________________________________________________________________

## User Experience

### Initial Setup

```bash
$ rledger import add-account
? Select your bank: Chase
? Account type: Checking
? Account name in ledger: Assets:Chase:Checking
? Connect via SimpleFIN? [Y/n] Y
  → Opening browser for authentication...
  → Connected successfully
? Upload a recent statement PDF (optional): ~/Downloads/chase-jan-2024.pdf
  → Extracted 47 transactions
  → Opening balance: $3,521.45
  → Closing balance: $4,523.17 ✓
✅ Account configured
```

### Regular Sync

```bash
$ rledger import sync
Syncing Assets:Chase:Checking...
  → API: 12 new transactions
  → CSV: ~/Downloads/chase-feb-2024.csv found, 12 transactions
  → Matching: 12/12 matched across sources (100%)
  → Balance: Statement $5,847.23 = Ledger $5,847.23 ✓

Syncing Assets:Amex:Platinum...
  → API: 8 new transactions
  → Balance: Statement $2,341.56 ≠ Ledger $2,291.56 ⚠️
  → Difference: $50.00 (1 transaction missing?)

Review required for 1 account. Run `rledger import review` to resolve.
```

### Review Queue

```bash
$ rledger import review
Assets:Amex:Platinum has 1 issue:

Balance mismatch: -$50.00
  Statement: $2,341.56 (Feb 28, 2024)
  Ledger:    $2,291.56

Possible causes:
  1. Missing transaction around Feb 15-20 for ~$50
  2. Duplicate transaction removed incorrectly

Recent unmatched from API:
  Feb 18  COSTCO WHOLESALE  -$50.00  [Not in ledger]

? Import this transaction? [Y/n] Y
  → Added to ledger
  → Balance now matches ✓
```

______________________________________________________________________

## Security Considerations

- **Credentials**: Never stored in config files; use system keychain or env vars
- **API tokens**: Encrypted at rest, scoped to read-only
- **PDF parsing**: Sandboxed, no code execution
- **WASM plugins**: Sandboxed, no filesystem access

______________________________________________________________________

## Success Metrics

| Metric | Target |
|--------|--------|
| Balance match rate | >99% after reconciliation |
| Auto-categorization accuracy | >90% for known merchants |
| Manual intervention rate | \<5% of transactions |
| Time to import (1000 txns) | \<5 seconds |
| Supported institutions | Top 50 US banks at launch |

______________________________________________________________________

## Open Questions

### Extraction

1. ~~**LLM for PDF parsing**: Local (slow) vs cloud (privacy concerns)?~~ → User configurable
1. **Local LLM options**: Which local models work well? (llama.cpp, Ollama, etc.)
1. **Ensemble weighting**: How to weight different OCR engines? Learn from corrections?

### APIs & Pricing

4. **Plaid pricing**: $0.30/connection/month - include or require user's own key?
1. **SimpleFIN**: $15/year - recommend as default? Or make optional?

### Data Management

6. **Historical import**: Bulk import years of data vs incremental only?
1. **Multi-currency**: How to handle FX transactions from travel cards?
1. **Storage limits**: Archive compression? Remote backup options?

### Transparency Log

9. **Log format**: Custom binary vs SQLite vs JSON lines?
1. **Merkle tree library**: Build vs use existing (e.g., `merkle-tree-rs`)?
1. **Public attestation**: Partner with Sigstore? Or self-hosted Rekor?

### User Experience

12. **Offline-first**: How to handle API-only institutions without internet?
01. **Conflict resolution**: When sources disagree, what's the UX?
01. **Mobile**: How to handle statement import from phone photos?

______________________________________________________________________

## References

### Data Matching & Reconciliation

- [Splink Documentation](https://moj-analytical-services.github.io/splink/)
- [Plaid Transaction Reconciliation](https://plaid.com/blog/finding-the-right-fit-how-plaid-reconciles-pending-and-posted-transactions/)
- [Great Expectations](https://greatexpectations.io/)
- [Fellegi-Sunter Model (1969)](https://www.tandfonline.com/doi/abs/10.1080/01621459.1969.10501049)

### Document Extraction

- [Reducto Hybrid Architecture](https://reducto.ai/)
- [LayoutLM Paper](https://arxiv.org/abs/1912.13318)
- [DocTR](https://github.com/mindee/doctr)
- [Calamari OCR](https://github.com/Calamari-OCR/calamari)
- [Consensus OCR Voting](https://dl.acm.org/doi/10.1006/cviu.1996.0502)
- [HITL for IDP](https://www.intelligentdocumentprocessing.com/can-idp-achieve-100-accuracy-yes-and-no/)
- [OmniAI OCR Benchmark](https://getomni.ai/blog/ocr-benchmark)
- [SCORE-Bench](https://unstructured.io/blog/introducing-score-bench-an-open-benchmark-for-document-parsing)

### Bank Data

- [SimpleFIN Protocol](https://www.simplefin.org/protocol.html)
- [Teller API](https://teller.io/)
- [hledger CSV import](https://hledger.org/import-csv.html)

### Beancount Import Ecosystem

- [beangulp](https://github.com/beancount/beangulp) - Official Beancount v3 importer framework with `identify()`, `account()`, `extract()` interface
- [smart_importer](https://github.com/beancount/smart_importer) - ML-augmented importers using scikit-learn SVM for account prediction
- [beancount_reds_importers](https://github.com/redstreet/beancount_reds_importers) - Community importers framework

### Transparency & Integrity

- [Sigstore Rekor](https://docs.sigstore.dev/logging/overview/)
- [Merkle Trees Explained](https://en.wikipedia.org/wiki/Merkle_tree)
- [Content-Addressable Storage](https://en.wikipedia.org/wiki/Content-addressable_storage)

### Append-Only Database Patterns

- [Git Object Database](https://git-scm.com/book/en/v2/Git-Internals-Git-Objects) - The canonical content-addressed storage design
- [Git Database Internals (GitHub Blog)](https://github.blog/open-source/git/gits-database-internals-i-packed-object-store/) - Pack files and compression
- [Certificate Transparency RFC 6962](https://www.rfc-editor.org/rfc/rfc6962.html) - Append-only Merkle tree logs
- [CT RFC 9162 (v2.0)](https://www.rfc-editor.org/rfc/rfc9162.html) - Updated CT specification
- [ct-merkle (Rust crate)](https://github.com/rozbb/ct-merkle) - CT-style Merkle tree in Rust
- [immudb](https://github.com/codenotary/immudb) - Immutable database with Merkle verification
- [Dolt](https://github.com/dolthub/dolt) - Git for data, MySQL-compatible
- [Fossil VCS](https://fossil-scm.org/home/doc/tip/www/tech_overview.wiki) - SQLite's own version control, append-only artifacts
- [Event Sourcing Pattern (Microsoft)](https://learn.microsoft.com/en-us/azure/architecture/patterns/event-sourcing) - Append-only event stores
- [Event Sourcing Pattern (microservices.io)](https://microservices.io/patterns/data/event-sourcing.html) - Detailed pattern explanation
- [Content-Addressable SQLite (Textile)](https://blog.textile.io/the-quest-for-a-content-addressable-sqlite) - CAS-backed SQLite VFS
- [ipfs-sqlite-block-store](https://github.com/Actyx/ipfs-sqlite-block-store) - IPFS blocks in SQLite (Rust)

### Rust Crates for OCR/Extraction

- [ort](https://github.com/pykeio/ort) - ONNX Runtime bindings for Rust
- [tesseract-rs](https://github.com/cafercangundogdu/tesseract-rs) - Tesseract with bundled compilation
- [leptess](https://github.com/houqp/leptess) - Tesseract/Leptonica bindings
- [rust-paddle-ocr](https://github.com/zibo-chen/rust-paddle-ocr) - PaddleOCR with MNN backend
- [PaddleOCR.rs](https://github.com/OXeu/PaddleOCR.rs) - PaddleOCR V3 inference
- [OnnxTR](https://github.com/felixdittrich92/OnnxTR) - DocTR models in ONNX format
- [image](https://github.com/image-rs/image) - Image processing
- [pdf](https://github.com/nicoulaj/pdf) - PDF parsing

### Python Libraries (for reference/interop)

- [pdfplumber](https://github.com/jsvine/pdfplumber) - PDF→image conversion (proven for statement extraction)
- [Ollama](https://ollama.ai/) - Local LLM inference server
- [qwen3-vl](https://ollama.com/library/qwen3-vl) - Vision model with high accuracy for documents

### Local Vision Models (via Ollama)

- `qwen3-vl:8b` - Best accuracy, ~150s/page on RTX 3090
- `minicpm-v` - Fast mode, ~20-30s/page, lower accuracy
