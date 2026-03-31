# Documentation Issues Found

## Issue #1: Release Asset Names (installation.md)

**Location:** `docs/getting-started/installation.md`

**Problem:** Documented filenames don't include version number

**Docs say:**
```
rustledger-x86_64-unknown-linux-gnu.tar.gz
```

**Actual:**
```
rustledger-v0.10.1-x86_64-unknown-linux-gnu.tar.gz
```

**Fix:** Update table to show versioned filenames or use `rustledger-<version>-<target>.tar.gz` pattern

---

## Issue #2: VS Code Extension Doesn't Exist (editor-integration.md)

**Location:** `docs/guides/editor-integration.md`

**Problem:** Claims a VS Code extension exists that doesn't

**Docs say:**
```bash
code --install-extension rustledger.rustledger-vscode
```

**Reality:** This extension does NOT exist in VS Code marketplace

**Docs also claim these settings exist:**
```json
{
  "rustledger.path": "rledger",
  "rustledger.checkOnSave": true,
  "rustledger.formatting.enabled": true
}
```

**Reality:** These settings are completely fabricated - no extension implements them

**Fix:** Remove fake extension docs, document using generic LSP client instead

---

## Issue #3: Non-existent Beancount Setting (rustledger-lsp/README.md)

**Location:** `crates/rustledger-lsp/README.md`

**Problem:** Claims a Beancount extension setting exists

**Docs say:**
```json
{
  "beancount.languageServerPath": "rledger-lsp"
}
```

**Reality:** No Beancount VS Code extension supports this setting:
- Lencerf.beancount - syntax only, no LSP
- polarmutex.beancount-langserver - uses own LSP, no custom path
- fengkx.beancount-lsp-client - uses `beanLsp.*` settings

**Fix:** Document using generic LSP client or state VS Code is not well-supported

---

## Issue #4: Inconsistent VS Code Documentation

**Problem:** Two different docs (LSP README vs website) have completely different (both wrong) VS Code instructions

- LSP README: claims `beancount.languageServerPath`
- Website: claims `rustledger.rustledger-vscode` extension

**Fix:** Consolidate to one correct source of truth

---

## Issue #5: Missing Command Docs

**Commands with no documentation:**
- `add` - exists in CLI, no docs
- `config` - exists in CLI, no docs

---

## Issue #6: Incomplete Command Option Documentation

**check command missing:**
- `-q, --quiet`
- `-C, --no-cache`
- `-a, --auto`
- `--plugin` (WASM plugins)

**query command missing:**
- `-F, --query-file`
- `-o, --output`
- `-m, --numberify`
- `-q, --no-errors`
- `beancount` format option

**format command missing:** (need to verify)
**extract command missing:** (need to verify)

---

## Issue #7: Massive Plugin Documentation Gap

**Location:** `docs/reference/plugins.md`

**Problem:** Only 12 of 31 plugins are documented

**Missing plugins (19 total):**
- `generate_base_ccy_prices`
- `rename_accounts`
- `forecast`
- `auto_tag`
- `capital_gains_classifier` (long_short variant)
- `capital_gains_classifier` (gain_loss variant)
- `currency_accounts`
- `document_discovery`
- `rx_txn`
- `effective_date`
- `check_drained`
- `box_accrual`
- `check_average_cost`
- `check_closing`
- `no_unused`
- `unrealized`
- `zerosum`
- `commodity_attr`
- `valuation`

---

## Issue #8: BQL Documentation Claims Non-existent Features

**Location:** `docs/reference/bql.md`

**Problems found by testing:**

### 8a. `FROM entries` doesn't work
```sql
SELECT * FROM entries
```
**Error:** `table 'entries' does not exist`

Docs say FROM is "optional" and defaults to "entries", but the table doesn't exist.

### 8b. FILTER clause doesn't parse
```sql
SELECT sum(cost(position)) FILTER (WHERE year(date) = 2024)
```
**Error:** `parse error at position 27: unexpected end of input`

Year-over-year example in docs is broken.

### 8c. Date arithmetic doesn't work
```sql
WHERE date >= today() - 30
```
**Error:** `arithmetic requires numeric values`

"Last 30 days" example in docs is broken.

### 8d. Case-insensitive regex doesn't parse
```sql
WHERE account ~* "assets"
```
**Error:** parse error

Documented `~*` operator doesn't exist.

**BQL Features That DO Work:**
- ✅ Basic SELECT, WHERE, GROUP BY, ORDER BY, LIMIT
- ✅ Regular regex matching (`~`)
- ✅ Date functions: year(), month(), day(), quarter(), weekday(), today()
- ✅ Account functions: root(), leaf(), parent()
- ✅ Amount functions: cost(), units(), currency(), number()
- ✅ String functions: length()
- ✅ Aggregates: sum(), count(), first(), last(), min(), max()
- ✅ Tags filtering: `"tag" IN tags`
- ✅ IN operator with lists
- ✅ Column aliases (AS)

---

## Issue #9: Crate README Inconsistencies

**Location:** `crates/rustledger-query/README.md`

### 9a. Claims "Subqueries" but they're not supported
Line 22: "Subqueries and PIVOT tables"

**Reality:** Main BQL docs explicitly state "Subqueries: Not currently supported"

### 9b. UPPER/LOWER functions not documented in main BQL reference
Query README lists: "String functions (LENGTH, UPPER, LOWER)"

**Reality:** These functions WORK but aren't documented in `docs/reference/bql.md`

### 9c. PIVOT BY syntax undocumented
Query README mentions "PIVOT tables" but doesn't explain syntax.

**Actual syntax:** `SELECT ... GROUP BY 1, 2 PIVOT BY <column_index>`

Example that works:
```sql
SELECT account, year(date), sum(position) GROUP BY 1, 2 PIVOT BY 2
```

---

## Verified Working

- ✅ Homebrew formula exists (v0.10.1)
- ✅ AUR package exists (rustledger-bin)
- ✅ Fedora COPR exists
- ✅ Scoop bucket exists
- ✅ Shell completions work
- ✅ `rledger-lsp` binary builds
- ✅ Neovim config looks correct (uses standard lspconfig pattern)
- ✅ Helix config looks correct
- ✅ Emacs configs look correct
- ✅ Sublime Text config looks correct
- ✅ MCP server README matches available tools
- ✅ FFI WASI README looks comprehensive
- ✅ WASM README examples look correct
- ✅ Importer README pattern looks correct
- ✅ Plugin README lists all 30 native plugins correctly
- ✅ Main CLI README commands list is correct

## Still To Verify

- [x] Command docs vs --help (Issue #5, #6)
- [x] BQL examples actually run (Issue #8)
- [x] Plugin list matches code (Issue #7)
- [x] All crate README examples (Issue #9)
