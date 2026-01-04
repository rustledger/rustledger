# Architecture Overview

This document describes the high-level architecture of rustledger.

## System Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              rustledger                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │
│  │   CLI       │    │   WASM      │    │   Library   │    │    LSP      │  │
│  │ (bean-check │    │  (Browser)  │    │    API      │    │  (Editor)   │  │
│  │  bean-query)│    │             │    │             │    │             │  │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘    └──────┬──────┘  │
│         │                  │                  │                  │         │
│         └──────────────────┴────────┬─────────┴──────────────────┘         │
│                                     │                                       │
│                          ┌──────────▼──────────┐                           │
│                          │   beancount-core    │                           │
│                          │  (Processing Pipeline)                          │
│                          └──────────┬──────────┘                           │
│                                     │                                       │
│    ┌────────────┬───────────────────┼───────────────────┬────────────┐     │
│    │            │                   │                   │            │     │
│    ▼            ▼                   ▼                   ▼            ▼     │
│ ┌──────┐  ┌──────────┐  ┌───────────────────┐  ┌──────────┐  ┌─────────┐  │
│ │Parser│  │  Loader  │  │     Booking       │  │Validation│  │  Query  │  │
│ │      │  │          │  │  (Interpolation)  │  │          │  │  (BQL)  │  │
│ └──────┘  └──────────┘  └───────────────────┘  └──────────┘  └─────────┘  │
│                                                                             │
│                          ┌──────────────────────┐                          │
│                          │    Plugin Host       │                          │
│                          │    (wasmtime)        │                          │
│                          └──────────────────────┘                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Crate Structure

```
rustledger/
├── crates/
│   ├── beancount-core/       # Core types and traits
│   ├── beancount-parser/     # Lexer and parser
│   ├── beancount-loader/     # File loading and includes
│   ├── beancount-booking/    # Interpolation and booking engine
│   ├── beancount-validate/   # Validation rules
│   ├── beancount-query/      # BQL query engine
│   ├── beancount-plugin/     # WASM plugin runtime
│   └── beancount-cli/        # CLI tools
├── Cargo.toml                # Workspace definition
└── spec/                     # Specifications (this folder)
```

## Crate Dependencies

```
                    ┌─────────────────┐
                    │  beancount-cli  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
              ▼              ▼              ▼
    ┌─────────────┐  ┌─────────────┐  ┌─────────────┐
    │   -query    │  │  -validate  │  │   -plugin   │
    └──────┬──────┘  └──────┬──────┘  └──────┬──────┘
           │                │                │
           │         ┌──────┴──────┐         │
           │         │             │         │
           ▼         ▼             │         ▼
    ┌─────────────────────┐        │  ┌─────────────┐
    │  beancount-booking  │        │  │  wasmtime   │
    └──────────┬──────────┘        │  └─────────────┘
               │                   │
               ▼                   │
    ┌─────────────────────┐        │
    │  beancount-loader   │◄───────┘
    └──────────┬──────────┘
               │
               ▼
    ┌─────────────────────┐
    │  beancount-parser   │
    └──────────┬──────────┘
               │
               ▼
    ┌─────────────────────┐
    │   beancount-core    │
    └─────────────────────┘
               │
               ▼
    ┌─────────────────────┐
    │    rust_decimal     │
    │    chrono           │
    └─────────────────────┘
```

## Processing Pipeline

```
┌──────────────────────────────────────────────────────────────────────────┐
│                         PROCESSING PIPELINE                               │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────┐   ┌────────┐   ┌────────┐   ┌────────┐   ┌────────┐        │
│  │ Source │──▶│  Lex   │──▶│ Parse  │──▶│  AST   │──▶│ Expand │        │
│  │ Files  │   │        │   │        │   │        │   │Includes│        │
│  └────────┘   └────────┘   └────────┘   └────────┘   └───┬────┘        │
│                                                          │              │
│  Phase 1: PARSING                                        │              │
│  ─────────────────────────────────────────────────────────              │
│                                                          │              │
│                                                          ▼              │
│  ┌────────┐   ┌────────┐   ┌────────┐   ┌────────┐   ┌────────┐        │
│  │ Apply  │◀──│ Plugin │◀──│Validate│◀──│  Book  │◀──│Interpolate     │
│  │ Plugins│   │  Host  │   │  Accts │   │  Lots  │   │ Amounts│        │
│  └───┬────┘   └────────┘   └────────┘   └────────┘   └────────┘        │
│      │                                                                  │
│  Phase 2: BOOKING & VALIDATION                                          │
│  ─────────────────────────────────────────────────────────              │
│      │                                                                  │
│      ▼                                                                  │
│  ┌────────┐   ┌────────┐   ┌────────┐                                  │
│  │Validate│──▶│ Collect│──▶│ Ledger │                                  │
│  │Balance │   │ Errors │   │(final) │                                  │
│  └────────┘   └────────┘   └────────┘                                  │
│                                                                          │
│  Phase 3: FINAL VALIDATION                                              │
│  ─────────────────────────────────────────────────────────              │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
```

## Data Flow

### Phase 1: Parsing

```
Source Text
    │
    ▼
┌─────────────────┐
│     Lexer       │  Produces tokens with spans
│  (chumsky/      │
│   winnow)       │
└────────┬────────┘
         │
         ▼
    Token Stream
         │
         ▼
┌─────────────────┐
│     Parser      │  Produces AST with spans
│                 │  Option<Amount> for missing values
└────────┬────────┘
         │
         ▼
   Vec<Directive>
   + ParseErrors
         │
         ▼
┌─────────────────┐
│     Loader      │  Resolves includes, collects options
│                 │  Handles cycles, builds SourceMap
└────────┬────────┘
         │
         ▼
   Vec<Directive>  (merged from all files)
   + Options
   + SourceMap
```

### Phase 2: Booking

```
   Vec<Directive>
         │
         ▼
┌─────────────────┐
│   Sort by Date  │  Stable sort, non-txns before txns
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Interpolation  │  Fill Option<Amount> → Amount
│                 │  Using transaction balance equation
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│    Booking      │  Match reductions to lots
│                 │  FIFO/LIFO/STRICT/NONE
│                 │  Update Inventory per account
└────────┬────────┘
         │
         ▼
   Vec<Directive>  (fully specified)
   + HashMap<Account, Inventory>
```

### Phase 3: Validation

```
   Vec<Directive>
   + Inventories
         │
         ▼
┌─────────────────┐
│ Account Check   │  Open before use, not used after close
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Balance Check   │  Assertions match computed balance
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Currency Check  │  Constraints honored
└────────┬────────┘
         │
         ▼
     Ledger
   + Vec<Error>
```

## Core Type Relationships

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           CORE TYPES                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────┐                                                       │
│  │    Ledger    │                                                       │
│  ├──────────────┤                                                       │
│  │ directives   │───────────▶ Vec<Directive>                           │
│  │ options      │───────────▶ Options                                  │
│  │ accounts     │───────────▶ HashMap<Account, AccountState>           │
│  │ inventories  │───────────▶ HashMap<Account, Inventory>              │
│  │ errors       │───────────▶ Vec<Error>                               │
│  └──────────────┘                                                       │
│                                                                         │
│  ┌──────────────┐         ┌──────────────┐                             │
│  │  Directive   │         │ Transaction  │                             │
│  ├──────────────┤         ├──────────────┤                             │
│  │ Transaction ─┼────────▶│ date         │                             │
│  │ Balance      │         │ flag         │                             │
│  │ Open         │         │ payee        │                             │
│  │ Close        │         │ narration    │                             │
│  │ Commodity    │         │ postings ────┼──▶ Vec<Posting>             │
│  │ Pad          │         │ tags         │                             │
│  │ Event        │         │ links        │                             │
│  │ Query        │         │ metadata     │                             │
│  │ Note         │         └──────────────┘                             │
│  │ Document     │                                                       │
│  │ Price        │         ┌──────────────┐                             │
│  │ Custom       │         │   Posting    │                             │
│  └──────────────┘         ├──────────────┤                             │
│                           │ account      │                             │
│                           │ units ───────┼──▶ Option<Amount>           │
│  ┌──────────────┐         │ cost ────────┼──▶ Option<CostSpec>         │
│  │    Amount    │         │ price ───────┼──▶ Option<Amount>           │
│  ├──────────────┤         │ metadata     │                             │
│  │ number ──────┼──▶ Decimal              └──────────────┘             │
│  │ currency ────┼──▶ String                                            │
│  └──────────────┘                                                       │
│                           ┌──────────────┐                             │
│  ┌──────────────┐         │   Position   │                             │
│  │     Cost     │         ├──────────────┤                             │
│  ├──────────────┤         │ units ───────┼──▶ Amount                   │
│  │ number       │         │ cost ────────┼──▶ Option<Cost>             │
│  │ currency     │         └──────────────┘                             │
│  │ date         │                                                       │
│  │ label        │         ┌──────────────┐                             │
│  └──────────────┘         │  Inventory   │                             │
│                           ├──────────────┤                             │
│                           │ positions ───┼──▶ Vec<Position>            │
│                           └──────────────┘                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Plugin Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PLUGIN ARCHITECTURE                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Beancount File                                                        │
│   ─────────────                                                         │
│   plugin "myplugin.wasm" "config"                                       │
│                                                                         │
│         │                                                               │
│         ▼                                                               │
│   ┌─────────────────┐                                                   │
│   │   Plugin Host   │                                                   │
│   │   (Rust)        │                                                   │
│   ├─────────────────┤                                                   │
│   │ load_plugin()   │───────▶ Compile WASM module                      │
│   │ run_plugin()    │───────▶ Serialize directives                     │
│   └────────┬────────┘         Call WASM function                       │
│            │                  Deserialize results                       │
│            │                                                            │
│            ▼                                                            │
│   ┌─────────────────┐      ┌─────────────────┐                         │
│   │    wasmtime     │      │  WASM Module    │                         │
│   │    Runtime      │◀────▶│  (plugin.wasm)  │                         │
│   └─────────────────┘      ├─────────────────┤                         │
│                            │ fn process(     │                         │
│   Sandbox:                 │   input: bytes  │                         │
│   • No filesystem          │ ) -> bytes      │                         │
│   • No network             └─────────────────┘                         │
│   • Memory limited                                                      │
│   • CPU time limited                                                    │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────┐      │
│   │                    WASM BOUNDARY                             │      │
│   ├─────────────────────────────────────────────────────────────┤      │
│   │                                                             │      │
│   │   Rust (Host)              │      WASM (Plugin)             │      │
│   │   ───────────              │      ─────────────             │      │
│   │                            │                                │      │
│   │   Vec<Directive>  ────serialize────▶  bytes                │      │
│   │                            │            │                   │      │
│   │                            │            ▼                   │      │
│   │                            │      Plugin Logic              │      │
│   │                            │      (any language)            │      │
│   │                            │            │                   │      │
│   │   Vec<Directive>  ◀───deserialize───  bytes                │      │
│   │   Vec<Error>               │                                │      │
│   │                            │                                │      │
│   └─────────────────────────────────────────────────────────────┘      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Query Engine Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        BQL QUERY ENGINE                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   "SELECT account, sum(position) WHERE account ~ 'Expenses' GROUP BY 1" │
│                              │                                          │
│                              ▼                                          │
│                    ┌─────────────────┐                                  │
│                    │   BQL Parser    │                                  │
│                    │   (SQL-like)    │                                  │
│                    └────────┬────────┘                                  │
│                             │                                           │
│                             ▼                                           │
│                    ┌─────────────────┐                                  │
│                    │   Query AST     │                                  │
│                    │                 │                                  │
│                    │ • SELECT cols   │                                  │
│                    │ • FROM filter   │                                  │
│                    │ • WHERE filter  │                                  │
│                    │ • GROUP BY      │                                  │
│                    │ • ORDER BY      │                                  │
│                    └────────┬────────┘                                  │
│                             │                                           │
│                             ▼                                           │
│                    ┌─────────────────┐                                  │
│                    │ Query Planner   │                                  │
│                    │                 │                                  │
│                    │ • Optimize      │                                  │
│                    │ • Plan scans    │                                  │
│                    └────────┬────────┘                                  │
│                             │                                           │
│                             ▼                                           │
│   ┌─────────────────────────────────────────────────────────────┐      │
│   │                     Execution Engine                         │      │
│   ├─────────────────────────────────────────────────────────────┤      │
│   │                                                             │      │
│   │  Ledger ──▶ FROM Filter ──▶ Posting Iterator ──▶ WHERE     │      │
│   │                                                    Filter   │      │
│   │                                                      │      │      │
│   │                                                      ▼      │      │
│   │           Results ◀── Format ◀── ORDER/LIMIT ◀── GROUP BY  │      │
│   │                                                             │      │
│   └─────────────────────────────────────────────────────────────┘      │
│                                                                         │
│   Special Types:                                                        │
│   • Inventory: multi-lot aggregation                                   │
│   • Position: single lot with cost                                     │
│   • Amount: number + currency                                          │
│                                                                         │
│   Built-in Functions:                                                   │
│   • sum(), count(), first(), last(), min(), max()                      │
│   • units(), cost(), value(), weight()                                 │
│   • year(), month(), day(), parent(), leaf()                           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Error Handling Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        ERROR HANDLING                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Each Phase Produces Errors                                            │
│   ──────────────────────────                                            │
│                                                                         │
│   ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐        │
│   │  Parse   │    │  Book    │    │ Validate │    │  Plugin  │        │
│   │  Errors  │    │  Errors  │    │  Errors  │    │  Errors  │        │
│   └────┬─────┘    └────┬─────┘    └────┬─────┘    └────┬─────┘        │
│        │               │               │               │               │
│        └───────────────┴───────┬───────┴───────────────┘               │
│                                │                                        │
│                                ▼                                        │
│                    ┌─────────────────────┐                             │
│                    │  Error Collector    │                             │
│                    ├─────────────────────┤                             │
│                    │ • Deduplicate       │                             │
│                    │ • Sort by location  │                             │
│                    │ • Limit count       │                             │
│                    └──────────┬──────────┘                             │
│                               │                                         │
│                               ▼                                         │
│                    ┌─────────────────────┐                             │
│                    │  Error Renderer     │                             │
│                    │  (ariadne/miette)   │                             │
│                    └──────────┬──────────┘                             │
│                               │                                         │
│                               ▼                                         │
│   ┌─────────────────────────────────────────────────────────────┐      │
│   │ error[E1001]: Account "Assets:Unknown" is not open          │      │
│   │   --> ledger.beancount:42:3                                  │      │
│   │    |                                                         │      │
│   │ 42 |   Assets:Unknown  100 USD                               │      │
│   │    |   ^^^^^^^^^^^^^^ account used here                      │      │
│   │    |                                                         │      │
│   │    = help: add `open Assets:Unknown` before this line        │      │
│   └─────────────────────────────────────────────────────────────┘      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Memory Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        MEMORY LAYOUT                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   String Interning (for accounts, currencies)                           │
│   ───────────────────────────────────────────                           │
│                                                                         │
│   ┌─────────────────────────────────────────┐                          │
│   │           String Interner               │                          │
│   ├─────────────────────────────────────────┤                          │
│   │ "Assets:Cash"          → StringId(0)    │                          │
│   │ "Expenses:Food"        → StringId(1)    │                          │
│   │ "USD"                  → StringId(2)    │                          │
│   │ "EUR"                  → StringId(3)    │                          │
│   └─────────────────────────────────────────┘                          │
│                                                                         │
│   Account and Currency use StringId instead of String                   │
│   → Faster comparison (integer vs string)                               │
│   → Less memory (4 bytes vs 24+ bytes per reference)                   │
│   → Cache-friendly                                                      │
│                                                                         │
│   Arena Allocation (for AST nodes)                                      │
│   ────────────────────────────────                                      │
│                                                                         │
│   ┌─────────────────────────────────────────┐                          │
│   │              AST Arena                  │                          │
│   ├─────────────────────────────────────────┤                          │
│   │ [Directive][Directive][Directive]...    │                          │
│   │ [Posting][Posting][Posting]...          │                          │
│   │ [Metadata][Metadata]...                 │                          │
│   └─────────────────────────────────────────┘                          │
│                                                                         │
│   All AST nodes allocated in contiguous arena                           │
│   → Single deallocation                                                 │
│   → Cache-friendly iteration                                            │
│   → No reference counting overhead                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Threading Model

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        THREADING MODEL                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Parse Phase: Parallel per file                                        │
│   ──────────────────────────────                                        │
│                                                                         │
│   ┌────────┐  ┌────────┐  ┌────────┐                                   │
│   │ File 1 │  │ File 2 │  │ File 3 │                                   │
│   └───┬────┘  └───┬────┘  └───┬────┘                                   │
│       │           │           │                                         │
│       ▼           ▼           ▼                                         │
│   ┌────────┐  ┌────────┐  ┌────────┐                                   │
│   │Thread 1│  │Thread 2│  │Thread 3│    (parallel)                     │
│   │ parse  │  │ parse  │  │ parse  │                                   │
│   └───┬────┘  └───┬────┘  └───┬────┘                                   │
│       │           │           │                                         │
│       └───────────┼───────────┘                                         │
│                   │                                                      │
│                   ▼                                                      │
│              ┌─────────┐                                                │
│              │  Merge  │  (single-threaded)                             │
│              └────┬────┘                                                │
│                   │                                                      │
│   Booking Phase: Sequential (stateful)                                  │
│   ────────────────────────────────────                                  │
│                   │                                                      │
│                   ▼                                                      │
│              ┌─────────┐                                                │
│              │Booking  │  Must be sequential:                           │
│              │Engine   │  inventory state depends on order              │
│              └────┬────┘                                                │
│                   │                                                      │
│   Query Phase: Parallel per query                                       │
│   ───────────────────────────────                                       │
│                   │                                                      │
│                   ▼                                                      │
│   ┌────────┐  ┌────────┐  ┌────────┐                                   │
│   │Query 1 │  │Query 2 │  │Query 3 │    (parallel, read-only)          │
│   └────────┘  └────────┘  └────────┘                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```
