# ADR-0009: The formatter certifies its own output

## Status

Accepted. Phases A (the certifier) and B (one frame, fixed-point
idempotence) are implemented; phase C is planned (see
[Phase plan](#phase-plan)).

## Context

`rledger format` (and every surface built on the same function: the LSP's
document and range formatting, the WASM and FFI `format` calls, `doctor
roundtrip`) makes five promises about its output:

1. **Meaning.** Beancount reads the output as it reads the input: the same
   directives, decimal scale included; the same errors on the same
   statements; the same comments in the same slots.
1. **Idempotence.** `f(f(x)) == f(x)`.
1. **No loss.** Text the formatter does not own (a line it cannot parse, a
   comment) is never deleted or altered.
1. **Canonical form.** A clean ledger has exactly one formatted form, a pure
   function of its parse tree (#1262, PR #1284; the gofmt-style design, kept).
1. **Range = whole.** Formatting a range gives what formatting the whole file
   gives, restricted to that range.

Only promise 4 held by construction. The others rested on a stack of
exceptions, each counting lines or bytes in its own frame: a pre-parse fold of
`\r\n` into `\n`; `RepairedLines`, which undoes the fold where the fold
repaired a broken line; `keep_bom_before_a_second`; `ErrorRanges::keep_cr` and
its BOM offset; the last-line newline rules; the string-aware
`crlf_to_lf_outside_strings` / `lf_to_crlf_outside_strings` scanners. Where two
of those frames disagreed, the formatter broke a promise, and the nightly
fuzzer kept finding such disagreements (#3084: an input that gained a `\n` on
every pass; its root cause was two token streams that disagreed about a
second BOM, fixed in #3085). An exhaustive sweep of short inputs found a
meaning bug of the same family: `2024-01-01 A; ` (a broken line without a
final newline) formatted to `2024-01-01 A;\n`, which reads a comment the
input did not have.

Each fix closed one disagreement. None closed the class: the promises were
properties of the interaction of the exceptions, checked only after the fact
by a test oracle (`fuzz/fuzz_targets/common/format_roundtrip.rs`).

## Decision

**The formatter checks its own output, item by item, and keeps as written any
item whose canonical form does not read back as the original did.** Three
stages:

1. **Classify.** Parse the source as written, once, in one frame (no text is
   rewritten before the parse: the lexer reads `\r\n` as a line ending and a
   stray `\r` run as trivia). Split the file into items: each top-level node of the tree
   (a directive, or a region the parser could not read) is one, and the text
   between them (blank lines, file-level comments, a BOM) is the separator.
   An item holding a parse error (reported, or quieted by bison's recovery
   window: `ParseResult` errors and `defect_spans`, the oracle-calibrated
   classification, not a second classifier) is **opaque**: copied byte for
   byte, from its first non-blank line to the end of its last one, that
   line's own line ending included. Every other item is **clean**: rebuilt by
   the canonical emitter.
1. **Emit.** Clean items through the existing canonical `emit_*` functions,
   unchanged; opaque items verbatim; the separator by the driver's spacing
   rules. The driver owns every byte it writes: the blank lines and comments
   between items, the final newline (not after an opaque last line, which
   would be a change to text it does not own), the leading BOM (dropped,
   unless a second BOM follows), and the line ending of every line it or the
   emitter writes, `\n` or, as an option, `\r\n` (the LSP on a CRLF
   document). The writer records the line endings it writes, so the emitter
   finds the end of a line it wrote without reading its output again, and
   no decision anywhere reads the text through a second lexer pass: one
   token stream, the tree's, is behind every one (the #3085 lesson). The
   walk records the output range of each item.
1. **Certify and demote.** Reparse the output and check, per item: the output
   holds exactly one node in the item's range (same boundaries); the item's
   directives, options, includes and plugins are the same (structural
   equality, plus decimal scale and sign and metadata key order, which
   `PartialEq` does not see: `same_directive`); its comment stream is the
   same (same text in the same slot); every line holding a reported error is
   kept verbatim and no line gains one that the input did not already hold
   (reported or quieted). An item that fails is **demoted** to opaque and the
   file is emitted again.
1. **Fixed point.** The certified output `y` is returned only if certifying
   `y` again gives `y`. Formatting `y` then runs that same certification
   first, gets its own input back, and returns it: `f(f(x)) == f(x)` holds by
   construction, not by the emitter's good behavior. When `y` is not a
   fixed point, the item at the first difference is demoted and `x`
   certified again; when that item is already opaque, `x` is returned.

Demotion only grows the set of opaque items, so the loop terminates. When a
failure cannot be pinned on an item the formatter can still demote (the item
is already opaque, or the failure is in the separator), the file is returned
unchanged. All-opaque is the identity, and the identity keeps every promise
trivially.

### One definition of "the same meaning"

The certifier's checks are a production version of the round-trip oracle, in
`crates/rustledger-parser/src/cst/certify.rs`: `same_directive`, the comment
stream, the error-line rules. The oracle calls the same functions (through
`#[doc(hidden)]` re-exports) to check whole files, so the product and its
tests share one definition (AGENTS.md, Canonical-Function Discipline).
Directives are compared structurally, not through `Debug` text: `PartialEq`
plus a walk of every decimal (`rustledger_core::visit::visit_numbers`,
compared by exact representation) and every metadata block's key order
(`visit_metadata`). Both walks are exhaustive matches, so a new field that
carries a number cannot be skipped silently.

### The certifier hides emitter bugs from users, not from us

A demotion means the canonical emitter produced something wrong. Users get
the safe output; the tests do not accept it:

- The fuzz target and the corpus sweeps (`format_roundtrip_properties`)
  require **zero demotions** (`__format_source_report`), so a fuzz find is
  still an emitter bug to fix.
- `test_format_exhaustive_short_inputs` runs every string of up to four
  symbols over the bytes the frame bugs were made of (a BOM, `"`, `\n`,
  `\r`, `\r\n`, `A`, `;`, `*`, a space, a date) and pins the inputs the
  certifier demotes in `tests/format_roundtrip_common/exhaustive_demotions.manifest`.
  The list may only shrink: a new entry is a new emitter bug, and a fix
  removes its lines. It is empty since phase B. Every input of the sweep
  must keep every promise.

### Prior art

- **Black** (Python) checks, in its default safe mode, that the reformatted
  AST is equivalent to the original and that a second pass is stable. On
  failure it refuses the whole file and reports an internal error.
- **rustfmt** leaves untouched what it cannot format (a macro it cannot
  parse, a line it cannot fit) and formats the rest.
- **gofmt** formats only what parses, and refuses a file that does not.

We certify like Black, but demote per item like rustfmt, and fall back to
Black's whole-file refusal (as the identity, not an error) only when no item
can be blamed. A broken file still formats around its broken lines, as it did
before (#1335, #2794).

### Costs

- **Time.** Certification reparses the output and formats it once more.
  Measured with `crates/rustledger-parser/benches/parser_bench.rs`
  (`format_source_vs_with_parsed`, 1000 transactions; before the certifier,
  phase A, phase B): `format_source` 4.0, 9.9, 8.6 ms;
  `format_source_with_parsed` 1.5, 7.1, 6.5 ms; the same ledger with CRLF
  line endings 17.0 ms in phase A (a second parse of the raw source),
  9.0 ms in phase B. The floor is one parse of the output and one emit of
  it beyond the uncertified cost. An input that
  is already canonical (format-on-save of a formatted file, `format --check`
  on a clean tree) is returned without certification, at the old cost:
  output equal to input reads as the input by being it.
- **Hidden bugs.** A demotion degrades the output silently (the item keeps
  its author's layout). The zero-demotion property of the fuzz target and
  the manifest ratchet keep such bugs visible to developers.
- **The checks can be too strict.** A failure the certifier cannot attribute
  returns the whole file unchanged. That is safe, but unformatted; the
  corpus pins it at zero.

## Phase plan

- **Phase A** (0.25, #3086): wrap the existing formatter in the
  certifier and the demotion loop at the public entry points
  (`format_source`, `format_source_grouped`, `format_source_with_parsed`,
  `format_source_with_parsed_grouped`, `try_format_source*`, the LSP's
  document formatting). The frame exceptions stay; the certifier makes their
  disagreements safe.
- **Phase B** (done): segment the original bytes in one frame (no pre-parse fold),
  with the driver owning separators, the final newline, line endings and the
  BOM, and delete the exceptions (`RepairedLines`, `keep_bom_before_a_second`,
  `keep_cr`, the last-line rules, the string-aware scanners where nothing
  needs them). The LSP's CRLF-preserving mode becomes a driver option applied
  to the bytes the driver writes. Every decision reads the tree's one token
  stream (the #3085 lesson). Also: the fixed-point check replaced the
  phase-A idempotence check (a second emit with the same items forced),
  and opaque items are copied byte for byte (phase A trimmed their
  trailing blanks, folded their CRLFs and added a final newline, which is
  how `2024-01-01 A; ` gained a comment).
- **Phase C**: range formatting on the same driver, with the items outside
  the range forced opaque (deleting the separate range path), and the driver
  and certifier made format-neutral behind a frontend trait (segment, emit,
  meaning), beancount being the first frontend: other grammars (ledger,
  hledger) are planned.

## Consequences

### Positive

- Promises 1-3 hold for every input by construction of the loop, not by the
  absence of a known counterexample: the worst outcome is an item, or the
  file, kept as written.
- The definition of "the same meaning" exists once, in production code.
- Phase B deleted the frame exceptions without risk to users: a mistake
  would have become a demotion the tests report, not corrupted output. The
  exhaustive sweep (every string of up to six symbols, 1.1M inputs) has no
  demotion left.

### Negative, and accepted

- Formatting a file that is not yet canonical costs about twice what it did
  before the certifier (more for the cached-parse entry).
- A demoted item is left unformatted without telling the user. The CLI and
  the LSP do not surface demotions yet.
