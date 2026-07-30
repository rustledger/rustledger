# ADR-0008: Presentation is declared by the ledger, resolved per surface

## Status

Accepted

## Context

`rledger format` produces a canonical form. The question this record settles is
what "canonical" ranges over, because two different things were being called by
that name:

- **Canonical value** — what the numbers mean. `1,234.50` and `1234.50` are the
  same amount. The parser guarantees this, and nothing in this decision touches
  it.
- **Canonical text** — the bytes on disk. This is what a formatter actually
  produces and what `format --check` compares.

The original position was gofmt's: there is exactly one canonical text for any
given content, no knobs, because a formatter exists to end the argument.
ADR-adjacent code said so explicitly — `OutputSurface`'s first implementation
carried the comment *"ledger text has one canonical form"* — and stripping
thousands separators followed from it. A file with separators and one without
mean the same thing, so pick the simpler and normalize to it.

Issue #1892 pressed on that. A ledger denominated in a currency where amounts
run to ten digits is materially harder to read unseparated, Beancount's own
`option "render_commas"` exists precisely for this, and Beancount's printer
honors it (`grammar.py` calls `dcontext.set_commas(options["render_commas"])`
during the parse; `printer.py` renders through that same context). rledger
stripped the separators such a ledger had asked for.

The observation that resolved it: **the Beancount grammar admits both
spellings.** A formatter that strips separators is therefore not enforcing a
truth, it is making a style choice while presenting it as a canonical form.
Refusing to let the ledger choose is not more principled than letting it — it
just moves the choice from the ledger's author to us.

## Decision

**Canonical text is a function of `(content, the ledger's own declarations)`.**
Not one universal normal form, but one per ledger.

Four rules follow.

### 1. A surface renders separators iff its consumer has a grammar for them

Not "iff a human reads it". The question is whether the receiving parser can
absorb the variation:

| Consumer | Separators | Why |
|----------|-----------|-----|
| Beancount readers (`format`, `query --format beancount`, the LSP) | as declared | the grammar admits them; every conforming reader accepts them |
| Rendered tables (`report`, `query` text) | as declared | read by a person |
| CSV / JSON | **never** | no grammar — a separator forces quoting and then breaks `Decimal(field)` |

The CSV/JSON suppression is **absolute**: it outranks the ledger-wide option and
any per-commodity declaration. That asymmetry is the whole point of the rule —
those consumers cannot express the preference, so the preference does not reach
them. This lives in exactly one place, `OutputSurface::renders_thousands_separators`.

### 2. The declaration lives in the ledger, never in the invocation

This is what keeps the decision from being "we added a formatting flag", which
is the thing gofmt exists to prevent.

`option "render_commas"` and per-commodity `render_commas:` are data in the
ledger. `rledger format --ledger <root>` names *where those declarations live*;
it cannot choose a style. So within any one ledger there is still exactly one
canonical text, `--check` still means something, and every tool that reads that
ledger agrees on it.

### 3. Only presentation that cannot change meaning is the ledger's to choose

Grouping qualifies: inserting or removing separators cannot change a value, and
the parser strips them before anything sees a number.

Precision does not. `DisplayContext` knows a commodity's tracked precision and
`report`/`query` render through it, but **`format` deliberately does not
re-quantize** — a `1234567.5` in a file whose commodity declares `precision: 2`
is written back as `1,234,567.5`, not `1,234,567.50`. Beancount infers a
transaction's balance tolerance from the decimal places actually written, so
padding would change whether the ledger balances. A formatter may exercise the
freedom the grammar allows; it may not use that freedom to alter meaning.

This is the boundary of the ADR, and it is narrower than "presentation is the
ledger's business".

### 4. A ledger-relative canonical form obliges tools to find the ledger

If canonical text depends on the ledger, a tool that cannot see the ledger
cannot produce it. Both the language server and `rledger format` therefore
locate the root journal themselves (shared name list and walk in
`rustledger_loader::discover`), so a file formats identically on save and in a
pre-commit hook.

Discovery is a **guess**, so it is verified: a discovered ledger governs a file
only if that ledger actually includes it. An explicitly named `--ledger` skips
the check, because a guess must be confirmed while an instruction is followed.

## Consequences

### Positive

- A ledger that asks for separators gets them everywhere it is safe to give
  them, matching Beancount.
- One rule, stated once, covers every output surface. Before this, the surfaces
  had already drifted: `query --format beancount` emitted separators while
  `format` stripped them, and CSV emitted them while JSON did not.
- `format --check` and idempotence survive, because the style is fixed by the
  ledger rather than by the caller.
- Editor and CLI agree by construction, since they share the discovery rule.

### Negative, and accepted

- **A file has no canonical form in isolation.** Taken out of its ledger, the
  same bytes canonicalize differently. This is inherent to the decision, not an
  implementation gap. `--no-ledger` is the escape hatch for pipelines that need
  output to depend only on the file's own content.
- **Discovery reads the filesystem**, so `format`'s output depends on something
  other than its input. Bounded three ways: only ledgers that *declare*
  `render_commas` are affected at all (one that declares nothing is
  byte-identical to before), a discovered ledger must actually include the file,
  and `--no-ledger` opts out entirely.
- **A naked number has no commodity**, so a `Value::Number` column in a query
  (`SUM(number)`) can only take the ledger-wide default, never a per-commodity
  declaration. Unavoidable: there is nothing to resolve against.
- **Groups are three digits**, which is all the lexer accepts
  (`\d{1,3}(,\d{3})*`). Other conventions, such as Indian lakh grouping, would
  need a grammar change first — the formatter must never emit text its own
  parser rejects.

## Prior art

- **gofmt / black** — one canonical form, no configuration. The position this
  ADR departs from, and the reason rule 2 exists.
- **rustfmt (`rustfmt.toml`), clang-format (`.clang-format`), EditorConfig
  (`.editorconfig`)** — style declared in-tree and discovered by walking up from
  the file. The closest analogue: the project, not the invocation, owns the
  style, and every tool that touches the project finds the same answer. Rule 4
  is the same mechanism.
- **Beancount** — `grammar.py` sets the display context's `commas` flag from
  `options["render_commas"]` while parsing; `printer.py` renders through that
  context. Beancount already treats presentation as ledger-declared data.
