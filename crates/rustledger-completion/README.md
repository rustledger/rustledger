# rustledger-completion

Editor-agnostic completion logic for Beancount sources.

This crate is the single source of truth for the completion logic shared
between the rustledger LSP server (`rustledger-lsp`) and the WASM editor
(`rustledger-wasm`). It is deliberately pure: no clock access, no
`lsp-types`, no `wasm-bindgen`. Callers supply the live data (account /
currency / payee / tag / link string lists and "today's" date) and map the
neutral `CompletionCandidate` results into their own editor-specific item
types.

It provides:

- `offset_to_byte` — map a position (UTF-8, UTF-16, or character offset)
  to a char-boundary-safe byte offset.
- `classify_context` — classify the text before the cursor into a
  `CompletionContext`.
- `*_candidates` functions — produce neutral `CompletionCandidate` lists
  for each context.
