# Regression inputs, kept in tree

Each file here once broke an assertion of `fuzz_parse` (the parser's lossless
round-trip, see `fuzz_targets/common/lossless.rs`). They live beside the fix
rather than only in the durable fuzz corpus branch, so losing that branch, or
`cmin` pruning it, cannot resurrect a closed bug (AGENTS.md, "Long-lived
reference branches"). CI seeds this directory into the target's corpus.
`fuzz_green_eq_red` keeps the same files under its own directory.

Replay one:

```sh
cargo fuzz run fuzz_parse regressions/fuzz_parse/<file>
```

| file | what it caught |
|---|---|
| `crlf-hash-comment-2769` | A column-0 `#` comment on a CRLF line ran to the `\n`, so it also claimed the `\r` the `\r?\n` newline token starts at. The two tokens overlapped by a byte and the directive after the comment failed with P0012 (#2769, fixed in #2773). |
| `hash-comment-quote-2775` | A `"` in a column-0 `#` comment opened a multi-line string while the lexer skipped the comment token by token, so the directives after it vanished with no error and `rledger format` deleted them (#2775). |
