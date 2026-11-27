# Regression inputs, kept in tree

Each file here once broke a property of `fuzz_format_roundtrip` (the
formatter round-trip oracle, see `fuzz_targets/common/format_roundtrip.rs`).
They live beside the fix rather than only in the durable fuzz corpus branch,
so losing that branch, or `cmin` pruning it, cannot resurrect a closed bug
(AGENTS.md, "Long-lived reference branches"). CI seeds this directory into the
target's corpus, and `tests/format_roundtrip_properties.rs` replays every file
under `fuzz/regressions/`.

Replay one:

```sh
cargo fuzz run fuzz_format_roundtrip regressions/fuzz_format_roundtrip/<file>
```

| file | what it caught |
|---|---|
| `leading-indented-comment` | `\t;\n\t+`: a file-leading indented comment was moved to column 0. rledger keeps bison's recovery after such a comment quiet, so the indented line after it is clean, and after a column-0 comment it is an error: formatting broke a clean file. |
