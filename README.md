# fuzz-corpus

libFuzzer corpora, one directory per target, published nightly by
`.github/workflows/fuzz.yml` and replayed by every PR run.

Machine-maintained; do not hand-edit. Crash regressions belong in-tree
under `crates/<crate>/fuzz/regressions/<target>/`, not here.
