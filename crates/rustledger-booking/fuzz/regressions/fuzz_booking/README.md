# Crash inputs, kept in tree

Each file here reproduced a panic once. They live beside the fix rather than in
the durable fuzz corpus branch, so losing that branch cannot resurrect a bug
that was already closed (CLAUDE.md, "Long-lived reference branches").

Replay one:

```sh
cargo fuzz run fuzz_booking regressions/fuzz_booking/<file>
```

| file | what it caught |
|---|---|
| `interpolated-cost-division-overflow-2340` | `total / units_number.abs()` in `interpolate.rs`, solving a cost from a residual: the seventh unchecked division of the class #2327 fixed, and the one its grep could not reach because it lives in a third file. Found minutes into the first run of the widened generator (#2340). |
