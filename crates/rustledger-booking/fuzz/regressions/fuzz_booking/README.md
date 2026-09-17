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
| `booked-cost-underflow-2344` | `BookedCost::new`'s `per_unit * \|units\| == total` invariant, reached from `interpolate.rs`: `2.55 / 7.9e28` UNDERFLOWS to `0`, so the checked division added for the row above returns `Some(0)` and reports nothing. Checked arithmetic guards the top of `Decimal`'s range only; the four engine sites now construct through `try_new`, which guards both ends. |
| `headroom-net-hides-ceiling-lot-2345` | `apply`'s "the guard is unsound" assertion — a plain `assert!`, so a release abort. `add_headroom_for` bounded the per-currency NET and the cost-less merge slot, but #2118 had made cost-bearing lots merge too, so two opposite lots netted to zero while the lot the next add joined sat at `Decimal::MAX`. Found only after the generator's wide-mantissa arm was fixed: it fed a raw `i128` to `try_from_i128_with_scale`, representable about 1 time in 2^31, so it had been yielding `ZERO` on every draw. |
