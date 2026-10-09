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
| `rebuild-slot-order-prefix-2404` | `rebuild_index`'s "internal positions summed past the Decimal range" `debug_assert!`, reached from `apply`'s rollback. The rebuild re-summed units in SLOT order, and a partial sum overflows on a valid inventory: slots `[MAX - k, MAX, -MAX]`, where a merge put the last add into the first slot. `add` had checked its running total one operation at a time and cached `MAX - k`. In release the assertion is compiled out and `units_cache` was left half rebuilt. The rebuild now totals an overflowing currency exactly (`checked_exact_sum_python_scale`). The nightly found it on 2026-09-20; the bug predates that. |
| `ordered-walk-available-total-overflow-2554` | `available_total += pos.units.number.abs()` in `plan_ordered_in`, a running total kept only for the shortfall message. A STRICT sale of `MAX` against lots of `0.48`, `0.1`, two dust lots and `MAX` reached the ordered walk through the total-match exception, and the sum hit `0.58 + MAX` on the lot that covered the sale. Behind it, the same walk's `remaining -= take` ROUNDED (`MAX - 0.48` is `MAX`), so it drained more units than were sold, and the exception's `Sum` had rounded to a false total match. The walk now keeps its remainder exactly, the shortfall total is summed only when reported, the total match is decided exactly, and a take or lot no `Decimal` holds is a booking overflow. The nightly found it on 2026-10-09. |
