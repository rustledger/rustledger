# rustledger profiling trends

📊 **Live dashboard: <https://rustledger.github.io/rustledger/>** — instruction + heap trends over time, rendered from `history.jsonl`.

**CI-managed data branch** (like `benchmarks` / `compatibility`). **Do not hand-edit** —
the nightly `profile.yml` workflow appends a data point each night. (`index.html` is the
dashboard; it reads `history.jsonl` live, so new nightly points appear automatically.)

## Contents

- `history.jsonl` — one JSON object per nightly run, with **deterministic** metrics for
  the `load → process` pipeline over a fixed N-transaction workload:
  - `instructions` — total instructions executed (cachegrind `I refs`), machine-independent.
  - `heap_total_bytes` / `heap_peak_bytes` / `heap_blocks` — dhat heap totals.
- `latest/` — the newest `flamegraph.svg` (CPU, where the time goes) and
  `dhat-heap.json` (heap allocation tree; open at <https://nnethercote.github.io/dh_view/>).

## Why

Wall-clock benchmarks (the `benchmarks` branch) catch timing regressions but are noisy.
These metrics are **deterministic** — diff `instructions` / `heap_total_bytes`
night-over-night to spot real regressions or wins, then drill in with the artifacts.

Seeded from a local run on commit `200c6f4`.
