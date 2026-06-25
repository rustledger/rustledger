//! CPU-profiling harness for the `load` → `process` pipeline.
//!
//! Samples the CPU (in-process, via `pprof`'s signal-based sampler — no `perf`
//! privileges needed) while running the same pipeline as `rledger check` over a
//! ledger file `iterations` times, and writes `flamegraph.svg` — open it in a
//! browser to see which call paths dominate CPU time. The nightly `profile.yml`
//! workflow runs this over a generated ledger to surface the hot spots to
//! optimize, complementing the `dhat` heap profile (where the bytes go).
//!
//! ```text
//! cargo run -p rustledger --profile profiling --example flamegraph_pipeline \
//!     --features flamegraph -- <ledger.beancount> [iterations]
//! ```
//!
//! Without the `flamegraph` feature the example still builds and runs the
//! pipeline (no profiling), so it stays green in the default `--all-targets`
//! build.

#[cfg(feature = "flamegraph")]
use pprof::ProfilerGuardBuilder;

fn main() {
    let Some(path) = std::env::args_os().nth(1) else {
        eprintln!("usage: flamegraph_pipeline <ledger.beancount> [iterations]");
        std::process::exit(2);
    };
    // Loop the pipeline so the sampler (1 kHz) collects enough samples on even a
    // fast run; default chosen for a ~10k-txn ledger.
    // Read from `args_os` (not `args`) so a non-UTF8 ledger path in argv[1]
    // doesn't panic the whole iterator before we reach the count.
    let iterations: usize = std::env::args_os()
        .nth(2)
        .and_then(|s| s.to_str().and_then(|t| t.parse().ok()))
        .unwrap_or(50);

    // Same pipeline as `rledger check`: the one-shot `load` runs parse +
    // includes + options, then book + plugins + validate.
    let options = rustledger_loader::LoadOptions {
        run_plugins: true,
        validate: true,
        ..Default::default()
    };

    #[cfg(feature = "flamegraph")]
    let guard = match ProfilerGuardBuilder::default()
        .frequency(1000)
        .blocklist(&["libc", "libgcc", "pthread", "vdso"])
        .build()
    {
        Ok(g) => g,
        Err(e) => {
            eprintln!("failed to start CPU profiler: {e}");
            std::process::exit(1);
        }
    };

    let p = std::path::Path::new(&path);
    let mut pipeline_errors = 0usize;
    for _ in 0..iterations {
        match rustledger_loader::load(p, &options) {
            // `load` returns `Ok` even when the pipeline accumulated validation
            // errors (in `ledger.errors`); record the count so a flamegraph over
            // an erroring workload isn't silently reported as clean.
            Ok(ledger) => pipeline_errors = ledger.errors.len(),
            Err(e) => {
                eprintln!("load/process failed: {e}");
                std::process::exit(1);
            }
        }
    }
    if pipeline_errors > 0 {
        eprintln!("note: workload produced {pipeline_errors} pipeline errors");
    }

    #[cfg(feature = "flamegraph")]
    {
        let report = match guard.report().build() {
            Ok(r) => r,
            Err(e) => {
                eprintln!("failed to build profile report: {e}");
                std::process::exit(1);
            }
        };
        let file = match std::fs::File::create("flamegraph.svg") {
            Ok(f) => f,
            Err(e) => {
                eprintln!("failed to create flamegraph.svg: {e}");
                std::process::exit(1);
            }
        };
        if let Err(e) = report.flamegraph(file) {
            eprintln!("failed to write flamegraph: {e}");
            std::process::exit(1);
        }
        eprintln!("wrote flamegraph.svg ({iterations} iterations)");
    }

    #[cfg(not(feature = "flamegraph"))]
    eprintln!("ran {iterations} iterations (build with --features flamegraph to profile)");
}
