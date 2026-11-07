//! Heap-profiling harness for the `load` → `process` pipeline.
//!
//! Runs the same path as `rledger check` (parse + includes + options, then
//! book + plugins + validate) over a ledger file, under dhat's heap-profiling
//! global allocator, and writes `dhat-heap.json` to the current directory on
//! exit — view it at <https://nnethercote.github.io/dh_view/>. The nightly
//! `profile.yml` workflow runs this over a generated ledger to surface
//! allocation hotspots ("where do the bytes come from") to optimize.
//!
//! ```text
//! cargo run -p rustledger --profile profiling --example profile_pipeline \
//!     --features dhat-heap -- <ledger.beancount>
//! ```
//!
//! Without the `dhat-heap` feature the example still builds and runs the
//! pipeline (no profiling), so it stays green in the default `--all-targets`
//! build.
//!
//! The loaded ledger is kept alive until the profiler has written its report,
//! so the report's end-of-run figures (`t-end`) are the retained journal, not
//! an empty heap. The same numbers are printed to stderr as a `retained:` line
//! from a snapshot taken while the ledger is alive, next to the run's peak and
//! total allocation. (Previously the ledger was dropped first, so `t-end`
//! measured nothing.)
//!
//! Set `PROFILE_DROP_SOURCE_TEXT=1` to load with `retain_source_text: false`
//! (#2752) and measure the journal without the source text.

// dhat installs a global allocator that wraps the system allocator to record
// every allocation. Gated behind the feature so the default build is untouched.
#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    // Profiles the whole run; on drop it writes `dhat-heap.json` (dropped
    // explicitly below, while the ledger is still alive).
    #[cfg(feature = "dhat-heap")]
    let profiler = dhat::Profiler::new_heap();

    let Some(path) = std::env::args_os().nth(1) else {
        eprintln!("usage: profile_pipeline <ledger.beancount>");
        std::process::exit(2);
    };

    // Mirror `rledger check`: the one-shot `load` runs parse + includes +
    // options, then book + plugins + validate, so the profile covers the full
    // pipeline rather than just parsing.
    let options = rustledger_loader::LoadOptions {
        run_plugins: true,
        validate: true,
        retain_source_text: std::env::var_os("PROFILE_DROP_SOURCE_TEXT").is_none(),
        ..Default::default()
    };
    let ledger = match rustledger_loader::load(std::path::Path::new(&path), &options) {
        Ok(ledger) => ledger,
        Err(e) => {
            eprintln!("load/process failed: {e}");
            std::process::exit(1);
        }
    };
    // `load` returns `Ok` even when the pipeline accumulated validation
    // errors (in `ledger.errors`, like `rledger check`). Surface the count so
    // a profile over an erroring ledger isn't silently "clean".
    eprintln!(
        "processed {} directives ({} pipeline errors)",
        ledger.directives.len(),
        ledger.errors.len()
    );

    // Snapshot the heap while the ledger is alive: `curr` is what the loaded
    // journal holds, `max` the run's peak, `total` everything allocated.
    #[cfg(feature = "dhat-heap")]
    {
        let s = dhat::HeapStats::get();
        eprintln!(
            "retained: {} bytes in {} blocks; peak: {} bytes in {} blocks; \
             total: {} bytes in {} blocks",
            s.curr_bytes, s.curr_blocks, s.max_bytes, s.max_blocks, s.total_bytes, s.total_blocks
        );
        // Write the report now, with the ledger still alive, so its `t-end`
        // is the retained journal too.
        drop(profiler);
    }
    drop(ledger);
}
