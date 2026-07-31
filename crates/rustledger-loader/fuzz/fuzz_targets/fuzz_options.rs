//! `Options::set` over arbitrary key/value pairs.
//!
//! The loader carries the highest fix density in the workspace (9.6 fixes per
//! kloc over six months, versus 2.9 for core) and, before this, the least
//! verification: mutation testing only, no fuzzing at all (#1902). Option
//! parsing is the obvious first target — it is a pure string function taking
//! two attacker-influenced inputs, and every value goes through hand-written
//! parsing that has needed repeated correction.
//!
//! Beyond "does not panic", this pins two properties that a wrong parse would
//! break silently:
//!
//! - **Determinism.** The same key/value applied to two fresh `Options` must
//!   produce the same warnings. A parser that depends on ambient state is
//!   wrong in a way tests rarely catch.
//! - **Warnings are never retracted.** Re-applying an option may add more
//!   diagnosis (it does; see the note by that assertion), but a parser that
//!   DROPPED a warning on re-application would be hiding a problem it had
//!   already found.
#![no_main]

use libfuzzer_sys::fuzz_target;
use rustledger_loader::Options;

fuzz_target!(|data: (String, String)| {
    let (key, value) = data;

    let mut a = Options::new();
    a.set(&key, &value);

    let mut b = Options::new();
    b.set(&key, &value);

    // Determinism: identical input, identical diagnosis.
    // Compare the WHOLE warning, not just code and message: `OptionWarning`
    // derives `PartialEq` and also carries `option` and `value`, so this
    // catches a divergence that leaves the text identical.
    assert_eq!(
        a.warnings, b.warnings,
        "Options::set is non-deterministic for key={key:?} value={value:?}"
    );

    // NOT asserted: that re-applying an option produces the same diagnosis.
    // The first version of this target did, and the fuzzer refuted it in 45
    // seconds with `key="plugin"` — 1 warning first, 2 the second time.
    //
    // That is correct behavior, not a bug. `Options` deliberately tracks
    // `set_options` so it can flag a non-repeatable option being set twice
    // (`options.rs`), and `plugin` is ALSO deprecated, so the second
    // application legitimately earns both warnings. `set_options` is
    // load-bearing elsewhere too — `resolve_effective_booking_method` gates on
    // it — so this statefulness is the design, not an accident.
    //
    // Left here as a warning to anyone tempted to "restore" idempotence: the
    // property is false by design, and asserting it only produces noise.
    //
    // What IS true is that repetition never panics and never RETRACTS a
    // diagnosis. A parser that dropped a warning on re-application would be
    // hiding a problem it had already found.
    let before = b.warnings.len();
    b.set(&key, &value);
    assert!(
        b.warnings.len() >= before,
        "re-applying key={key:?} retracted a warning ({} -> {})",
        before,
        b.warnings.len()
    );
});
