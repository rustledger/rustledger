//! Generate implementation traces of [`Inventory`] for TLA+ trace validation.
//!
//! The behavior-replay suite checks the model→implementation direction
//! (every model behavior is implemented correctly). This generator serves the
//! DUAL direction: drive the real `Inventory` through random Add/Reduce
//! sequences, record the abstract state after every operation, and let TLC
//! verify that each recorded transition satisfies `Conservation.tla`'s `Next`
//! relation (`scripts/tla-trace-validate.py` builds the trace modules and
//! runs TLC). An implementation transition the model forbids fails the
//! action property.
//!
//! Deterministic by construction (seeded LCG, no clocks), so CI failures
//! reproduce exactly from the printed seed.
//!
//! Usage:
//!   `cargo run -p rustledger-core --example conservation_trace_gen -- \
//!       --count 32 --max-units 3 --max-ops 8 --seed 1 [--corrupt]`
//!
//! Output (stdout): one line per trace — a JSON array of
//! `[inventory, totalAdded, totalReduced, opCount]` states, starting at the
//! initial all-zero state. `--corrupt` flips one unit in the final state of
//! each trace (used by the validator's self-test to prove TLC catches
//! violations).

use rust_decimal::Decimal;
use rustledger_core::{Amount, BookingMethod, Cost, Inventory, Position};

/// Minimal deterministic PRNG (LCG, Numerical Recipes constants) — avoids a
/// rand dependency and any ambient nondeterminism.
struct Lcg(u64);

impl Lcg {
    const fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % bound
    }
}

fn main() {
    let mut count = 32u64;
    let mut max_units = 3u64;
    let mut max_ops = 8u64;
    let mut seed = 1u64;
    let mut corrupt = false;

    let args: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--count" => {
                count = args[i + 1].parse().expect("--count takes a number");
                i += 2;
            }
            "--max-units" => {
                max_units = args[i + 1].parse().expect("--max-units takes a number");
                i += 2;
            }
            "--max-ops" => {
                max_ops = args[i + 1].parse().expect("--max-ops takes a number");
                i += 2;
            }
            "--seed" => {
                seed = args[i + 1].parse().expect("--seed takes a number");
                i += 2;
            }
            "--corrupt" => {
                corrupt = true;
                i += 1;
            }
            other => panic!("unknown argument {other:?}"),
        }
    }
    eprintln!(
        "conservation_trace_gen: count={count} max_units={max_units} \
         max_ops={max_ops} seed={seed} corrupt={corrupt}"
    );

    let cost = Cost::new(Decimal::ONE, "USD")
        .with_date(rustledger_core::naive_date(2024, 1, 1).expect("valid date"));

    for t in 0..count {
        let mut rng = Lcg(seed.wrapping_add(t).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut inv = Inventory::new();
        let mut total_added: i64 = 0;
        let mut total_reduced: i64 = 0;
        let mut op_count: i64 = 0;
        let mut states: Vec<[i64; 4]> = vec![[0, 0, 0, 0]];

        while op_count < max_ops as i64 {
            let amount = i64::try_from(rng.next(max_units) + 1).expect("small");
            if rng.next(2) == 0 {
                // Add — always enabled in the model.
                inv.add(Position::with_cost(
                    Amount::new(Decimal::from(amount), "AAPL"),
                    cost.clone(),
                ))
                .expect("fixture fits in Decimal");
                total_added += amount;
            } else {
                // Reduce — the model guard is `units <= inventory`; a failed
                // implementation reduce corresponds to a disabled action and
                // must be a stutter, so it is not recorded.
                match inv.reduce(
                    &Amount::new(Decimal::from(-amount), "AAPL"),
                    None,
                    BookingMethod::Fifo,
                ) {
                    Ok(_) => total_reduced += amount,
                    Err(_) => continue,
                }
            }
            op_count += 1;
            let inventory: i64 = inv
                .units("AAPL")
                .try_into()
                .expect("integer-valued inventory");
            states.push([inventory, total_added, total_reduced, op_count]);
        }

        if corrupt {
            // Break conservation in the final state so the validator can
            // prove TLC detects an illegal implementation transition.
            let last = states.len() - 1;
            states[last][0] += 1;
        }

        let rendered: Vec<String> = states
            .iter()
            .map(|s| format!("[{},{},{},{}]", s[0], s[1], s[2], s[3]))
            .collect();
        println!("[{}]", rendered.join(","));
    }
}
