//! TEMPORARY probe for #2605: fails only in the release configuration, to show
//! that a red slim job turns `build` red. Reverted in the next commit.
#[cfg(not(feature = "python-plugin-wasm"))]
#[test]
fn slim_gate_probe() {
    panic!("deliberate slim-only failure (#2605 gate probe)");
}
