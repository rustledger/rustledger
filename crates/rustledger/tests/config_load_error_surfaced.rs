//! Regression for issue #1306.
//!
//! A config file that exists but fails to parse must surface a clear
//! error, not be silently discarded so the user gets a misleading
//! downstream message. The reporter put a *source* definition
//! (`type` / `command`) under `[price.mapping.hy]`, which can't
//! deserialize as a `CommodityMapping`; `rledger price hy` then reported
//! "no price source configured" while `rledger config show` reported the
//! real TOML parse error. `main` now fails fast on a config-load error.

mod common;

use std::process::Command;

#[test]
fn malformed_config_surfaces_parse_error_instead_of_silent_default() {
    let bin = require_rledger!();

    // The exact mistake from #1306: a `[price.mapping.X]` table shaped
    // like a source definition. A valid mapping is a ticker string or a
    // `{ source = "..." }` table, so this can't deserialize.
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join(".rledger.toml"),
        "[price.mapping.hy]\ntype = \"command\"\ncommand = [\"uv\", \"run\", \"pricedl\"]\n",
    )
    .expect("write config");

    let output = Command::new(bin)
        .args(["price", "hy"])
        // Run inside the tempdir so its `.rledger.toml` is the project
        // config, and point HOME/XDG at the (empty) tempdir so no real
        // user/system config is loaded first.
        .current_dir(dir.path())
        .env("HOME", dir.path())
        .env("XDG_CONFIG_HOME", dir.path())
        .output()
        .expect("run rledger price");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "a malformed config must fail, not exit 0 with defaults.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stderr.contains("Failed to parse config file"),
        "stderr should name the config parse failure.\nstderr: {stderr}"
    );
    // The whole bug was that the misleading message masked the real
    // parse error — it must no longer appear.
    assert!(
        !stdout.contains("no price source configured")
            && !stderr.contains("no price source configured"),
        "the real parse error must replace the misleading 'no price source configured' message.\nstdout: {stdout}\nstderr: {stderr}"
    );
}
