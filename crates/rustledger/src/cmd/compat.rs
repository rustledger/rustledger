//! Install/uninstall bean-* compatibility wrapper scripts.
//!
//! Creates lightweight shell scripts (Unix) or .cmd files (Windows) that
//! delegate to `rledger` subcommands, providing a drop-in replacement for
//! Python beancount's `bean-*` commands.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

/// The bean-* commands and their rledger subcommand equivalents.
const COMPAT_COMMANDS: &[(&str, &str)] = &[
    ("bean-check", "check"),
    ("bean-format", "format"),
    ("bean-query", "query"),
    ("bean-report", "report"),
    ("bean-doctor", "doctor"),
    ("bean-extract", "extract"),
    ("bean-price", "price"),
];

/// Resolve the target directory for wrapper scripts.
///
/// Priority:
/// 1. Explicit `--prefix` argument
/// 2. Same directory as the running `rledger` binary
fn resolve_target_dir(prefix: Option<&Path>) -> Result<PathBuf> {
    if let Some(p) = prefix {
        return Ok(p.to_path_buf());
    }

    let exe = std::env::current_exe().context("could not determine rledger binary path")?;
    let dir = exe
        .parent()
        .context("rledger binary has no parent directory")?;
    Ok(dir.to_path_buf())
}

/// Marker line written into every generated wrapper so [`is_rledger_wrapper`]
/// can recognize one precisely, instead of treating any file that merely
/// mentions "rledger" as a wrapper.
const WRAPPER_MARKER: &str = "rledger compat wrapper";

/// POSIX single-quote a string so it survives in the generated `sh` wrapper
/// even when it contains spaces or shell metacharacters.
#[cfg(unix)]
fn sh_single_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''"))
}

/// Generate the content of a wrapper script for the current platform.
///
/// The shim execs `rledger` by **absolute path** (`current_exe`) rather than by
/// bare name, so it works even when the install directory is not on `PATH` —
/// the common `--prefix` case, where a bare `exec rledger` dies with
/// `exec: rledger: not found`. `rledger` is the validated-UTF-8 absolute path.
#[cfg(unix)]
fn wrapper_content(subcommand: &str, rledger: &str) -> String {
    format!(
        "#!/bin/sh\n# {WRAPPER_MARKER}\nexec {} {subcommand} \"$@\"\n",
        sh_single_quote(rledger)
    )
}

#[cfg(windows)]
fn wrapper_content(subcommand: &str, rledger: &str) -> String {
    format!("@rem {WRAPPER_MARKER}\r\n@\"{rledger}\" {subcommand} %*\r\n")
}

/// Get the wrapper file name for a bean-* command on the current platform.
#[cfg(unix)]
fn wrapper_filename(name: &str) -> String {
    name.to_string()
}

#[cfg(windows)]
fn wrapper_filename(name: &str) -> String {
    format!("{name}.cmd")
}

/// Check if an existing file is an rledger-generated wrapper.
///
/// Matches the current [`WRAPPER_MARKER`] line, plus the legacy `exec rledger`
/// / `@rledger` forms emitted before the absolute-path change, so upgrades
/// still overwrite/uninstall old wrappers. This is deliberately tighter than
/// "contains rledger" so unrelated scripts that merely mention rledger are not
/// clobbered. Returns `false` if the file doesn't exist or can't be read.
fn is_rledger_wrapper(path: &Path) -> bool {
    fs::read_to_string(path).is_ok_and(|c| {
        c.contains(WRAPPER_MARKER) || c.contains("exec rledger ") || c.contains("@rledger ")
    })
}

/// Install bean-* compatibility wrapper scripts, logging progress to stdout.
///
/// Thin wrapper over [`install_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `install_with_writer` with a buffer.
pub fn install(prefix: Option<&Path>) -> Result<()> {
    let mut stdout = std::io::stdout().lock();
    install_with_writer(prefix, &mut stdout)
}

/// Install bean-* compatibility wrapper scripts, writing progress lines to
/// `out`. Skip notices for non-rledger files still go to stderr.
pub fn install_with_writer<W: Write>(prefix: Option<&Path>, out: &mut W) -> Result<()> {
    // Resolve the binary once: the shims exec this absolute path (so they work
    // even when the install dir is off PATH), and — absent `--prefix` — it also
    // determines the install directory. Computing `current_exe()` a single time
    // avoids an extra syscall and a potential dir/exe mismatch.
    let rledger_exe = std::env::current_exe()
        .context("could not determine the rledger binary path for the wrapper scripts")?;
    let rledger_str = rledger_exe.to_str().with_context(|| {
        format!(
            "rledger binary path is not valid UTF-8, cannot write wrapper scripts: {}",
            rledger_exe.display()
        )
    })?;
    let dir = match prefix {
        Some(p) => p.to_path_buf(),
        None => rledger_exe
            .parent()
            .context("rledger binary has no parent directory")?
            .to_path_buf(),
    };

    if !dir.exists() {
        bail!(
            "target directory does not exist: {}\n  hint: create it first or use --prefix",
            dir.display()
        );
    }

    let mut installed = 0;
    for (name, subcommand) in COMPAT_COMMANDS {
        let filename = wrapper_filename(name);
        let path = dir.join(&filename);

        if path.exists() && !is_rledger_wrapper(&path) {
            eprintln!(
                "  skip: {} (exists and is not an rledger wrapper)",
                path.display()
            );
            continue;
        }

        let content = wrapper_content(subcommand, rledger_str);
        fs::write(&path, &content)
            .with_context(|| format!("failed to write {}", path.display()))?;

        // Make executable on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
                .with_context(|| format!("failed to set permissions on {}", path.display()))?;
        }

        writeln!(out, "  installed: {}", path.display())?;
        installed += 1;
    }

    if installed > 0 {
        writeln!(
            out,
            "\n{installed} wrapper(s) installed to {}",
            dir.display()
        )?;
        // Check if the directory is on PATH
        if let Ok(path_var) = std::env::var("PATH")
            && !std::env::split_paths(&path_var).any(|p| p == dir)
        {
            writeln!(out, "  note: {} may not be on your PATH", dir.display())?;
        }
    } else {
        writeln!(out, "nothing to install (all wrappers already exist)")?;
    }

    Ok(())
}

/// Uninstall bean-* compatibility wrapper scripts, logging to stdout.
///
/// Thin wrapper over [`uninstall_with_writer`].
pub fn uninstall(prefix: Option<&Path>) -> Result<()> {
    let mut stdout = std::io::stdout().lock();
    uninstall_with_writer(prefix, &mut stdout)
}

/// Uninstall bean-* compatibility wrapper scripts, writing progress lines
/// to `out`. Skip notices for non-rledger files still go to stderr.
pub fn uninstall_with_writer<W: Write>(prefix: Option<&Path>, out: &mut W) -> Result<()> {
    let dir = resolve_target_dir(prefix)?;
    let mut removed = 0;

    for (name, _) in COMPAT_COMMANDS {
        let filename = wrapper_filename(name);
        let path = dir.join(&filename);

        if !path.exists() {
            continue;
        }

        // Only remove if it's one of our wrappers
        if !is_rledger_wrapper(&path) {
            eprintln!("  skip: {} (not an rledger wrapper)", path.display());
            continue;
        }

        fs::remove_file(&path).with_context(|| format!("failed to remove {}", path.display()))?;
        writeln!(out, "  removed: {}", path.display())?;
        removed += 1;
    }

    if removed > 0 {
        writeln!(out, "\n{removed} wrapper(s) removed from {}", dir.display())?;
    } else {
        writeln!(out, "nothing to remove")?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compat_commands_mapping() {
        assert_eq!(COMPAT_COMMANDS.len(), 7);
        assert!(
            COMPAT_COMMANDS
                .iter()
                .all(|(name, _)| name.starts_with("bean-"))
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_wrapper_content_unix() {
        let content = wrapper_content("check", "/opt/tools/rledger");
        assert!(content.starts_with("#!/bin/sh\n"));
        assert!(content.contains(WRAPPER_MARKER));
        // Execs the absolute path, not a bare `rledger` (which would break when
        // the install dir is off PATH).
        assert!(
            content.contains("exec '/opt/tools/rledger' check"),
            "should exec the absolute path: {content:?}"
        );
        assert!(
            !content.contains("exec rledger "),
            "must not exec bare rledger"
        );
        assert!(content.contains("\"$@\""));
    }

    #[cfg(unix)]
    #[test]
    fn test_wrapper_content_unix_quotes_spaces() {
        // A path with spaces must stay a single argument in the shim.
        let content = wrapper_content("query", "/opt/my tools/rledger");
        assert!(
            content.contains("exec '/opt/my tools/rledger' query"),
            "spaces in the path must be single-quoted: {content:?}"
        );
    }

    #[cfg(windows)]
    #[test]
    fn test_wrapper_content_windows() {
        let content = wrapper_content("check", "C:\\tools\\rledger.exe");
        assert!(content.contains(WRAPPER_MARKER));
        // Execs the absolute path (double-quoted) with %*, not a bare @rledger.
        assert!(
            content.contains("@\"C:\\tools\\rledger.exe\" check %*"),
            "should exec the absolute path: {content:?}"
        );
        assert!(!content.contains("@rledger "), "must not exec bare rledger");
    }

    #[test]
    fn test_install_and_uninstall() {
        let dir = tempfile::tempdir().unwrap();
        install(Some(dir.path())).unwrap();

        // Verify all wrappers were created
        for (name, subcommand) in COMPAT_COMMANDS {
            let path = dir.path().join(wrapper_filename(name));
            assert!(path.exists(), "{} should exist", path.display());

            let contents = fs::read_to_string(&path).unwrap();
            assert!(contents.contains("rledger"));
            assert!(contents.contains(subcommand));

            // Check executable on Unix
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = fs::metadata(&path).unwrap().permissions();
                assert_eq!(perms.mode() & 0o111, 0o111, "{name} should be executable");
            }
        }

        // Uninstall
        uninstall(Some(dir.path())).unwrap();

        // Verify all wrappers were removed
        for (name, _) in COMPAT_COMMANDS {
            let path = dir.path().join(wrapper_filename(name));
            assert!(!path.exists(), "{} should not exist", path.display());
        }
    }

    #[test]
    fn test_install_skips_non_rledger_files() {
        let dir = tempfile::tempdir().unwrap();

        // Write a non-rledger bean-check
        let path = dir.path().join(wrapper_filename("bean-check"));
        fs::write(
            &path,
            "#!/bin/sh\npython3 -m beancount.scripts.check \"$@\"\n",
        )
        .unwrap();

        install(Some(dir.path())).unwrap();

        // Should NOT have been overwritten
        let contents = fs::read_to_string(&path).unwrap();
        assert!(
            contents.contains("python3"),
            "should not overwrite non-rledger wrapper"
        );
    }

    #[test]
    fn test_install_skips_non_utf8_files() {
        let dir = tempfile::tempdir().unwrap();

        // Write a binary file that can't be read as UTF-8
        let path = dir.path().join(wrapper_filename("bean-check"));
        fs::write(&path, b"\x80\x81\x82\xff").unwrap();

        install(Some(dir.path())).unwrap();

        // Should NOT have been overwritten
        let contents = fs::read(&path).unwrap();
        assert_eq!(
            contents, b"\x80\x81\x82\xff",
            "should not overwrite non-UTF-8 file"
        );
    }

    #[test]
    fn test_install_overwrites_existing_rledger_wrappers() {
        let dir = tempfile::tempdir().unwrap();

        // Write an old rledger wrapper
        let path = dir.path().join(wrapper_filename("bean-check"));
        // A legacy-format rledger wrapper (bare `exec rledger`, pre absolute
        // path) that `is_rledger_wrapper` still recognizes for upgrades.
        fs::write(&path, "#!/bin/sh\nexec rledger check-old \"$@\"\n").unwrap();

        install(Some(dir.path())).unwrap();

        // Should have been overwritten with the new exec line for `check` and no
        // longer reference the old `check-old` subcommand.
        let contents = fs::read_to_string(&path).unwrap();
        assert!(
            !contents.contains("check-old"),
            "should overwrite: {contents:?}"
        );
        #[cfg(unix)]
        assert!(
            contents.contains("check \"$@\""),
            "unix exec line: {contents:?}"
        );
        #[cfg(windows)]
        assert!(
            contents.contains("check %*"),
            "windows exec line: {contents:?}"
        );
    }

    #[test]
    fn test_uninstall_skips_non_rledger_files() {
        let dir = tempfile::tempdir().unwrap();

        // Write a non-rledger bean-check
        let path = dir.path().join(wrapper_filename("bean-check"));
        fs::write(&path, "#!/bin/sh\npython3 bean-check \"$@\"\n").unwrap();

        uninstall(Some(dir.path())).unwrap();

        // Should NOT have been removed
        assert!(path.exists(), "should not remove non-rledger file");
    }
}
