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

/// Generate the content of a wrapper script for the current platform.
#[cfg(unix)]
fn wrapper_content(subcommand: &str) -> String {
    format!("#!/bin/sh\nexec rledger {subcommand} \"$@\"\n")
}

#[cfg(windows)]
fn wrapper_content(subcommand: &str) -> String {
    format!("@rledger {subcommand} %*\r\n")
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
/// Returns `true` if the file can be read as UTF-8 and contains "rledger".
/// Returns `false` if the file doesn't exist, can't be read, or isn't a wrapper.
fn is_rledger_wrapper(path: &Path) -> bool {
    fs::read_to_string(path).is_ok_and(|contents| contents.contains("rledger"))
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
    let dir = resolve_target_dir(prefix)?;

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

        let content = wrapper_content(subcommand);
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
        let content = wrapper_content("check");
        assert!(content.starts_with("#!/bin/sh\n"));
        assert!(content.contains("rledger check"));
        assert!(content.contains("\"$@\""));
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
        fs::write(&path, "#!/bin/sh\nrledger check-old \"$@\"\n").unwrap();

        install(Some(dir.path())).unwrap();

        // Should have been overwritten
        let contents = fs::read_to_string(&path).unwrap();
        assert!(
            contents.contains("rledger check"),
            "should overwrite old rledger wrapper"
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
