//! Download manager for CPython-WASI runtime.
//!
//! Downloads and caches the Python WASI runtime on first use.

use super::PythonError;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::{self, BufReader, Read};
use std::path::PathBuf;

/// `CPython` WASI build version.
const PYTHON_VERSION: &str = "3.14.2";

/// Download URL for the `CPython` WASI build.
const DOWNLOAD_URL: &str = "https://github.com/brettcannon/cpython-wasi-build/releases/download/v3.14.2/python-3.14.2-wasi_sdk-24.zip";

/// Expected SHA256 checksum of the download.
const EXPECTED_SHA256: &str = "af31d6d63f8833fbaba7cd8013893fc06fdf9af3f6abfb14223d061858ac4a4f";

/// Size of the download in bytes (approximate, for progress display).
const DOWNLOAD_SIZE_MB: f64 = 14.0;

/// Get the cache directory for the Python WASI runtime.
fn cache_dir() -> Result<PathBuf, PythonError> {
    let base = dirs::cache_dir()
        .ok_or_else(|| PythonError::Download("could not determine cache directory".to_string()))?;
    Ok(base.join("rustledger").join("python-wasi"))
}

/// Get the path to the python.wasm file.
pub fn python_wasm_path() -> Result<PathBuf, PythonError> {
    let dir = cache_dir()?;
    Ok(dir.join("python.wasm"))
}

/// Get the path to the Python standard library.
pub fn python_stdlib_path() -> Result<PathBuf, PythonError> {
    let dir = cache_dir()?;
    Ok(dir.join("lib"))
}

/// Ensure the Python WASI runtime is downloaded and cached.
///
/// Returns the path to the python.wasm file.
pub fn ensure_runtime() -> Result<PathBuf, PythonError> {
    let wasm_path = python_wasm_path()?;

    if wasm_path.exists() {
        return Ok(wasm_path);
    }

    eprintln!("⚠️  Python plugin runtime not found.");
    eprintln!("⚠️  Downloading CPython {PYTHON_VERSION} for WASI (~{DOWNLOAD_SIZE_MB:.0}MB)...");
    eprintln!("⚠️  This is a one-time download.");
    eprintln!();

    download_and_extract()?;

    if !wasm_path.exists() {
        return Err(PythonError::Download(
            "python.wasm not found after extraction".to_string(),
        ));
    }

    eprintln!("✓ Python WASI runtime installed.");
    eprintln!();

    Ok(wasm_path)
}

/// Download and extract the Python WASI runtime.
fn download_and_extract() -> Result<(), PythonError> {
    let cache = cache_dir()?;
    fs::create_dir_all(&cache)?;

    // Download the zip file to a temp file to avoid memory exhaustion.
    // Per-process names: two first runs at once (parallel tests, two
    // rledger processes) used to share one temp file and one extraction
    // target, so one could read the other's half-written zip, or see
    // `python.wasm` while it was still being written (#2500 review).
    let zip_path = cache.join(format!("download.zip.tmp.{}", std::process::id()));
    let mut response = ureq::get(DOWNLOAD_URL)
        .call()
        .map_err(|e| PythonError::Download(format!("HTTP request failed: {e}")))?;

    // Stream directly to file
    {
        let mut zip_file = File::create(&zip_path)
            .map_err(|e| PythonError::Download(format!("failed to create temp file: {e}")))?;
        let mut reader = response.body_mut().as_reader();
        io::copy(&mut reader, &mut zip_file)
            .map_err(|e| PythonError::Download(format!("failed to download: {e}")))?;
    }

    // Verify checksum from file
    let actual_hash = {
        let file = File::open(&zip_path)
            .map_err(|e| PythonError::Download(format!("failed to open temp file: {e}")))?;
        let mut reader = BufReader::new(file);
        let mut hasher = Sha256::new();
        let mut buffer = [0u8; 8192];
        loop {
            let bytes_read = reader
                .read(&mut buffer)
                .map_err(|e| PythonError::Download(format!("failed to read temp file: {e}")))?;
            if bytes_read == 0 {
                break;
            }
            hasher.update(&buffer[..bytes_read]);
        }
        hex::encode(hasher.finalize())
    };

    if actual_hash != EXPECTED_SHA256 {
        let _ = fs::remove_file(&zip_path); // Clean up on failure
        return Err(PythonError::ChecksumMismatch {
            expected: EXPECTED_SHA256.to_string(),
            actual: actual_hash,
        });
    }

    eprintln!("  ✓ Checksum verified");

    // Extract the zip file
    let zip_file = File::open(&zip_path)
        .map_err(|e| PythonError::Download(format!("failed to open zip: {e}")))?;
    let mut archive = zip::ZipArchive::new(zip_file)
        .map_err(|e| PythonError::Download(format!("failed to open zip: {e}")))?;

    let staging = cache.join(format!("extract.tmp.{}", std::process::id()));
    let _ = fs::remove_dir_all(&staging);
    fs::create_dir_all(&staging)?;

    for i in 0..archive.len() {
        let mut file = archive
            .by_index(i)
            .map_err(|e| PythonError::Download(format!("failed to read zip entry: {e}")))?;

        let outpath = match file.enclosed_name() {
            Some(path) => staging.join(path),
            None => continue,
        };

        if file.is_dir() {
            fs::create_dir_all(&outpath)?;
        } else {
            if let Some(parent) = outpath.parent() {
                fs::create_dir_all(parent)?;
            }
            let mut outfile = File::create(&outpath)?;
            io::copy(&mut file, &mut outfile)?;
        }
    }

    // Clean up temp file
    let _ = fs::remove_file(&zip_path);

    let installed = install_staged(&staging, &cache);
    let _ = fs::remove_dir_all(&staging);
    installed?;

    eprintln!("  ✓ Extracted to {}", cache.display());
    Ok(())
}

/// Move a complete extraction from `staging` into `cache`.
///
/// `python.wasm` is what [`ensure_runtime`] checks for, so it goes in
/// last, by an atomic rename: whoever sees it sees a complete `lib` too.
/// When it is already there, another process finished first and this
/// extraction is dropped. A `lib` with no `python.wasm` beside it is left
/// over from an interrupted install, and is replaced.
fn install_staged(staging: &std::path::Path, cache: &std::path::Path) -> Result<(), PythonError> {
    let wasm = cache.join("python.wasm");
    if wasm.exists() {
        return Ok(());
    }
    let lib = cache.join("lib");
    if lib.exists() {
        let stale = cache.join(format!("lib.stale.{}", std::process::id()));
        fs::rename(&lib, &stale)?;
        let _ = fs::remove_dir_all(&stale);
    }
    match fs::rename(staging.join("lib"), &lib) {
        Ok(()) => {}
        // Another process installed its `lib` in the meantime.
        Err(_) if lib.exists() => {}
        Err(e) => return Err(e.into()),
    }
    fs::rename(staging.join("python.wasm"), &wasm)?;
    Ok(())
}

/// Encode bytes as hex string.
mod hex {
    use std::fmt::Write;

    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes.as_ref().iter().fold(String::new(), |mut acc, b| {
            let _ = write!(acc, "{b:02x}");
            acc
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_dir() {
        let dir = cache_dir().unwrap();
        assert!(dir.to_string_lossy().contains("rustledger"));
        assert!(dir.to_string_lossy().contains("python-wasi"));
    }

    #[test]
    fn test_python_wasm_path() {
        let path = python_wasm_path().unwrap();
        assert!(path.to_string_lossy().ends_with("python.wasm"));
    }

    #[test]
    fn test_python_stdlib_path() {
        let path = python_stdlib_path().unwrap();
        assert!(path.to_string_lossy().ends_with("lib"));
    }

    /// The runtime appears all at once: `python.wasm` (the "installed"
    /// marker) only after `lib`, a leftover partial `lib` is replaced, and
    /// a finished install is never overwritten (#2500 review).
    #[test]
    fn install_staged_is_all_or_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let cache = dir.path().join("cache");
        let staging = dir.path().join("staging");
        let stage = |tag: &str| {
            fs::create_dir_all(staging.join("lib")).unwrap();
            fs::write(staging.join("lib/os.py"), tag).unwrap();
            fs::write(staging.join("python.wasm"), tag).unwrap();
        };
        fs::create_dir_all(cache.join("lib")).unwrap();
        fs::write(cache.join("lib/partial.py"), "half").unwrap();

        stage("first");
        install_staged(&staging, &cache).unwrap();
        assert_eq!(
            fs::read_to_string(cache.join("python.wasm")).unwrap(),
            "first"
        );
        assert_eq!(
            fs::read_to_string(cache.join("lib/os.py")).unwrap(),
            "first"
        );
        assert!(!cache.join("lib/partial.py").exists(), "stale lib replaced");

        fs::remove_dir_all(&staging).unwrap();
        stage("second");
        install_staged(&staging, &cache).unwrap();
        assert_eq!(
            fs::read_to_string(cache.join("python.wasm")).unwrap(),
            "first"
        );
        assert_eq!(
            fs::read_to_string(cache.join("lib/os.py")).unwrap(),
            "first"
        );
    }

    #[test]
    fn test_hex_encode() {
        assert_eq!(hex::encode([0xde, 0xad, 0xbe, 0xef]), "deadbeef");
    }

    #[test]
    fn test_hex_encode_empty() {
        assert_eq!(hex::encode([]), "");
    }

    #[test]
    fn test_hex_encode_single_byte() {
        assert_eq!(hex::encode([0x00]), "00");
        assert_eq!(hex::encode([0xff]), "ff");
        assert_eq!(hex::encode([0x0a]), "0a");
    }

    #[test]
    fn test_constants() {
        // Verify constants are sensible
        assert!(PYTHON_VERSION.starts_with("3."));
        assert!(DOWNLOAD_URL.contains("cpython-wasi"));
        assert_eq!(EXPECTED_SHA256.len(), 64); // SHA256 hex = 64 chars
        // DOWNLOAD_SIZE_MB is a compile-time constant; clippy catches assertions on constants
    }
}
