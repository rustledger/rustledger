//! Download manager for CPython-WASI runtime.
//!
//! Downloads and caches the Python WASI runtime on first use.

use super::PythonError;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::{self, Cursor, Read};
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

/// Check if the Python runtime is already downloaded.
#[allow(dead_code)]
pub fn is_downloaded() -> bool {
    python_wasm_path().map(|p| p.exists()).unwrap_or(false)
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

    // Download the zip file
    let response = ureq::get(DOWNLOAD_URL)
        .call()
        .map_err(|e| PythonError::Download(format!("HTTP request failed: {e}")))?;

    let mut data = Vec::new();
    response
        .into_reader()
        .read_to_end(&mut data)
        .map_err(|e| PythonError::Download(format!("failed to read response: {e}")))?;

    // Verify checksum
    let actual_hash = hex::encode(Sha256::digest(&data));
    if actual_hash != EXPECTED_SHA256 {
        return Err(PythonError::ChecksumMismatch {
            expected: EXPECTED_SHA256.to_string(),
            actual: actual_hash,
        });
    }

    eprintln!("  ✓ Checksum verified");

    // Extract the zip file
    let cursor = Cursor::new(data);
    let mut archive = zip::ZipArchive::new(cursor)
        .map_err(|e| PythonError::Download(format!("failed to open zip: {e}")))?;

    for i in 0..archive.len() {
        let mut file = archive
            .by_index(i)
            .map_err(|e| PythonError::Download(format!("failed to read zip entry: {e}")))?;

        let outpath = match file.enclosed_name() {
            Some(path) => cache.join(path),
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

    eprintln!("  ✓ Extracted to {}", cache.display());

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
    fn test_hex_encode() {
        assert_eq!(hex::encode([0xde, 0xad, 0xbe, 0xef]), "deadbeef");
    }
}
