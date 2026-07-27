//! The protocol boundary: LSP URIs on one side, filesystem paths on the other.
//!
//! Everything that crosses converts HERE. The alternative is what this module
//! replaced: `document_links` grew its own URI builder, `main_loop` grew eight
//! more plus a `cfg(windows)` special case, and each drifted differently until
//! three separate bugs shipped (#1866, #1868). rust-analyzer confines the same
//! conversion to `from_proto`/`to_proto` for the same reason.
//!
//! If you find yourself writing `format!("file://{}", ...)` or stripping a
//! `file://` prefix, the function you want is already here.

use crate::PathUriError;
use lsp_types::Uri;
use std::path::PathBuf;

/// Convert an LSP URI to a file path.
///
/// Delegates to [`url::Url`], which is the only implementation in this tree
/// that gets the whole job right. `lsp-types` 0.97 swapped `url::Url` for
/// `fluent_uri::Uri`, a generic RFC 3986 parser with no file-path conversion
/// and no feature flag to restore it, so every call site here had been
/// hand-written and each had drifted:
///
/// - The decoder rebuilt UTF-8 one byte at a time (`result.push(byte as char)`),
///   so a ledger under `Facturé/` resolved to `FacturÃ©/` and every feature that
///   takes a path silently looked in a directory that does not exist.
/// - `file://` was stripped literally, leaving `/C:/x` on Windows, where the
///   drive colon also arrives as `%3A` (issue #1866).
///
/// rust-analyzer and taplo both keep a `url::Url`-based URI type deliberately
/// rather than reimplement this; `url` carries its own test suite for the
/// platform behavior our CI cannot exercise.
/// # Errors
/// [`PathUriError`] naming which step failed, so a caller can log something
/// more useful than "nothing happened".
pub fn uri_to_path(uri: &Uri) -> Result<PathBuf, PathUriError> {
    let url = url::Url::parse(uri.as_str()).map_err(|_| PathUriError::NotAUri)?;
    url.to_file_path().map_err(|()| PathUriError::NotALocalFile)
}

/// Convert a file path to an LSP URI.
///
/// The inverse of [`uri_to_path`], and the one place a `file:` URI is built.
/// `format!("file://{}", path.display())` was used at eight call sites and
/// percent-encoded nothing, so any path containing a space, `#`, or a non-ASCII
/// character produced a URI the editor could not open. On Windows it also
/// produced `file://C:/x`, which needs three slashes, and left the platform's
/// backslashes in place.
/// # Errors
/// [`PathUriError::NotAbsolute`] for a relative path, which has no `file:` URI.
pub fn path_to_uri(path: &std::path::Path) -> Result<Uri, PathUriError> {
    let url = url::Url::from_file_path(path).map_err(|()| PathUriError::NotAbsolute)?;
    // `url` encodes to the WHATWG path set, which leaves `[ ] ^ |` literal;
    // `lsp-types` parses with `fluent_uri`, strict RFC 3986, where none of them
    // is a `pchar`. Composing the lax encoder with the strict parser means a
    // perfectly ordinary path like `Statements/[2026-01] bank.pdf` produces a
    // string that will not parse, and the function returns `None` — no document
    // link, no goto-definition, no diagnostics for that file.
    //
    // Everything after `file://` is the path: `from_file_path` leaves the
    // authority empty except for a UNC share, whose host is a name and cannot
    // contain these characters, so escaping them here cannot corrupt a host.
    let mut out = String::with_capacity(url.as_str().len());
    for ch in url.as_str().chars() {
        match ch {
            '[' => out.push_str("%5B"),
            ']' => out.push_str("%5D"),
            '^' => out.push_str("%5E"),
            '|' => out.push_str("%7C"),
            _ => out.push(ch),
        }
    }
    out.parse::<Uri>().map_err(|_| PathUriError::Unencodable)
}

#[cfg(test)]
mod uri_conversion_tests {
    use super::*;
    use std::str::FromStr;

    fn uri(s: &str) -> Uri {
        Uri::from_str(s).expect("valid uri")
    }

    /// A percent-encoded path decodes to the bytes the filesystem actually has.
    ///
    /// The old decoder rebuilt UTF-8 one byte at a time — `%C3%A9` became two
    /// chars rather than one — so a ledger under `Facturé/` resolved to
    /// `FacturÃ©/` and every feature taking a path looked in a directory that
    /// does not exist. `uri_to_path` has a dozen call sites, so this was not
    /// confined to one feature.
    #[test]
    fn a_non_ascii_path_survives_the_round_trip() {
        for (encoded, want) in [
            (
                "file:///home/a/Factur%C3%A9/x.bean",
                "/home/a/Facturé/x.bean",
            ),
            ("file:///home/a/B%C3%BCcher/x.bean", "/home/a/Bücher/x.bean"),
            (
                "file:///home/a/%E4%BC%9A%E8%A8%88/x.bean",
                "/home/a/会計/x.bean",
            ),
            (
                "file:///tmp/re%20pro/main.beancount",
                "/tmp/re pro/main.beancount",
            ),
            ("file:///home/a/%23hash/x.bean", "/home/a/#hash/x.bean"),
        ] {
            assert_eq!(
                uri_to_path(&uri(encoded)).expect(encoded),
                std::path::PathBuf::from(want),
                "{encoded}"
            );
        }
    }

    /// Both directions agree, which is what a URI a handler hands back to the
    /// editor depends on.
    #[test]
    fn path_and_uri_round_trip() {
        for p in [
            "/tmp/plain.bean",
            "/tmp/a b/space.bean",
            "/tmp/Facturé/accented.bean",
            "/tmp/会計/cjk.bean",
            "/tmp/#hash/punct.bean",
            // `url` leaves these literal (WHATWG path set) but `fluent_uri`
            // refuses them (strict RFC 3986), so composing the two dropped a
            // perfectly ordinary statement filename. The corpus originally had
            // none of this class, which is why the gap survived review.
            "/tmp/a[1].bean",
            "/tmp/Statements/[2026-01] bank.pdf",
            "/tmp/a^b.bean",
            "/tmp/a|b.bean",
        ] {
            let path = std::path::Path::new(p);
            let u = path_to_uri(path).unwrap_or_else(|e| panic!("to uri {p}: {e}"));
            assert!(
                !u.as_str().contains(' '),
                "a raw space makes a URI the editor cannot open: {}",
                u.as_str()
            );
            assert_eq!(
                uri_to_path(&u).unwrap_or_else(|e| panic!("back {p}: {e}")),
                path
            );
        }
    }

    /// A relative path has no `file:` URI. Saying so beats inventing one that
    /// resolves against whatever the process's working directory happens to be.
    #[test]
    fn a_relative_path_has_no_uri() {
        assert_eq!(
            path_to_uri(std::path::Path::new("relative/x.bean")),
            Err(PathUriError::NotAbsolute)
        );
    }

    /// The shapes an editor actually sends, and where the answer changed.
    ///
    /// Every difference from the previous hand-rolled decoder is a correction,
    /// which is worth pinning because "stricter parser" is otherwise an
    /// unbounded claim:
    ///
    /// - A URI with a HOST (`file://server/share/x`) used to yield
    ///   `server/share/x`, a RELATIVE path, so any caller testing `exists()`
    ///   resolved it against the process's working directory. It is `None` here
    ///   now, and `url` turns it into a real UNC path on Windows.
    /// - A query or fragment used to be kept as part of the filename.
    #[test]
    fn editor_uri_shapes_resolve_or_are_refused() {
        // A host component is not a local path on this platform.
        #[cfg(not(windows))]
        assert_eq!(
            uri_to_path(&uri("file://server/share/x.bean")),
            Err(PathUriError::NotALocalFile)
        );

        // Query and fragment are URI syntax, not part of the filename.
        for u in ["file:///home/a/x.bean?q=1", "file:///home/a/x.bean#frag"] {
            assert_eq!(
                uri_to_path(&uri(u)).expect(u),
                std::path::PathBuf::from("/home/a/x.bean"),
                "{u}"
            );
        }

        // An unsaved buffer has no path, and did not before either.
        assert_eq!(
            uri_to_path(&uri("untitled:Untitled-1")),
            Err(PathUriError::NotALocalFile)
        );
    }

    /// A non-`file:` URI is not a path, and must not be coerced into one.
    #[test]
    fn a_non_file_uri_is_not_a_path() {
        assert_eq!(
            uri_to_path(&uri("untitled:Untitled-1")),
            Err(PathUriError::NotALocalFile)
        );
        assert_eq!(
            uri_to_path(&uri("https://example.com/x.bean")),
            Err(PathUriError::NotALocalFile)
        );
    }
}

#[cfg(test)]
mod windows_shape_tests {
    use super::*;

    /// A drive-letter path becomes a three-slash URI with the separators an
    /// editor expects.
    ///
    /// `cfg(windows)` because it cannot be faked: `from_file_path` decides what
    /// is absolute using the HOST platform's rules, so on Linux `C:\x` is a
    /// relative path and the function correctly refuses it. The main CI has no
    /// Windows runner (`release-test.yml` does), so this runs for a developer on
    /// Windows and in release testing rather than on every PR. Asserting a
    /// hand-written `C:/x` on Linux instead would test a shape the code never
    /// receives, which is how the backslash bug in #1867 got through.
    #[cfg(windows)]
    #[test]
    fn a_drive_letter_path_becomes_a_three_slash_uri() {
        let uri = path_to_uri(std::path::Path::new(r"C:\Users\a b\repro\neighbor.txt"))
            .expect("a drive-letter path has a URI on Windows");
        assert_eq!(uri.as_str(), "file:///C:/Users/a%20b/repro/neighbor.txt");
        assert_eq!(
            uri_to_path(&uri).expect("round trip"),
            std::path::PathBuf::from(r"C:\Users\a b\repro\neighbor.txt")
        );
    }

    /// The half of the Windows question that IS testable anywhere: the escaping
    /// `url` omits and `lsp-types` requires is applied regardless of platform.
    #[test]
    fn the_strict_parser_gap_is_closed_on_every_platform() {
        // Built by hand rather than through `from_file_path`, so the assertion
        // does not depend on what this platform calls absolute.
        for (raw, want) in [
            ("file:///tmp/a[1].bean", "file:///tmp/a%5B1%5D.bean"),
            ("file:///tmp/a^b.bean", "file:///tmp/a%5Eb.bean"),
            ("file:///tmp/a|b.bean", "file:///tmp/a%7Cb.bean"),
        ] {
            // `url` produces the left-hand form; `lsp-types` refuses it.
            assert!(
                raw.parse::<Uri>().is_err(),
                "{raw} should be rejected by the strict parser"
            );
            assert!(
                want.parse::<Uri>().is_ok(),
                "{want} should be accepted once escaped"
            );
        }
    }
}
