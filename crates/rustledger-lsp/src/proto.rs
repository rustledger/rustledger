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

use crate::{AbsPathBuf, PathUriError};
use lsp_types::Uri;

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
pub fn uri_to_path(uri: &Uri) -> Result<AbsPathBuf, PathUriError> {
    let url = url::Url::parse(uri.as_str()).map_err(|_| PathUriError::NotAUri)?;

    // `Url::to_file_path` is SCHEME-BLIND — it inspects the host and nothing
    // else — so `fugitive:///home/rob/main.beancount`, VS Code's
    // `git:/home/rob/main.beancount?{...}`, `vscode-notebook-cell:/...` and even
    // `https://localhost/etc/passwd` all hand back a real filesystem path. The
    // `strip_prefix("file://")` this module replaced rejected every one of them
    // for free, so without this check the boundary is a REGRESSION on the case
    // it was built to get right.
    //
    // These arrive in practice, not in theory: vim-fugitive gives a git-history
    // buffer the `beancount` filetype, so a client attached by filetype sends
    // `didOpen` for a `fugitive://` URI whose path is the live file's. That
    // text would land in the VFS under the real path, serving every later
    // completion and diagnostic from a stale revision, and its `didClose` would
    // evict the real file outright.
    if url.scheme() != "file" {
        return Err(PathUriError::NotALocalFile);
    }

    // A segment that percent-DECODES into path syntax is a URI claiming one
    // structure and denoting another. RFC 3986 removes dot segments BEFORE
    // decoding, so `%2E%2E` is a segment literally NAMED `..` and `%2F` is a
    // separator inside a single name — neither can exist on a real filesystem.
    // `to_file_path` decodes first and lets the result act as syntax, so
    // `file:///home/u/%2E%2E/secret` yields `/home/secret`, and
    // `file:///a/b%2Fc/d` yields four components from three segments.
    //
    // Worth rejecting regardless of whether a trusted client would send it: the
    // result goes straight to `vfs.open` and `Path::exists` with no
    // confinement, and CLAUDE.md names path traversal a standing concern here.
    //
    // Checked BEFORE `to_file_path` so the error names the real problem rather
    // than whatever the platform's path rules happen to object to first, which
    // also lets the test for it assert the same thing on every platform.
    //
    // Read the segments off the RAW URI, not off `url`. `Url::parse` decodes
    // `%2E` to `.` and then applies dot-segment removal, so by the time it has
    // a parsed value the evidence is gone: `file:///home/u/%2E%2E/secret`
    // arrives here as the innocent-looking `/home/secret`. `lsp_types::Uri` is
    // `fluent_uri`, strict RFC 3986, which normalizes nothing — it still holds
    // the string the client actually sent.
    for segment in uri.path().as_str().split('/') {
        let decoded = percent_encoding::percent_decode_str(segment).decode_utf8_lossy();
        // Only an ENCODED segment can lie. A literal `..` is ordinary relative
        // syntax that RFC 3986 resolves and `Url::parse` has already applied —
        // `include "../shared/x.bean"` produces exactly that and must keep
        // working. `%2E%2E` is a segment NAMED `..`, which is a different claim
        // and an impossible file. Comparing against the raw text is what tells
        // the two apart, and checking the decoded form alone rejected both.
        if decoded == segment {
            continue;
        }
        // `std::path::is_separator` rather than a literal `/` and `\\`: on Unix
        // a backslash is an ORDINARY filename character, and rejecting it here
        // refused the perfectly legal `/tmp/x\\y.bean`. The exhaustive byte
        // sweep below caught that within a minute of it being written.
        if decoded == "." || decoded == ".." || decoded.contains(std::path::is_separator) {
            return Err(PathUriError::DeceptiveSegment);
        }
    }

    // A `file:` URI's path is absolute by construction, so this cannot fail —
    // but it is the check that makes that a fact rather than an assumption, and
    // it is where every path in this crate acquires the invariant.
    let path = url
        .to_file_path()
        .map_err(|()| PathUriError::NotALocalFile)?;
    AbsPathBuf::new(path)
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
/// [`PathUriError::Unencodable`] if the result is still not a URI `lsp-types`
/// will parse — the catch-all for any byte `url` emits that `fluent_uri`
/// refuses. Both branches are live; neither is defensive padding.
pub fn path_to_uri(path: &std::path::Path) -> Result<Uri, PathUriError> {
    let url = url::Url::from_file_path(path).map_err(|()| PathUriError::NotAbsolute)?;

    // `from_file_path` copies `.` and `..` through verbatim, but `Url::parse`
    // applies RFC 3986 remove_dot_segments — which is what `uri_to_path` gets,
    // since it parses. Without this the two are not inverses:
    // `/home/a/2026/../shared/x.bean` produced a URI that came back as
    // `/home/a/shared/x.bean`, so a document link for an `include "../x"`
    // named a URI matching no other URI the server emits for that same file,
    // and an editor opened a second detached tab for an already-open buffer.
    // Re-parsing borrows `url`'s own dot-segment removal rather than adding a
    // hand-rolled copy of logic it already owns.
    let url = url::Url::parse(url.as_str()).map_err(|_| PathUriError::Unencodable)?;

    // `url` encodes to the WHATWG path set, which leaves `[ ] ^ |` literal;
    // `lsp-types` parses with `fluent_uri`, strict RFC 3986, where none of them
    // is a `pchar`. Composing the lax encoder with the strict parser means a
    // perfectly ordinary path like `Statements/[2026-01] bank.pdf` produces a
    // string that will not parse, and the function fails — no document link, no
    // goto-definition, no diagnostics for that file.
    //
    // ONLY over the path. An earlier version ran this across the whole string
    // on the reasoning that a UNC host "is a name and cannot contain these
    // characters" — false for an IP literal: `file://[::1]/share/x.bean` is a
    // legal URI that the pass turned into `file://%5B::1%5D/share/x.bean`,
    // which neither `fluent_uri` nor `url` will parse. Escaping the authority
    // can only ever corrupt it, since `url` has already encoded it correctly.
    let full = url.as_str();
    let path_part = url.path();
    // `from_file_path` emits no query and no fragment, so the path is the tail.
    debug_assert!(
        full.ends_with(path_part),
        "file URL has a query or fragment"
    );
    let split = full.len() - path_part.len();
    let mut out = String::with_capacity(full.len());
    out.push_str(&full[..split]);
    for ch in full[split..].chars() {
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
    // POSIX paths and `file:///home/...` URIs: on Windows `/tmp/x` is not
    // absolute and a driveless URI has no path, so this asserts a shape the
    // code never receives there. The Windows shapes have their own module.
    #[cfg(unix)]
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
    // POSIX paths and `file:///home/...` URIs: on Windows `/tmp/x` is not
    // absolute and a driveless URI has no path, so this asserts a shape the
    // code never receives there. The Windows shapes have their own module.
    #[cfg(unix)]
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
        #[cfg(unix)]
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
        // The first two are the ORIGINAL cases, and both passed for the wrong
        // reason: `untitled:Untitled-1` is cannot-be-a-base and
        // `https://example.com` has a foreign host, so `to_file_path` refused
        // them on grounds that have nothing to do with the scheme. Neither
        // could ever have caught a missing scheme check, which is what this
        // test is named for.
        //
        // The rest are the shapes that DID leak through: a hostless URI with a
        // real absolute path. Editors send all of them for a beancount buffer.
        for u in [
            "untitled:Untitled-1",
            "https://example.com/x.bean",
            // vim-fugitive, viewing a file's git history
            "fugitive:///home/rob/ledger/main.beancount",
            // VS Code's built-in Git extension, opening a diff
            "git:/home/rob/ledger/main.beancount?%7B%22ref%22%3A%22~%22%7D",
            "vscode-notebook-cell:/home/rob/nb.ipynb#W0sZmlsZQ",
            // `localhost` IS accepted as a local host by `to_file_path`, so
            // only the scheme check stands between this and `/etc/passwd`.
            "https://localhost/etc/passwd",
        ] {
            assert_eq!(
                uri_to_path(&uri(u)),
                Err(PathUriError::NotALocalFile),
                "{u} must not resolve to a path"
            );
        }
    }

    /// A segment that decodes into path syntax names a file outside the
    /// structure the URI shows.
    ///
    /// RFC 3986 removes dot segments BEFORE percent-decoding, so `%2E%2E` is a
    /// segment literally named `..` and `%2F` is a separator inside one name.
    /// `to_file_path` decodes first and lets the result act as syntax.
    #[test]
    fn a_segment_that_decodes_into_path_syntax_is_refused() {
        for u in [
            // was `/home/secret` — one directory above what the URI shows
            "file:///home/u/%2E%2E/secret",
            // was `/home/u/l/../../etc/passwd`
            "file:///home/u/l/%2E%2E%2F%2E%2E%2Fetc/passwd",
            // three segments in, four path components out
            "file:///a/b%2Fc/d",
        ] {
            assert_eq!(
                uri_to_path(&uri(u)),
                Err(PathUriError::DeceptiveSegment),
                "{u} must not resolve to a path"
            );
        }

        // A plain `..` is removed by the parser long before this check, so an
        // ordinary relative include still resolves rather than being refused.
        // POSIX-shaped, so `cfg(unix)`: the refusals above are platform-neutral
        // (the segment check runs before `to_file_path`), but this one asserts a
        // real resolved path.
        #[cfg(unix)]
        assert_eq!(
            uri_to_path(&uri("file:///home/a/ledger/../shared/x.bean")),
            Ok(AbsPathBuf::new("/home/a/shared/x.bean").expect("absolute"))
        );
    }

    /// The converters are inverses over dot segments.
    ///
    /// `from_file_path` copies `.` and `..` through verbatim while `Url::parse`
    /// removes them, so `path_to_uri` used to emit a URI that `uri_to_path`
    /// resolved to a DIFFERENT path. `resolve_full_path` builds document-link
    /// targets with `Path::join`, which preserves the `../` from
    /// `include "../shared/x.bean"`, so this was the shape it emitted: an
    /// editor opened a second, detached tab for a file already open under the
    /// normalized URI, and edits in one were invisible to the other.
    #[cfg(unix)]
    #[test]
    fn dot_segments_are_normalized_so_the_pair_inverts() {
        for (input, want) in [
            ("/home/rob/2026/../shared/a.bean", "/home/rob/shared/a.bean"),
            ("/home/rob/./a.bean", "/home/rob/a.bean"),
            ("/a/b/../../c", "/c"),
        ] {
            let path = std::path::Path::new(input);
            let uri = path_to_uri(path).unwrap_or_else(|e| panic!("{input}: {e}"));
            assert!(
                !uri.as_str().contains("/../") && !uri.as_str().contains("/./"),
                "{input} produced un-normalized {}",
                uri.as_str()
            );
            assert_eq!(
                uri_to_path(&uri).unwrap_or_else(|e| panic!("{input}: {e}")),
                std::path::PathBuf::from(want),
                "{input}"
            );
        }
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
    /// relative path and the function correctly refuses it. Asserting a
    /// hand-written `C:/x` on Linux instead would test a shape the code never
    /// receives, which is how the backslash bug in #1867 got through.
    ///
    /// This runs in the `lsp-windows` CI job. An earlier version of this
    /// comment claimed `release-test.yml` covered it — it does not: its two
    /// `windows-latest` jobs download a published binary and run `rledger
    /// check`, and no workflow in this repo ran `cargo test` on Windows at all,
    /// so this assertion executed nowhere. A `cfg` that nothing compiles is an
    /// assertion nobody makes.
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

    /// EVERY byte a POSIX filename may contain survives a round trip.
    ///
    /// Exhaustive rather than a corpus. The `[ ] ^ |` gap existed because `url`
    /// encodes to the WHATWG path set and `fluent_uri` parses strict RFC 3986,
    /// and it survived review precisely because the hand-picked corpus happened
    /// to contain no character of that class. A list of examples can only cover
    /// what its author thought of; enumerating the alphabet cannot miss a fifth
    /// character, which is the question this actually answers.
    ///
    /// `cfg(unix)` for `OsStrExt`: on Windows the legal-filename set is
    /// different and narrower, so the same sweep would not be meaningful.
    #[cfg(unix)]
    #[test]
    fn every_legal_filename_byte_round_trips() {
        use std::os::unix::ffi::OsStrExt;

        let mut bad = Vec::new();
        // All but NUL and `/`, the only two a POSIX filename cannot contain.
        for b in 1u8..=255 {
            if b == b'/' {
                continue;
            }
            let raw = [b'x', b, b'y'];
            let path = std::path::Path::new("/tmp").join(std::ffi::OsStr::from_bytes(&raw));
            match path_to_uri(&path) {
                Err(e) => bad.push(format!("{b:#04x}: path_to_uri: {e}")),
                Ok(uri) => match uri_to_path(&uri) {
                    Err(e) => bad.push(format!("{b:#04x}: uri_to_path: {e} ({})", uri.as_str())),
                    Ok(back) if back != path => {
                        bad.push(format!("{b:#04x}: {back:?} != {path:?}"));
                    }
                    Ok(_) => {}
                },
            }
        }
        assert!(bad.is_empty(), "bytes that do not round trip: {bad:#?}");
    }

    /// The half of the Windows question that IS testable anywhere: the escaping
    /// `url` omits and `lsp-types` requires is applied regardless of platform.
    #[test]
    fn the_strict_parser_gap_is_closed_on_every_platform() {
        // Anchored to whatever THIS platform calls absolute, so it runs
        // everywhere while still going through `path_to_uri`. An earlier
        // version asserted only that `"file:///tmp/a[1].bean".parse::<Uri>()`
        // fails and the escaped spelling parses — both properties of
        // `fluent_uri`, true whether or not this crate escapes anything, so
        // deleting the entire escape pass left it green. It was named as the
        // portable guard for that pass and could not fail on it.
        let base = if cfg!(windows) {
            std::path::PathBuf::from("C:\\tmp")
        } else {
            std::path::PathBuf::from("/tmp")
        };
        for (name, want_tail) in [
            ("a[1].bean", "a%5B1%5D.bean"),
            ("a^b.bean", "a%5Eb.bean"),
            ("a|b.bean", "a%7Cb.bean"),
            ("[2026-01] bank.pdf", "%5B2026-01%5D%20bank.pdf"),
        ] {
            let path = base.join(name);
            let uri = path_to_uri(&path).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(
                uri.as_str().ends_with(want_tail),
                "{name}: got {}, want a URI ending {want_tail}",
                uri.as_str()
            );
            // And it must invert, or escaping produced a URI naming a
            // different file than the one asked about.
            assert_eq!(
                uri_to_path(&uri).unwrap_or_else(|e| panic!("{name}: {e}")),
                path
            );
        }
    }
}
