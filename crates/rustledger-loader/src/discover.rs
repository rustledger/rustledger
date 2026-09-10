//! Finding a ledger's root journal without being told where it is.
//!
//! Both the language server and `rledger format` need this: neither is
//! handed a root, but both must resolve options (`render_commas`,
//! per-commodity declarations) that only exist there. The list of names
//! lives here so the two cannot disagree about what a root looks like —
//! a file the LSP formats one way and the CLI another is precisely the
//! failure this is meant to prevent.

use std::path::{Path, PathBuf};

/// Common root journal filenames, in priority order.
pub const COMMON_ROOT_NAMES: &[&str] = &[
    "main.bean",
    "main.beancount",
    "ledger.bean",
    "ledger.beancount",
    "journal.bean",
    "journal.beancount",
    "index.bean",
    "index.beancount",
];

/// The root journal directly inside `dir`, if one is there.
///
/// Checks [`COMMON_ROOT_NAMES`] in order and returns the first that exists
/// as a file. Does not recurse and does not walk upward — see
/// [`discover_journal_upward`] for that.
#[must_use]
pub fn discover_journal_file(dir: &Path) -> Option<PathBuf> {
    for name in COMMON_ROOT_NAMES {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// The nearest root journal at or above `start`.
///
/// Walks toward the filesystem root and returns the first directory that
/// holds one. Nearest wins, so a nested sub-ledger with its own root beats
/// an outer one — the same "most specific enclosing scope" rule an editor
/// or a version-control tool uses.
///
/// `start` is a DIRECTORY. Callers with a file path should pass its parent.
#[must_use]
pub fn discover_journal_upward(start: &Path) -> Option<PathBuf> {
    let mut dir = Some(start);
    while let Some(d) = dir {
        if let Some(found) = discover_journal_file(d) {
            return Some(found);
        }
        dir = d.parent();
    }
    None
}

/// How far up the tree [`discover_include_roots_upward`] looks.
///
/// A ledger's root sits a directory or two above its statements in every
/// layout seen in the wild. Walking to the filesystem root would mean reading
/// every `.beancount` file in the user's home directory the first time a
/// scratch file is opened.
const MAX_LEVELS: usize = 8;

/// How many candidate roots [`discover_include_roots_upward`] returns.
///
/// Each one costs the caller a full ledger load to test, so the cap is what
/// keeps a directory holding many ledgers from turning one file-open into a
/// long stall. Nearest first, so the cap drops the least likely candidates.
///
/// Public because a truncated search can only end in a wrong answer that
/// looks like an ordinary one: the file's real root was dropped and it is
/// validated alone, reporting accounts as never opened with nothing to say
/// why. A caller that gets exactly this many candidates should say so.
pub const MAX_CANDIDATES: usize = 16;

/// Files that might be the root of the ledger containing `target`, nearest
/// first.
///
/// [`discover_journal_upward`] only recognizes the names in
/// [`COMMON_ROOT_NAMES`], so a ledger rooted at `m1.beancount` is invisible to
/// it and its sub-files fall back to being validated alone, reporting accounts
/// as unopened that an `include`d file opens (#2285).
///
/// This is the fallback for that: any file near `target` that declares an
/// `include` is a candidate, whatever it is called. Deliberately returns
/// candidates rather than an answer, because "does this root actually reach
/// that file" can only be settled by resolving the includes, which is the
/// caller's business and expensive enough to be worth caching there.
///
/// Cheap on purpose. Directory listings plus a substring check, no parsing: a
/// file with no `include` anywhere in it cannot be the root of anything.
#[must_use]
pub fn discover_include_roots_upward(target: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut dir = target.parent();
    for _ in 0..MAX_LEVELS {
        let Some(current) = dir else {
            break;
        };
        // An unreadable directory holds no candidates, which is not the same
        // as there being none above it. Stopping here would let one directory
        // the user cannot read hide their actual root, so carry on upward.
        let Ok(entries) = std::fs::read_dir(current) else {
            dir = current.parent();
            continue;
        };

        // Sorted so the answer does not depend on directory order, which
        // varies by filesystem. Two candidate roots in one directory is
        // already unusual; picking a different one run to run would be worse.
        let mut here: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| {
                p != target
                    && p.extension()
                        .is_some_and(|e| e == "beancount" || e == "bean")
            })
            .collect();
        here.sort();

        for candidate in here {
            if declares_an_include(&candidate) {
                out.push(candidate);
                if out.len() >= MAX_CANDIDATES {
                    return out;
                }
            }
        }
        dir = current.parent();
    }
    out
}

/// Whether `path` contains an `include` directive.
///
/// Substring rather than a parse: this runs over every nearby file to decide
/// which ones are worth loading properly, and being wrong in the permissive
/// direction only costs one load that the caller then rejects. Being wrong in
/// the other direction would hide the real root.
///
/// Chunked, because the answer is usually NO and a no costs a full read
/// however it is spelled. Reading the file into a `String` allocates the whole
/// of the ledger next door, and reading it a line at a time was measurably
/// worse again: one buffer reused across chunks beats both. The overlap is
/// what keeps a match split across a chunk boundary from being missed.
fn declares_an_include(path: &Path) -> bool {
    use std::io::Read;

    const NEEDLE: &[u8] = b"include";
    const CHUNK: usize = 256 * 1024;

    let Ok(mut file) = std::fs::File::open(path) else {
        return false;
    };
    let mut buf = vec![0u8; CHUNK + NEEDLE.len()];
    let mut carry = 0usize;
    loop {
        let read = match file.read(&mut buf[carry..]) {
            Ok(0) => return false,
            Ok(n) => n,
            // A read error is not an opinion about the file's contents.
            Err(_) => return false,
        };
        let end = carry + read;
        if contains_needle(&buf[..end], NEEDLE) {
            return true;
        }
        // Keep the tail so `inclu|de` across a boundary still matches.
        let keep = NEEDLE.len() - 1;
        if end > keep {
            buf.copy_within(end - keep..end, 0);
            carry = keep;
        } else {
            carry = end;
        }
    }
}

/// `haystack.windows(n).any(..)` for a fixed needle, without building a slice
/// per position.
///
/// Anchoring on the first byte and only then comparing is what closes the gap
/// with `str::contains`, whose optimized search this is standing in for. The
/// naive form measured at four times the cost over a megabyte of ledger, which
/// is a file this reads in full every time the answer is no.
fn contains_needle(haystack: &[u8], needle: &[u8]) -> bool {
    let Some((&first, _)) = needle.split_first() else {
        return true;
    };
    let mut at = 0;
    while let Some(offset) = haystack[at..].iter().position(|&b| b == first) {
        let start = at + offset;
        if haystack[start..].starts_with(needle) {
            return true;
        }
        at = start + 1;
    }
    false
}

#[cfg(test)]
mod tests {
    use std::fs;

    /// The #2285 shape: a root whose name discovery does not know, above a
    /// sub-file that declares no includes of its own.
    #[test]
    fn finds_a_root_that_is_not_conventionally_named() {
        let dir = tempfile::tempdir().expect("tempdir");
        let sub_dir = dir.path().join("ledger");
        fs::create_dir_all(&sub_dir).expect("mkdir");
        let target = sub_dir.join("2025-01.beancount");
        fs::write(&target, "2026-01-01 balance Assets:Cash 0.00 EUR\n").expect("write target");
        fs::write(
            dir.path().join("accounts.beancount"),
            "2025-01-01 open Assets:Cash\n",
        )
        .expect("write accounts");
        let root = dir.path().join("m1.beancount");
        fs::write(
            &root,
            "include \"accounts.beancount\"\ninclude \"ledger/2025-01.beancount\"\n",
        )
        .expect("write root");

        let found = discover_include_roots_upward(&target);
        assert!(
            found.contains(&root),
            "the include-declaring root must be a candidate; got {found:?}"
        );
        assert!(
            !found.contains(&target),
            "the file itself must never be its own candidate: {found:?}"
        );
    }

    /// A file with no `include` anywhere cannot be a root, and testing it would
    /// cost the caller a full ledger load for nothing.
    #[test]
    fn skips_files_that_declare_no_include() {
        let dir = tempfile::tempdir().expect("tempdir");
        let target = dir.path().join("txns.beancount");
        fs::write(&target, "2026-01-01 balance Assets:Cash 0.00 EUR\n").expect("write target");
        fs::write(
            dir.path().join("plain.beancount"),
            "2025-01-01 open Assets:Cash\n",
        )
        .expect("write plain");

        assert_eq!(
            discover_include_roots_upward(&target),
            Vec::<PathBuf>::new(),
            "a file with no include must not be offered as a root"
        );
    }

    /// Nearest first, because the caller takes the first that reaches the file
    /// and a sub-ledger's own root should beat an outer one.
    #[test]
    fn orders_candidates_nearest_first() {
        let dir = tempfile::tempdir().expect("tempdir");
        let inner_dir = dir.path().join("sub");
        fs::create_dir_all(&inner_dir).expect("mkdir");
        let target = inner_dir.join("txns.beancount");
        fs::write(&target, "\n").expect("write target");
        let inner = inner_dir.join("inner.beancount");
        fs::write(&inner, "include \"txns.beancount\"\n").expect("write inner");
        let outer = dir.path().join("outer.beancount");
        fs::write(&outer, "include \"sub/txns.beancount\"\n").expect("write outer");

        let found = discover_include_roots_upward(&target);
        assert_eq!(
            found.first(),
            Some(&inner),
            "the nearer root must come first; got {found:?}"
        );
        assert!(found.contains(&outer));
    }

    /// The line-at-a-time scan must not stop before it reaches the include.
    ///
    /// Short-circuiting is the point of reading this way, and a scan that
    /// gave up early would silently drop roots whose includes sit below a
    /// header comment or a block of options, which is where they usually are.
    #[test]
    fn finds_an_include_that_is_not_on_the_first_line() {
        let dir = tempfile::tempdir().expect("tempdir");
        let target = dir.path().join("txns.beancount");
        fs::write(&target, "\n").expect("write target");

        let mut body = String::new();
        body.push_str(";; a long header comment\n".repeat(500).as_str());
        body.push_str("option \"title\" \"Ledger\"\n");
        body.push_str("include \"txns.beancount\"\n");
        let root = dir.path().join("late.beancount");
        fs::write(&root, body).expect("write root");

        assert!(
            discover_include_roots_upward(&target).contains(&root),
            "an include below a header must still be found"
        );
    }

    /// An `include` straddling a chunk boundary must still be found.
    ///
    /// The scan reads a fixed chunk at a time and carries the last few bytes
    /// forward for exactly this. Nothing else exercises that carry, and an
    /// off-by-one in it fails silently: the root is simply never offered, and
    /// the user gets #2285's wrong diagnostic back with no clue why.
    ///
    /// Sweeps a window of offsets rather than computing where the boundary
    /// falls. The first draft placed the word at `CHUNK - n`, which is not the
    /// boundary at all (the buffer is a chunk plus the needle), so the word
    /// landed inside the first read every time and the case passed with the
    /// carry removed entirely. A sweep cannot be wrong about the arithmetic
    /// because it does not do any.
    #[test]
    fn finds_an_include_split_across_a_chunk_boundary() {
        const CHUNK: usize = 256 * 1024;
        let dir = tempfile::tempdir().expect("tempdir");

        for offset in (CHUNK - 8)..(CHUNK + 32) {
            let root = dir.path().join("root.beancount");
            let mut body = ";".repeat(offset);
            body.push_str("include \"txns.beancount\"\n");
            fs::write(&root, &body).expect("write root");

            assert!(
                declares_an_include(&root),
                "`include` starting at byte {offset} was missed; \
                 the chunk carry does not cover this alignment"
            );
        }
    }

    /// The candidate cap is exact, so a caller can tell saturation from a
    /// directory that simply holds that many ledgers.
    ///
    /// Nothing else pins the number, and a cap that quietly returned one more
    /// or one fewer would make the caller's "did we truncate" check wrong in
    /// the direction that stays silent.
    #[test]
    fn returns_at_most_max_candidates() {
        let dir = tempfile::tempdir().expect("tempdir");
        let target = dir.path().join("txns.beancount");
        fs::write(&target, "\n").expect("write target");
        for i in 0..(MAX_CANDIDATES + 5) {
            fs::write(
                dir.path().join(format!("root{i:03}.beancount")),
                "include \"txns.beancount\"\n",
            )
            .expect("write root");
        }

        assert_eq!(
            discover_include_roots_upward(&target).len(),
            MAX_CANDIDATES,
            "the cap must be exact for the caller's saturation check to mean anything"
        );
    }

    /// Bytes that are not UTF-8 must not panic or be reported as a root.
    #[test]
    fn a_non_utf8_file_is_not_a_candidate() {
        let dir = tempfile::tempdir().expect("tempdir");
        let target = dir.path().join("txns.beancount");
        fs::write(&target, "\n").expect("write target");
        fs::write(
            dir.path().join("binary.beancount"),
            [0xff, 0xfe, 0x00, 0x01],
        )
        .expect("write binary");

        assert_eq!(
            discover_include_roots_upward(&target),
            Vec::<PathBuf>::new(),
            "unreadable bytes are not an include"
        );
    }

    /// The walk is bounded. Without a cap, opening a scratch file would read
    /// every beancount file between it and the filesystem root.
    #[test]
    fn stops_walking_up_after_max_levels() {
        let dir = tempfile::tempdir().expect("tempdir");
        let mut deep = dir.path().to_path_buf();
        for i in 0..(MAX_LEVELS + 3) {
            deep = deep.join(format!("d{i}"));
        }
        fs::create_dir_all(&deep).expect("mkdir");
        let target = deep.join("txns.beancount");
        fs::write(&target, "\n").expect("write target");
        // A root far enough up to be outside the walk.
        fs::write(
            dir.path().join("root.beancount"),
            "include \"x.beancount\"\n",
        )
        .expect("write root");

        assert_eq!(
            discover_include_roots_upward(&target),
            Vec::<PathBuf>::new(),
            "a root beyond MAX_LEVELS must not be reached"
        );
    }

    use super::*;

    #[test]
    fn finds_a_root_beside_the_file_and_prefers_the_nearest() {
        let dir = tempfile::tempdir().expect("tempdir");
        let outer = dir.path();
        let inner = outer.join("sub/deeper");
        std::fs::create_dir_all(&inner).expect("mkdir");

        std::fs::write(outer.join("main.beancount"), "").expect("write outer");
        assert_eq!(
            discover_journal_upward(&inner),
            Some(outer.join("main.beancount")),
            "walks up when nothing is nearer"
        );

        let nested = outer.join("sub").join("ledger.beancount");
        std::fs::write(&nested, "").expect("write inner");
        assert_eq!(
            discover_journal_upward(&inner),
            Some(nested),
            "a nearer root wins over an outer one"
        );
    }

    #[test]
    fn name_priority_is_stable_and_directories_do_not_count() {
        let dir = tempfile::tempdir().expect("tempdir");
        // A DIRECTORY named like a root must not be mistaken for one.
        std::fs::create_dir(dir.path().join("main.bean")).expect("mkdir");
        assert_eq!(discover_journal_file(dir.path()), None);

        std::fs::write(dir.path().join("journal.beancount"), "").expect("write");
        std::fs::write(dir.path().join("main.beancount"), "").expect("write");
        assert_eq!(
            discover_journal_file(dir.path()),
            Some(dir.path().join("main.beancount")),
            "`main.beancount` outranks `journal.beancount`"
        );
    }

    #[test]
    fn returns_none_when_there_is_no_ledger_anywhere_above() {
        let dir = tempfile::tempdir().expect("tempdir");
        let deep = dir.path().join("a/b/c");
        std::fs::create_dir_all(&deep).expect("mkdir");
        // The walk reaches the filesystem root and stops; tempdirs live
        // under /tmp, which has no journal.
        assert_eq!(discover_journal_upward(&deep), None);
    }
}
