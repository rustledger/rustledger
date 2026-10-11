use super::equivalence::{self, Fingerprint};
use super::overlay::OverlayFs;
use super::segment::segment;
use super::split::{Period, plan};
use super::{merge, split, swap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn tmp() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("rl-restructure-")
        .tempdir()
        .expect("tempdir")
}

fn write(dir: &Path, name: &str, text: &str) -> PathBuf {
    let p = dir.join(name);
    if let Some(parent) = p.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(&p, text).unwrap();
    p.canonicalize().unwrap()
}

fn fingerprint(root: &Path) -> Fingerprint {
    equivalence::load(root, OverlayFs::disk()).unwrap().0
}

fn split_args(file: &Path, by: Period) -> split::Args {
    split::Args {
        file: Some(file.to_path_buf()),
        by,
        dir: None,
        ledger: None,
        dry_run: false,
    }
}

fn merge_args(file: &Path) -> merge::Args {
    merge::Args {
        file: Some(file.to_path_buf()),
        output: None,
        keep_included: false,
        ledger: None,
        dry_run: false,
    }
}

/// Run split; returns (exit code, stdout, stderr).
fn run_split(args: &split::Args) -> (ExitCode, String, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let code = split::run_with_writer(args, &mut out, &mut err).unwrap();
    (
        code,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

fn run_merge(args: &merge::Args) -> (ExitCode, String, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let code = merge::run_with_writer(args, &mut out, &mut err).unwrap();
    (
        code,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// Every file under `dir` (recursively) with its bytes, excluding backups.
fn snapshot(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else {
                out.push((p.clone(), fs::read(&p).unwrap()));
            }
        }
    }
    out.sort();
    out
}

const LEDGER: &str = r#"; My ledger
; kept as the file header

option "title" "Test"
option "operating_currency" "USD"
plugin "beancount.plugins.auto_accounts"

2023-01-01 open Assets:Bank USD
2023-01-01 open Assets:Broker USD,STOCK "FIFO"
2023-01-01 open Income:Salary USD
2023-01-01 open Expenses:Food USD

; January pay
2023-01-31 * "Employer" "Pay"
  Assets:Bank      1000 USD
  Income:Salary   -1000 USD

2023-06-01 * "Buy" #invest
  Assets:Broker    10 STOCK {10 USD}
  Assets:Bank    -100 USD

2023-12-31 balance Assets:Bank  900 USD

; ---- 2024 ----
; The first lunch of the year
2024-01-02 * "Lunch"  ; trailing note
  Expenses:Food     12 USD
  Assets:Bank      -12 USD

2024-03-01 * "Sell"
  Assets:Broker    -5 STOCK {} @ 20 USD
  Assets:Bank     100 USD
  Income:Salary  -50 USD

; end of file
"#;

#[test]
fn split_by_year_round_trips_through_merge() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let original = fingerprint(&file);

    let (code, out, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "stdout: {out}\nstderr: {err}");
    assert!(out.contains("Equivalence check passed"), "{out}");

    let y2023 = fs::read_to_string(dir.path().join("ledger/2023.beancount")).unwrap();
    let y2024 = fs::read_to_string(dir.path().join("ledger/2024.beancount")).unwrap();
    let root = fs::read_to_string(&file).unwrap();
    assert!(
        y2023.starts_with("2023-01-01 open Assets:Bank USD\n"),
        "{y2023}"
    );
    assert!(!y2023.contains("2024-"), "{y2023}");
    assert!(!y2024.contains("2023-"), "{y2024}");
    assert_eq!(
        root,
        "; My ledger\n; kept as the file header\n\noption \"title\" \"Test\"\n\
         option \"operating_currency\" \"USD\"\n\
         plugin \"beancount.plugins.auto_accounts\"\n\n\
         include \"ledger/2023.beancount\"\ninclude \"ledger/2024.beancount\"\n\n\
         ; end of file\n"
    );
    assert_eq!(fingerprint(&file), original, "split changed the ledger");

    let (code, out, err) = run_merge(&merge_args(&file));
    assert_eq!(code, ExitCode::SUCCESS, "stdout: {out}\nstderr: {err}");
    assert_eq!(fingerprint(&file), original, "merge changed the ledger");
    assert!(!dir.path().join("ledger/2023.beancount").exists());
    assert!(!dir.path().join("ledger/2024.beancount").exists());
    let merged = fs::read_to_string(&file).unwrap();
    assert!(!merged.contains("include"), "{merged}");
    // Every line of the original survives, verbatim, somewhere in the merge.
    for line in LEDGER.lines() {
        assert!(merged.contains(line), "lost line {line:?}:\n{merged}");
    }
}

#[test]
fn split_by_month_names_files_by_month() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let original = fingerprint(&file);
    let (code, out, err) = run_split(&split_args(&file, Period::Month));
    assert_eq!(code, ExitCode::SUCCESS, "stdout: {out}\nstderr: {err}");
    for m in ["2023-01", "2023-06", "2023-12", "2024-01", "2024-03"] {
        assert!(
            dir.path().join(format!("ledger/{m}.beancount")).exists(),
            "missing {m}"
        );
    }
    assert_eq!(fingerprint(&file), original);
}

/// Comments move with the directive they precede, verbatim; the file header
/// and the trailer stay in the root.
#[test]
fn comments_move_with_the_directive_they_precede() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let (code, _, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{err}");
    let y2023 = fs::read_to_string(dir.path().join("ledger/2023.beancount")).unwrap();
    let y2024 = fs::read_to_string(dir.path().join("ledger/2024.beancount")).unwrap();
    assert!(y2023.contains("\n; January pay\n2023-01-31 * \"Employer\" \"Pay\"\n"));
    assert!(y2024.starts_with(
        "; ---- 2024 ----\n; The first lunch of the year\n2024-01-02 * \"Lunch\"  ; trailing note\n"
    ));
    let root = fs::read_to_string(&file).unwrap();
    assert!(root.starts_with("; My ledger\n; kept as the file header\n"));
    assert!(root.ends_with("; end of file\n"));
}

#[test]
fn dry_run_writes_nothing() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let before = snapshot(dir.path());
    let mut args = split_args(&file, Period::Year);
    args.dry_run = true;
    let (code, out, _) = run_split(&args);
    assert_eq!(code, ExitCode::SUCCESS);
    assert!(out.contains("create   ledger/2023.beancount") || out.contains("2023.beancount"));
    assert!(out.contains("Dry run: nothing was written."), "{out}");
    assert_eq!(snapshot(dir.path()), before, "dry run touched the disk");

    // And for merge.
    write(
        dir.path(),
        "part.beancount",
        "2020-01-01 open Assets:Cash\n",
    );
    let inc = write(dir.path(), "main.beancount", "include \"part.beancount\"\n");
    let before = snapshot(dir.path());
    let mut m = merge_args(&inc);
    m.dry_run = true;
    let (code, out, err) = run_merge(&m);
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(
        snapshot(dir.path()),
        before,
        "merge dry run touched the disk"
    );
}

#[test]
fn split_backs_up_the_original_and_writes_a_manifest() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let (code, out, _) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS);
    assert!(out.contains("Backup of the original files"), "{out}");
    let backups: Vec<PathBuf> = fs::read_dir(dir.path().join(".rledger-backup"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    assert_eq!(backups.len(), 1);
    let saved = fs::read_to_string(backups[0].join("ledger.beancount.bak")).unwrap();
    assert_eq!(saved, LEDGER);
    let manifest = fs::read_to_string(backups[0].join("manifest.txt")).unwrap();
    assert!(manifest.contains("saved\t"), "{manifest}");
    assert!(manifest.contains("created\t"), "{manifest}");
    // No temporaries left behind.
    assert!(
        snapshot(dir.path())
            .iter()
            .all(|(p, _)| !p.to_string_lossy().contains("rledger-tmp")),
    );
}

#[test]
fn split_refuses_to_overwrite_an_existing_period_file() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    write(dir.path(), "ledger/2024.beancount", "; mine\n");
    let before = snapshot(dir.path());
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let e = split::run_with_writer(&split_args(&file, Period::Year), &mut out, &mut err)
        .unwrap_err()
        .to_string();
    assert!(e.contains("already exists"), "{e}");
    assert_eq!(snapshot(dir.path()), before);
}

/// The swap restores the originals when the post-write verification fails,
/// and removes what it created.
#[test]
fn failed_verification_restores_the_backup() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", "; original\n");
    let new = dir.path().join("sub/new.beancount");
    let plan = swap::Plan {
        writes: vec![
            (new.clone(), "; new\n".to_string()),
            (file.clone(), "; replaced\n".to_string()),
        ],
        commit: file.clone(),
        removes: Vec::new(),
        backup_base: dir.path().canonicalize().unwrap(),
        originals: vec![(file.clone(), b"; original\n".to_vec())],
        operation: "split",
        template: file.clone(),
        mode_mask: None,
    };
    let e = swap::apply(&plan, || anyhow::bail!("simulated mismatch")).unwrap_err();
    assert!(format!("{e:#}").contains("restored"), "{e:#}");
    assert_eq!(fs::read_to_string(&file).unwrap(), "; original\n");
    assert!(!new.exists());
    assert!(!dir.path().join("sub").exists());
}

/// The check must be able to say "dirty". A split that drops one
/// transaction, and one that moves a same-date lot into another file the way
/// an account split would, are both refused.
#[test]
fn the_check_refuses_a_broken_split() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let before = super::load_before(&file).unwrap();

    // 1. Lose a directive.
    let src = fs::read_to_string(&file).unwrap();
    let seg = segment(&src, &file).unwrap();
    let layout = plan(&seg, Period::Year, &src).unwrap();
    let mut writes: Vec<(PathBuf, String)> = Vec::new();
    let mut includes = Vec::new();
    for (key, (content, _)) in &layout.periods {
        let p = dir.path().join(format!("ledger/{key}.beancount"));
        includes.push(format!("include \"ledger/{key}.beancount\""));
        let content = if key == "2024" {
            content.replace("2024-01-02 * \"Lunch\"", "2024-01-02 * \"Dinner\"")
        } else {
            content.clone()
        };
        writes.push((p, content));
    }
    writes.push((file.clone(), layout.root_text(&includes, "\n")));
    let diff = super::check_planned(&file, &before, &writes, &[]).unwrap();
    assert!(
        diff.as_deref()
            .is_some_and(|d| d.contains("directive stream differs")),
        "{diff:?}"
    );

    // 2. Include the period files in the wrong order relative to an existing
    // include holding a same-date lot: FIFO then sells a different lot.
    let dir = tmp();
    let root = write(
        dir.path(),
        "main.beancount",
        "option \"booking_method\" \"FIFO\"\n\
         include \"accounts.beancount\"\n\
         include \"lots-b.beancount\"\n\
         2024-01-01 * \"Buy A\"\n  Assets:Broker  1 STOCK {10 USD}\n  Assets:Bank\n\
         2024-02-01 * \"Sell\"\n  Assets:Broker  -1 STOCK {} @ 30 USD\n  Assets:Bank  30 USD\n  Income:Gains\n",
    );
    write(
        dir.path(),
        "accounts.beancount",
        "2020-01-01 open Assets:Broker\n2020-01-01 open Assets:Bank\n2020-01-01 open Income:Gains\n",
    );
    write(
        dir.path(),
        "lots-b.beancount",
        "2024-01-01 * \"Buy B\"\n  Assets:Broker  1 STOCK {20 USD}\n  Assets:Bank\n",
    );
    let before = super::load_before(&root).unwrap();
    let src = fs::read_to_string(&root).unwrap();
    // Period include AFTER the existing includes: Buy A now sorts after Buy B.
    let wrong = "option \"booking_method\" \"FIFO\"\n\
                 include \"accounts.beancount\"\n\
                 include \"lots-b.beancount\"\n\
                 include \"main/2024.beancount\"\n";
    let seg = segment(&src, &root).unwrap();
    let layout = plan(&seg, Period::Year, &src).unwrap();
    let period = layout.periods["2024"].0.clone();
    let writes = vec![
        (dir.path().join("main/2024.beancount"), period),
        (root.clone(), wrong.to_string()),
    ];
    let diff = super::check_planned(&root, &before, &writes, &[]).unwrap();
    assert!(diff.is_some(), "a reordered same-date lot must be refused");

    // ... while the real split of the same ledger passes.
    let (code, out, err) = run_split(&split_args(&root, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    let new_root = fs::read_to_string(&root).unwrap();
    let period_at = new_root.find("main/2024.beancount").unwrap();
    let existing_at = new_root.find("accounts.beancount").unwrap();
    assert!(
        period_at < existing_at,
        "period includes must precede existing ones:\n{new_root}"
    );
}

/// A relative `document` path resolves against its file's directory, so
/// moving it into `ledger/` would point it elsewhere: refused, exit 1, nothing
/// written. With `--dir .` the files stay beside the root and it passes.
#[test]
fn relative_document_paths_are_protected() {
    let dir = tmp();
    write(dir.path(), "receipt.pdf", "%PDF");
    let file = write(
        dir.path(),
        "ledger.beancount",
        "2024-01-01 open Assets:Bank\n2024-01-05 document Assets:Bank \"receipt.pdf\"\n",
    );
    let before = snapshot(dir.path());
    let (code, _, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::from(1), "{err}");
    assert!(
        err.contains("document path would resolve differently"),
        "{err}"
    );
    assert!(err.contains("Nothing was written"), "{err}");
    assert_eq!(snapshot(dir.path()), before);

    let mut args = split_args(&file, Period::Year);
    args.dir = Some(dir.path().to_path_buf());
    let (code, out, err) = run_split(&args);
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert!(dir.path().join("2024.beancount").exists());
}

/// A `pushtag`/`pushmeta` span that crosses the year boundary still applies
/// to every directive it covered, and every new file is balanced.
#[test]
fn pushtag_and_pushmeta_spans_survive_a_boundary() {
    let src = "2023-01-01 open Assets:Bank\n\
               2023-01-01 open Expenses:Travel\n\
               \n\
               ; the trip\n\
               pushtag #trip\n\
               pushmeta trip-id: \"paris\"\n\
               2023-12-30 * \"Hotel\"\n  Expenses:Travel  100 USD\n  Assets:Bank\n\
               pushtag #inner\n\
               2023-12-31 * \"Dinner\"\n  Expenses:Travel  50 USD\n  Assets:Bank\n\
               2024-01-02 * \"Flight\"\n  Expenses:Travel  300 USD\n  Assets:Bank\n\
               poptag #inner\n\
               2024-01-03 * \"Taxi\"\n  Expenses:Travel  30 USD\n  Assets:Bank\n\
               popmeta trip-id:\n\
               ; trip over\n\
               poptag #trip\n\
               2024-02-01 * \"Home\"\n  Expenses:Travel  1 USD\n  Assets:Bank\n";
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", src);
    let original = fingerprint(&file);
    let (code, out, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(fingerprint(&file), original);

    let y2023 = fs::read_to_string(dir.path().join("ledger/2023.beancount")).unwrap();
    let y2024 = fs::read_to_string(dir.path().join("ledger/2024.beancount")).unwrap();
    // The original push lines, with their comment, are in the file of the
    // first directive they cover; the pop with its comment in the file of
    // the last.
    assert!(y2023.contains("; the trip\npushtag #trip\n"), "{y2023}");
    assert!(y2024.contains("; trip over\npoptag #trip\n"), "{y2024}");
    // 2023 closes what is still open; 2024 re-opens it.
    assert!(
        y2023
            .trim_end()
            .ends_with("poptag #inner\npopmeta trip-id:\npoptag #trip"),
        "{y2023}"
    );
    assert!(
        y2024.starts_with("pushtag #trip\npushmeta trip-id: \"paris\"\npushtag #inner\n2024-01-02"),
        "{y2024}"
    );
    // Each file parses clean on its own: balanced stacks.
    for (name, text) in [("2023", &y2023), ("2024", &y2024)] {
        let errs = rustledger_parser::parse(text).errors;
        assert!(errs.is_empty(), "{name}: {errs:?}");
    }
}

/// A ledger that already uses includes: they stay in the root, and merge
/// flattens nested includes and globs in loader order.
#[test]
fn existing_includes_and_nested_merge() {
    let dir = tmp();
    let root = write(
        dir.path(),
        "main.beancount",
        "option \"operating_currency\" \"USD\"\n\
         ; accounts live elsewhere\n\
         include \"accounts.beancount\"\n\
         include \"years/*.beancount\"\n\
         2024-06-01 * \"Root txn\"\n  Expenses:Food  1 USD\n  Assets:Bank\n",
    );
    write(
        dir.path(),
        "accounts.beancount",
        "2020-01-01 open Assets:Bank\n2020-01-01 open Expenses:Food\ninclude \"more/nested.beancount\"\n",
    );
    write(
        dir.path(),
        "more/nested.beancount",
        "2020-01-01 open Income:Job\n",
    );
    write(
        dir.path(),
        "years/2021.beancount",
        "2021-01-01 * \"a\"\n  Expenses:Food  2 USD\n  Assets:Bank\n",
    );
    write(
        dir.path(),
        "years/2022.beancount",
        "2022-01-01 * \"b\"\n  Expenses:Food  3 USD\n  Assets:Bank\n",
    );
    let original = fingerprint(&root);

    let (code, out, err) = run_split(&split_args(&root, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    let text = fs::read_to_string(&root).unwrap();
    assert!(text.contains("; accounts live elsewhere\ninclude \"accounts.beancount\""));
    assert_eq!(fingerprint(&root), original);

    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(fingerprint(&root), original);
    let merged = fs::read_to_string(&root).unwrap();
    assert!(!merged.contains("include"), "{merged}");
    assert!(merged.contains("; accounts live elsewhere\n"), "{merged}");
    for gone in [
        "accounts.beancount",
        "more/nested.beancount",
        "years/2021.beancount",
        "main/2024.beancount",
    ] {
        assert!(!dir.path().join(gone).exists(), "{gone} not removed");
    }
}

#[test]
fn merge_output_leaves_the_originals_alone() {
    let dir = tmp();
    let root = write(dir.path(), "main.beancount", "include \"a.beancount\"\n");
    write(dir.path(), "a.beancount", "2020-01-01 open Assets:Bank\n");
    let before = snapshot(dir.path());
    let out_path = dir.path().join("flat.beancount");
    let mut args = merge_args(&root);
    args.output = Some(out_path.clone());
    let (code, out, err) = run_merge(&args);
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    let mut after = snapshot(dir.path());
    after.retain(|(p, _)| {
        p != &out_path.canonicalize().unwrap() && !p.to_string_lossy().contains(".rledger-backup")
    });
    assert_eq!(after, before);
    assert_eq!(fingerprint(&out_path), fingerprint(&root));
}

/// Merging where an included file sets an option the loader ignores there
/// (#2151) would make it take effect: refused.
#[test]
fn merge_refuses_an_option_that_would_start_applying() {
    let dir = tmp();
    let root = write(dir.path(), "main.beancount", "include \"a.beancount\"\n");
    write(
        dir.path(),
        "a.beancount",
        "option \"booking_method\" \"LIFO\"\n2020-01-01 open Assets:Bank\n",
    );
    let before = snapshot(dir.path());
    let (code, _, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::from(1), "{err}");
    assert_eq!(snapshot(dir.path()), before);
}

#[test]
fn org_mode_headings_and_crlf_are_kept() {
    let src = "option \"title\" \"x\"\r\n\r\n* 2023\r\n2023-01-01 open Assets:Bank\r\n\r\n* 2024\r\n2024-01-01 note Assets:Bank \"hi\"\r\n";
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", src);
    let original = fingerprint(&file);
    let (code, out, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(fingerprint(&file), original);
    let y2024 = fs::read_to_string(dir.path().join("ledger/2024.beancount")).unwrap();
    assert!(y2024.contains("* 2024\r\n2024-01-01 note"), "{y2024:?}");
    let root = fs::read_to_string(&file).unwrap();
    assert!(
        root.contains("include \"ledger/2023.beancount\"\r\n"),
        "{root:?}"
    );
}

#[test]
fn parse_errors_are_refused() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", "2024-01-01 open\n");
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let e = split::run_with_writer(&split_args(&file, Period::Year), &mut out, &mut err)
        .unwrap_err()
        .to_string();
    assert!(e.contains("parse error"), "{e}");
}

/// Segmentation is lossless: the pieces concatenate back to the source.
#[test]
fn segmentation_is_lossless() {
    for src in [
        LEDGER,
        "\u{FEFF}; bom\n2024-01-01 open Assets:A\n",
        "2024-01-01 open Assets:A",
        "\n\n; only a comment\n",
        "pushtag #a\n2024-01-01 note Assets:A \"x\"\npoptag #a\n; tail",
    ] {
        let seg = segment(src, Path::new("x")).unwrap();
        let mut joined = seg.leading.clone();
        for i in &seg.items {
            joined.push_str(&i.text);
        }
        joined.push_str(&seg.trailing);
        assert_eq!(joined, src);
    }
}

/// A period file must never be the file being split: `2024.beancount` split
/// by year into its own directory would otherwise be written twice.
#[test]
fn a_period_file_cannot_overwrite_the_split_file() {
    let dir = tmp();
    let file = write(
        dir.path(),
        "2024.beancount",
        "2024-01-01 open Assets:Bank\n2023-01-01 open Assets:Cash\n",
    );
    let before = snapshot(dir.path());
    let mut args = split_args(&file, Period::Year);
    args.dir = Some(dir.path().to_path_buf());
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let e = split::run_with_writer(&args, &mut out, &mut err)
        .unwrap_err()
        .to_string();
    assert!(e.contains("would overwrite the file being split"), "{e}");
    assert_eq!(snapshot(dir.path()), before);
}

/// Merge never deletes a file it does not own: an include reached through a
/// symlink, or one outside FILE's directory, may belong to another ledger.
#[cfg(unix)]
#[test]
fn merge_keeps_symlinked_and_out_of_tree_includes() {
    let dir = tmp();
    let shared = write(
        dir.path(),
        "shared/accounts.beancount",
        "2020-01-01 open Assets:Bank\n",
    );
    let outside = write(
        dir.path(),
        "common.beancount",
        "2020-01-01 open Assets:Cash\n",
    );
    let inside = write(
        dir.path(),
        "ledger/own.beancount",
        "2020-01-01 open Assets:Own\n",
    );
    std::os::unix::fs::symlink(&shared, dir.path().join("ledger/accounts.beancount")).unwrap();
    let root = write(
        dir.path(),
        "ledger/main.beancount",
        "include \"accounts.beancount\"\ninclude \"../common.beancount\"\ninclude \"own.beancount\"\n",
    );
    let original = fingerprint(&root);
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(fingerprint(&root), original);
    assert!(shared.exists(), "the symlink's target was deleted");
    assert!(dir.path().join("ledger/accounts.beancount").exists());
    assert!(outside.exists(), "an out-of-tree include was deleted");
    assert!(
        !inside.exists(),
        "the plain in-tree include should be removed"
    );
    assert!(out.contains("kept"), "{out}");
}

/// A comment on an include's own line survives the merge.
#[test]
fn merge_keeps_the_comment_on_an_include_line() {
    let dir = tmp();
    let root = write(
        dir.path(),
        "main.beancount",
        "include \"a.beancount\" ; NOTE: keep me\n",
    );
    write(dir.path(), "a.beancount", "2020-01-01 open Assets:Bank\n");
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    let merged = fs::read_to_string(&root).unwrap();
    assert!(merged.contains("; NOTE: keep me"), "{merged}");
    assert!(!merged.contains("include"), "{merged}");
}

/// The in-memory preview sees planned files through an include glob written
/// with `./` (the loader keeps it as written), so the split is refused before
/// anything is written rather than after.
#[test]
fn the_preview_sees_planned_files_through_a_dotted_glob() {
    let dir = tmp();
    write(
        dir.path(),
        "sub/other.beancount",
        "2020-01-01 open Assets:Other\n",
    );
    let root = write(
        dir.path(),
        "main.beancount",
        "include \"./sub/*.beancount\"\n2024-01-01 open Assets:Bank\n",
    );
    let before = snapshot(dir.path());
    let mut args = split_args(&root, Period::Year);
    args.dir = Some(dir.path().join("sub"));
    let (code, out, err) = run_split(&args);
    assert_eq!(code, ExitCode::from(1), "{out}{err}");
    assert_eq!(snapshot(dir.path()), before);
}

/// New files, backups and `merge -o` output are as private as the ledger.
#[cfg(unix)]
#[test]
fn permissions_carry_over() {
    use std::os::unix::fs::PermissionsExt;
    let mode = |p: &Path| fs::metadata(p).unwrap().permissions().mode() & 0o777;
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
    let (code, _, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{err}");
    assert_eq!(mode(&dir.path().join("ledger/2023.beancount")), 0o600);
    assert_eq!(mode(&file), 0o600);
    let backup = fs::read_dir(dir.path().join(".rledger-backup"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    assert_eq!(mode(&backup.join("ledger.beancount.bak")), 0o600);

    let out_path = dir.path().join("flat.beancount");
    let mut args = merge_args(&file);
    args.output = Some(out_path.clone());
    let (code, out, err) = run_merge(&args);
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(mode(&out_path), 0o600);
    // Nothing was replaced, so there is nothing to back up.
    assert!(!out.contains("Backup"), "{out}");
    assert_eq!(
        fs::read_dir(dir.path().join(".rledger-backup"))
            .unwrap()
            .count(),
        1
    );
}

/// A file kept because it is reached through a symlink keeps its children
/// too: removing them would leave it with a dangling include.
#[cfg(unix)]
#[test]
fn merge_keeps_the_children_of_a_kept_file() {
    let dir = tmp();
    write(
        dir.path(),
        "sub/real.beancount",
        "2020-01-01 open Assets:A\ninclude \"child.beancount\"\n",
    );
    let child = write(
        dir.path(),
        "sub/child.beancount",
        "2020-01-01 open Assets:B\n",
    );
    std::os::unix::fs::symlink(
        dir.path().join("sub/real.beancount"),
        dir.path().join("link.beancount"),
    )
    .unwrap();
    let other = write(
        dir.path(),
        "other.beancount",
        "include \"sub/real.beancount\"\n",
    );
    let other_before = fingerprint(&other);
    let root = write(dir.path(), "main.beancount", "include \"link.beancount\"\n");
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert!(child.exists(), "the kept file's child was deleted:\n{out}");
    assert_eq!(fingerprint(&other), other_before);
}

/// `merge -o` must not change the ledger it was made from: a glob in FILE
/// that matches the output path would count every directive twice.
#[test]
fn merge_output_into_a_globbed_directory_is_refused() {
    let dir = tmp();
    let root = write(
        dir.path(),
        "main.beancount",
        "include \"parts/*.beancount\"\n",
    );
    write(
        dir.path(),
        "parts/a.beancount",
        "2020-01-01 open Assets:Cash\n2020-01-01 open Income:X\n\
         2020-02-01 * \"x\"\n  Assets:Cash  1 USD\n  Income:X\n",
    );
    let before = snapshot(dir.path());
    let mut args = merge_args(&root);
    args.output = Some(dir.path().join("parts/merged.beancount"));
    let (code, out, err) = run_merge(&args);
    assert_eq!(code, ExitCode::from(1), "{out}{err}");
    assert!(
        err.contains("would change once the output file exists"),
        "{err}"
    );
    assert_eq!(snapshot(dir.path()), before);
}

/// The merged file is no more readable than the most private file in it.
#[cfg(unix)]
#[test]
fn merged_file_takes_the_strictest_permissions() {
    use std::os::unix::fs::PermissionsExt;
    let mode = |p: &Path| fs::metadata(p).unwrap().permissions().mode() & 0o777;
    let dir = tmp();
    let root = write(
        dir.path(),
        "main.beancount",
        "include \"secret.beancount\"\n",
    );
    let secret = write(
        dir.path(),
        "secret.beancount",
        "2020-01-01 open Assets:Bank\n",
    );
    fs::set_permissions(&root, fs::Permissions::from_mode(0o644)).unwrap();
    fs::set_permissions(&secret, fs::Permissions::from_mode(0o600)).unwrap();
    let out_path = dir.path().join("o.beancount");
    let mut args = merge_args(&root);
    args.output = Some(out_path.clone());
    let (code, out, err) = run_merge(&args);
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(mode(&out_path), 0o600);
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(mode(&root), 0o600);
}

/// Narrowing read access never takes away write access: merging a read-only
/// archived year must not make the root read-only.
#[cfg(unix)]
#[test]
fn merging_a_read_only_file_keeps_the_root_writable() {
    use std::os::unix::fs::PermissionsExt;
    let mode = |p: &Path| fs::metadata(p).unwrap().permissions().mode() & 0o777;
    let dir = tmp();
    let root = write(dir.path(), "main.beancount", "include \"2019.beancount\"\n");
    let year = write(dir.path(), "2019.beancount", "2019-01-01 open Assets:C\n");
    fs::set_permissions(&root, fs::Permissions::from_mode(0o644)).unwrap();
    fs::set_permissions(&year, fs::Permissions::from_mode(0o444)).unwrap();
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(mode(&root), 0o644);
}

/// New and backup files keep the original's group, and a merged file loses
/// group read access when a merged file belongs to another group. Needs a
/// second group to move files into; skipped (with a note) where the user has
/// only one.
#[cfg(unix)]
#[test]
fn group_ownership_carries_over() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let out = std::process::Command::new("id").arg("-G").output().unwrap();
    let groups: Vec<u32> = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .filter_map(|g| g.parse().ok())
        .collect();
    let dir = tmp();
    let probe = write(dir.path(), "probe", "");
    let mine = fs::metadata(&probe).unwrap().gid();
    let Some(&other) = groups.iter().find(|&&g| g != mine) else {
        eprintln!("Skipping group_ownership_carries_over: only one group");
        return;
    };
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    std::os::unix::fs::chown(&file, None, Some(other)).unwrap();
    fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
    let (code, _, err) = run_split(&split_args(&file, Period::Year));
    assert_eq!(code, ExitCode::SUCCESS, "{err}");
    let gid = |p: &Path| fs::metadata(p).unwrap().gid();
    assert_eq!(gid(&file), other);
    assert_eq!(gid(&dir.path().join("ledger/2023.beancount")), other);
    let backup = fs::read_dir(dir.path().join(".rledger-backup"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    assert_eq!(gid(&backup.join("ledger.beancount.bak")), other);

    // Merge a file of the user's own group into a root of `other`: the
    // merged file keeps `other` but may not grant it the included content.
    let dir = tmp();
    let root = write(dir.path(), "main.beancount", "include \"a.beancount\"\n");
    let a = write(dir.path(), "a.beancount", "2020-01-01 open Assets:Bank\n");
    std::os::unix::fs::chown(&root, None, Some(other)).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o640)).unwrap();
    fs::set_permissions(&a, fs::Permissions::from_mode(0o640)).unwrap();
    let (code, out, err) = run_merge(&merge_args(&root));
    assert_eq!(code, ExitCode::SUCCESS, "{out}{err}");
    assert_eq!(gid(&root), other);
    assert_eq!(
        fs::metadata(&root).unwrap().permissions().mode() & 0o777,
        0o600
    );
}

/// A ledger whose two loads differ is refused: `unstable` reports any
/// difference between `before` and a fresh load. Simulated by changing the
/// file between the two loads, which is what a varying plugin looks like.
#[test]
fn a_ledger_that_loads_differently_twice_is_refused() {
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", LEDGER);
    let before = super::load_before(&file).unwrap();
    assert_eq!(super::unstable(&file, &before).unwrap(), None);
    fs::write(&file, LEDGER.replace("\"Lunch\"", "\"Brunch\"")).unwrap();
    let reason = super::unstable(&file, &before).unwrap();
    assert!(
        reason
            .as_deref()
            .is_some_and(|r| r.starts_with("The ledger does not load the same way twice")),
        "{reason:?}"
    );
}

/// A restore after a failed verification gives the file back its group.
#[cfg(unix)]
#[test]
fn restore_keeps_the_group() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let out = std::process::Command::new("id").arg("-G").output().unwrap();
    let groups: Vec<u32> = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .filter_map(|g| g.parse().ok())
        .collect();
    let dir = tmp();
    let file = write(dir.path(), "ledger.beancount", "; original\n");
    let mine = fs::metadata(&file).unwrap().gid();
    let Some(&other) = groups.iter().find(|&&g| g != mine) else {
        eprintln!("Skipping restore_keeps_the_group: only one group");
        return;
    };
    std::os::unix::fs::chown(&file, None, Some(other)).unwrap();
    fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
    let plan = swap::Plan {
        writes: vec![(file.clone(), "; replaced\n".to_string())],
        commit: file.clone(),
        removes: Vec::new(),
        backup_base: dir.path().canonicalize().unwrap(),
        originals: vec![(file.clone(), b"; original\n".to_vec())],
        operation: "split",
        template: file.clone(),
        mode_mask: None,
    };
    swap::apply(&plan, || anyhow::bail!("simulated mismatch")).unwrap_err();
    assert_eq!(fs::read_to_string(&file).unwrap(), "; original\n");
    let meta = fs::metadata(&file).unwrap();
    assert_eq!(meta.gid(), other);
    assert_eq!(meta.permissions().mode() & 0o777, 0o640);
}
