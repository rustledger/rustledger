//! Drift guard for the agent skill in `skills/rledger/` (issue #3009).
//!
//! The skill teaches agents how to drive `rledger`, so a renamed command or
//! flag that the skill still names would mislead every agent that loads it.
//! These tests read the skill's Markdown and check it against the real binary
//! (its `--help` output, which clap generates from the definitions), so the
//! rename fails CI instead:
//!
//! - every `rledger <command> [<subcommand>]` written in a code span or a code
//!   block names a command that exists, and each `--flag`/`-f` in it is one that
//!   command (or a parent) accepts;
//! - every flag listed in a table under a command's section of
//!   `references/commands.md` exists on that command or one of its subcommands;
//! - every top-level command is mentioned, so a new command gets documented;
//! - the ledger marked `skill-test: check-clean` passes `check` and is
//!   formatted;
//! - the frontmatter is valid and every relative link resolves.
//!
//! The binary is `CARGO_BIN_EXE_rledger`, always built for this package's
//! integration tests, so nothing here can skip silently.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

fn rledger() -> Command {
    Command::new(env!("CARGO_BIN_EXE_rledger"))
}

fn skill_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../skills/rledger")
}

/// `SKILL.md` and every `references/*.md`, as (path relative to the skill, text).
fn skill_files() -> Vec<(String, String)> {
    let dir = skill_dir();
    let mut paths = vec![dir.join("SKILL.md")];
    let mut refs: Vec<PathBuf> = std::fs::read_dir(dir.join("references"))
        .expect("skills/rledger/references exists")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "md"))
        .collect();
    refs.sort();
    paths.extend(refs);
    paths
        .into_iter()
        .map(|p| {
            let text =
                std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            let rel = p
                .strip_prefix(&dir)
                .expect("under the skill dir")
                .to_string_lossy()
                .into_owned();
            (rel, text)
        })
        .collect()
}

/// `rledger <path...> --help`, cached; `None` when the path is not a command.
struct Help(BTreeMap<Vec<String>, Option<String>>);

impl Help {
    const fn new() -> Self {
        Self(BTreeMap::new())
    }

    fn get(&mut self, path: &[String]) -> Option<String> {
        self.0
            .entry(path.to_vec())
            .or_insert_with(|| {
                let out = rledger()
                    .args(path)
                    .arg("--help")
                    .output()
                    .expect("run rledger --help");
                out.status
                    .success()
                    .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
            })
            .clone()
    }

    /// The subcommands listed under `Commands:` (without clap's `help`).
    fn subcommands(&mut self, path: &[String]) -> Vec<String> {
        let Some(help) = self.get(path) else {
            return Vec::new();
        };
        help.lines()
            .skip_while(|l| l.trim() != "Commands:")
            .skip(1)
            .take_while(|l| !l.trim().is_empty())
            .filter_map(|l| l.split_whitespace().next())
            .filter(|name| *name != "help")
            .map(str::to_owned)
            .collect()
    }
}

/// Whether `help` documents `flag` (`--long` or `-s`).
fn help_has_flag(help: &str, flag: &str) -> bool {
    help.match_indices(flag).any(|(i, _)| {
        let before = help[..i].chars().next_back();
        let after = help[i + flag.len()..].chars().next();
        let starts = before.is_none_or(|c| c.is_whitespace() || c == '[' || c == '`');
        let ends = after.is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'));
        starts && ends
    })
}

/// A shell-ish word: its text, and whether it was quoted.
struct Word {
    text: String,
    quoted: bool,
}

/// Split one command line into words, stopping at a pipe, redirect, `;`,
/// `&&` or comment, which end the `rledger` invocation.
fn shell_words(line: &str) -> Vec<Word> {
    let mut words = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    let mut in_word = false;
    let mut chars = line.chars();
    while let Some(c) = chars.next() {
        match c {
            '\'' | '"' => {
                in_word = true;
                quoted = true;
                for q in chars.by_ref() {
                    if q == c {
                        break;
                    }
                    cur.push(q);
                }
            }
            c if c.is_whitespace() => {
                if in_word {
                    words.push(Word {
                        text: std::mem::take(&mut cur),
                        quoted,
                    });
                    in_word = false;
                    quoted = false;
                }
            }
            '|' | ';' | '&' | '>' | '<' if !in_word => break,
            '#' if !in_word => break,
            c => {
                in_word = true;
                cur.push(c);
            }
        }
    }
    if in_word {
        words.push(Word { text: cur, quoted });
    }
    words
}

/// The text that is code: whole lines inside fenced blocks, and inline code
/// spans elsewhere. Returned as (1-based line number, code text).
fn code_fragments(text: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut fenced = false;
    for (i, line) in text.lines().enumerate() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced {
            out.push((i + 1, line.to_owned()));
        } else {
            for (j, span) in line.split('`').enumerate() {
                if j % 2 == 1 {
                    out.push((i + 1, span.to_owned()));
                }
            }
        }
    }
    out
}

/// Every `rledger ...` invocation in a code fragment: its words after
/// `rledger`. `ag-rledger` and `rledger-lsp` are other binaries.
fn invocations(fragment: &str) -> Vec<Vec<Word>> {
    let mut out = Vec::new();
    for (i, _) in fragment.match_indices("rledger ") {
        let before = fragment[..i].chars().next_back();
        if before.is_some_and(|c| c.is_alphanumeric() || matches!(c, '-' | '_' | '/' | '.')) {
            continue;
        }
        out.push(shell_words(&fragment[i + "rledger ".len()..]));
    }
    out
}

fn is_flag(word: &Word) -> bool {
    let t = &word.text;
    !word.quoted
        && t.starts_with('-')
        && t.len() > 1
        && t != "--"
        && !t[1..].starts_with(|c: char| c.is_ascii_digit())
}

fn flag_name(text: &str) -> &str {
    text.split('=').next().unwrap_or(text)
}

/// A word that stands for an argument (`<FILE>`, `[OPTIONS]`, `...`).
fn is_placeholder(word: &Word) -> bool {
    !word.quoted && (word.text.starts_with(['<', '[']) || word.text.contains("..."))
}

#[test]
fn test_skill_invocations_name_real_commands_and_flags() {
    let mut help = Help::new();
    let mut problems = Vec::new();
    let mut checked = 0usize;
    for (file, text) in skill_files() {
        for (line, fragment) in code_fragments(&text) {
            for words in invocations(&fragment) {
                let mut path: Vec<String> = Vec::new();
                let mut flags: Vec<String> = Vec::new();
                for word in &words {
                    if is_flag(word) {
                        flags.push(flag_name(&word.text).to_owned());
                    } else if word.quoted || is_placeholder(word) {
                        // an argument value
                    } else if help.subcommands(&path).contains(&word.text) {
                        path.push(word.text.clone());
                    } else if path.is_empty() {
                        problems.push(format!(
                            "{file}:{line}: `{}`: rledger has no command `{}`",
                            fragment.trim(),
                            word.text
                        ));
                        break;
                    }
                    // otherwise a positional argument (FILE, a report's FILE
                    // before its name, a value)
                }
                checked += 1;
                // A flag may belong to the command or any parent (globals, and
                // `report`'s options written before the report name).
                let helps: Vec<String> = (0..=path.len())
                    .filter_map(|n| help.get(&path[..n]))
                    .collect();
                for flag in flags {
                    if !helps.iter().any(|h| help_has_flag(h, &flag)) {
                        problems.push(format!(
                            "{file}:{line}: `rledger {}` has no flag `{flag}`",
                            path.join(" ")
                        ));
                    }
                }
            }
        }
    }
    assert!(
        checked >= 50,
        "only {checked} `rledger` invocations found in the skill; is the parser broken?"
    );
    assert!(
        problems.is_empty(),
        "the skill names commands or flags rledger does not have:\n{}",
        problems.join("\n")
    );
}

/// Flags listed in the tables of `references/commands.md`, checked against the
/// command whose `## <command>` section holds them, or its subcommands.
#[test]
fn test_skill_command_tables_list_real_flags() {
    let text = std::fs::read_to_string(skill_dir().join("references/commands.md"))
        .expect("read references/commands.md");
    let mut help = Help::new();
    let top = help.subcommands(&[]);
    let mut section: Option<Vec<String>> = None;
    let mut problems = Vec::new();
    let mut checked = 0usize;
    for (i, line) in text.lines().enumerate() {
        if let Some(heading) = line.strip_prefix("## ") {
            let name = heading.trim().to_lowercase();
            section = if name == "global flags" {
                Some(Vec::new())
            } else if top.contains(&name) {
                Some(vec![name])
            } else {
                None
            };
            continue;
        }
        let Some(path) = &section else { continue };
        if !line.starts_with('|') {
            continue;
        }
        // The command's help and every subcommand's.
        let mut helps = vec![help.get(path).expect("section command has help")];
        for sub in help.subcommands(path) {
            let mut p = path.clone();
            p.push(sub);
            helps.extend(help.get(&p));
        }
        for (j, span) in line.split('`').enumerate() {
            if j % 2 == 0 {
                continue;
            }
            for raw in span.split([',', ' ']) {
                let word = Word {
                    text: raw.trim().to_owned(),
                    quoted: false,
                };
                if !is_flag(&word) {
                    continue;
                }
                let flag = flag_name(&word.text);
                checked += 1;
                if !helps.iter().any(|h| help_has_flag(h, flag)) {
                    problems.push(format!(
                        "references/commands.md:{}: `rledger {}` has no flag `{flag}`",
                        i + 1,
                        path.join(" ")
                    ));
                }
            }
        }
    }
    assert!(
        checked >= 40,
        "only {checked} flags found in the command tables; is the parser broken?"
    );
    assert!(
        problems.is_empty(),
        "references/commands.md lists flags rledger does not have:\n{}",
        problems.join("\n")
    );
}

#[test]
fn test_skill_mentions_every_top_level_command() {
    let mut help = Help::new();
    let mut mentioned = BTreeSet::new();
    for (_, text) in skill_files() {
        for (_, fragment) in code_fragments(&text) {
            for words in invocations(&fragment) {
                if let Some(first) = words.first() {
                    mentioned.insert(first.text.clone());
                }
            }
        }
    }
    let missing: Vec<String> = help
        .subcommands(&[])
        .into_iter()
        .filter(|c| !mentioned.contains(c))
        .collect();
    assert!(
        missing.is_empty(),
        "rledger commands the skill never mentions (add them to \
         skills/rledger/references/commands.md): {missing:?}"
    );
}

#[test]
fn test_skill_sample_ledger_checks_clean_and_is_formatted() {
    const MARKER: &str = "<!-- skill-test: check-clean -->";
    let mut samples = Vec::new();
    for (file, text) in skill_files() {
        let mut rest = text.as_str();
        while let Some(at) = rest.find(MARKER) {
            rest = &rest[at + MARKER.len()..];
            let open = rest
                .find("```beancount\n")
                .unwrap_or_else(|| panic!("{file}: {MARKER} not followed by a beancount block"));
            let body = &rest[open + "```beancount\n".len()..];
            let close = body.find("\n```").expect("closed code block");
            samples.push((file.clone(), body[..=close].to_owned()));
            rest = &body[close..];
        }
    }
    assert!(!samples.is_empty(), "no {MARKER} sample in the skill");

    for (file, source) in samples {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("sample.beancount");
        std::fs::write(&path, &source).expect("write sample");

        let out = rledger()
            .args(["check", "--no-cache", "--format", "json"])
            .arg(&path)
            .output()
            .expect("run rledger check");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let value: serde_json::Value = serde_json::from_str(&stdout)
            .unwrap_or_else(|e| panic!("{file}: check JSON: {e}\n{stdout}"));
        assert!(
            out.status.success() && value["error_count"] == 0 && value["warning_count"] == 0,
            "{file}: the check-clean sample has diagnostics:\n{stdout}"
        );

        let out = rledger()
            .args(["format", "--no-ledger", "--check", "--diff"])
            .arg(&path)
            .output()
            .expect("run rledger format");
        assert!(
            out.status.success(),
            "{file}: the check-clean sample is not formatted:\n{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn test_skill_frontmatter_and_links() {
    let dir = skill_dir();
    let skill = std::fs::read_to_string(dir.join("SKILL.md")).expect("read SKILL.md");
    let front = skill
        .strip_prefix("---\n")
        .and_then(|s| s.split_once("\n---\n"))
        .map(|(f, _)| f)
        .expect("SKILL.md starts with a --- frontmatter block");
    let field = |key: &str| {
        front
            .lines()
            .find_map(|l| Some(l.strip_prefix(key)?.strip_prefix(':')?.trim()))
            .unwrap_or_else(|| panic!("frontmatter has no `{key}`"))
    };
    let name = field("name");
    assert_eq!(name, "rledger", "frontmatter name");
    assert_eq!(
        dir.file_name().and_then(|n| n.to_str()),
        Some(name),
        "the skill's directory must be named after it"
    );
    let description = field("description");
    assert!(
        !description.is_empty() && description.len() <= 1024,
        "description must be 1-1024 characters, is {}",
        description.len()
    );
    assert!(
        skill.lines().count() < 300,
        "keep SKILL.md short; move detail into references/"
    );

    // Relative Markdown links must resolve inside the skill, since the skill
    // is copied out of the repository on its own.
    let mut broken = Vec::new();
    for (file, text) in skill_files() {
        let base = dir.join(&file);
        let base = base.parent().expect("file has a parent");
        for (i, _) in text.match_indices("](") {
            let target = &text[i + 2..];
            let Some(end) = target.find(')') else {
                continue;
            };
            let target = &target[..end];
            if target.starts_with("http") || target.starts_with('#') {
                continue;
            }
            let path = target.split('#').next().unwrap_or(target);
            if !base.join(path).exists() {
                broken.push(format!("{file}: {target}"));
            }
        }
    }
    assert!(broken.is_empty(), "broken relative links: {broken:?}");
}
