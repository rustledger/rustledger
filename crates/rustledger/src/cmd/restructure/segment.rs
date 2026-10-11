//! Cut one source file into top-level items, losslessly.
//!
//! Built on the parser's CST, whose trivia rule is the one the issue asks for:
//! the blank lines and comments between two directives belong to the
//! directive that FOLLOWS them (the Directive-Terminator Rule in
//! `rustledger_parser::cst`). So an item's text is its preceding comments,
//! the directive exactly as written, and its terminating newline, and the
//! file is the concatenation of `leading`, every item's text, and `trailing`,
//! byte for byte. Nothing is reformatted.

use anyhow::{Result, bail};
use rustledger_core::NaiveDate;
use rustledger_parser::cst::ast::{AstNode, AstToken, Directive as Node};
use rustledger_parser::{NodeOrToken, SyntaxNode};

/// One entry on the pushtag/pushmeta stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum StackKey {
    /// `pushtag #NAME` / `poptag #NAME` (name without the `#`).
    Tag(String),
    /// `pushmeta KEY: ...` / `popmeta KEY:` (key without the colon).
    Meta(String),
}

impl StackKey {
    /// The line that pops this entry.
    pub(super) fn pop_line(&self) -> String {
        match self {
            Self::Tag(t) => format!("poptag #{t}"),
            Self::Meta(k) => format!("popmeta {k}:"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ItemKind {
    /// A directive that produces a dated entry.
    Dated(NaiveDate),
    /// An `include`, with its path as the parser read it.
    Include(String),
    /// An `option` or `plugin`: global, stays with the file it is in.
    Global,
    /// `pushtag` / `pushmeta`.
    Push(StackKey),
    /// `poptag` / `popmeta`.
    Pop(StackKey),
}

#[derive(Debug, Clone)]
pub(super) struct Item {
    pub(super) kind: ItemKind,
    /// Preceding comments and blank lines, the directive, its newline.
    pub(super) text: String,
    /// The directive alone: no preceding comments, no same-line comment, no
    /// newline. Used to repeat a `pushtag`/`pushmeta` in another file.
    pub(super) content: String,
    /// Length of the part of `text` before the directive's own line: the
    /// preceding comments and blank lines.
    pub(super) lead_len: usize,
}

#[derive(Debug)]
pub(super) struct Segmented {
    /// Text before the first directive (a BOM, a file header).
    pub(super) leading: String,
    pub(super) items: Vec<Item>,
    /// Text after the last directive.
    pub(super) trailing: String,
}

impl Segmented {
    /// The file's directives, in order, that produce dated entries.
    pub(super) fn dated_count(&self) -> usize {
        self.items
            .iter()
            .filter(|i| matches!(i.kind, ItemKind::Dated(_)))
            .count()
    }
}

/// Segment `source`. Refuses a file with parse errors: which text belongs to
/// which directive is only known for text the parser understood.
pub(super) fn segment(source: &str, path: &std::path::Path) -> Result<Segmented> {
    let parsed = rustledger_parser::parse(source);
    if let Some(e) = parsed.errors.first() {
        bail!(
            "{} has {} parse error(s) (first: {e}); fix them before restructuring",
            path.display(),
            parsed.errors.len()
        );
    }
    let mut dates = parsed.directives.iter().map(|d| d.value.date());
    let mut includes = parsed.includes.iter().map(|(p, _)| p.clone());

    let root = rustledger_parser::parse_structured(source);
    let mut leading = String::new();
    let mut items: Vec<Item> = Vec::new();
    // Text seen since the last item that belongs to the next one: stray
    // top-level trivia, and malformed-but-tolerated lines (an org-mode
    // `* Heading`, which the parser keeps as an error node without raising
    // an error).
    let mut pending = String::new();

    for child in root.children_with_tokens() {
        match child {
            NodeOrToken::Token(t) => {
                if items.is_empty() {
                    leading.push_str(t.text());
                } else {
                    pending.push_str(t.text());
                }
            }
            NodeOrToken::Node(node) => {
                let Some(directive) = Node::cast(node.clone()) else {
                    // An error node the parser did not report: keep its text
                    // with whatever follows it.
                    if items.is_empty() {
                        leading.push_str(&node.text().to_string());
                    } else {
                        pending.push_str(&node.text().to_string());
                    }
                    continue;
                };
                let kind = match &directive {
                    Node::Open(_)
                    | Node::Close(_)
                    | Node::Commodity(_)
                    | Node::Note(_)
                    | Node::Document(_)
                    | Node::Event(_)
                    | Node::Query(_)
                    | Node::Price(_)
                    | Node::Balance(_)
                    | Node::Pad(_)
                    | Node::Custom(_)
                    | Node::Transaction(_) => match dates.next() {
                        Some(d) => ItemKind::Dated(d),
                        None => bail!(
                            "internal error: {} has more dated directives than the parser produced",
                            path.display()
                        ),
                    },
                    Node::Include(_) => match includes.next() {
                        Some(p) => ItemKind::Include(p),
                        None => bail!(
                            "internal error: {} has more includes than the parser produced",
                            path.display()
                        ),
                    },
                    Node::Option(_) | Node::Plugin(_) => ItemKind::Global,
                    Node::Pushtag(d) => ItemKind::Push(StackKey::Tag(tag_name(d.tag())?)),
                    Node::Poptag(d) => ItemKind::Pop(StackKey::Tag(tag_name(d.tag())?)),
                    Node::Pushmeta(d) => ItemKind::Push(StackKey::Meta(meta_key(d.key())?)),
                    Node::Popmeta(d) => ItemKind::Pop(StackKey::Meta(meta_key(d.key())?)),
                };
                let mut text = std::mem::take(&mut pending);
                let prefix = text.len();
                text.push_str(&node.text().to_string());
                let (content, content_start) = content_text(&node);
                // Back up from the directive's first token to its line start.
                let lead_len = text[..prefix + content_start]
                    .rfind('\n')
                    .map_or(0, |nl| nl + 1);
                items.push(Item {
                    kind,
                    text,
                    content,
                    lead_len,
                });
            }
        }
    }
    if dates.next().is_some() || includes.next().is_some() {
        bail!(
            "internal error: {} produced directives the restructurer did not see",
            path.display()
        );
    }

    // A comment block written directly above the first directive (no blank
    // line between) describes that directive, not the file; it goes with it.
    // Anything above a blank line stays put as the file's header.
    if let Some(first) = items.first_mut()
        && !matches!(first.kind, ItemKind::Global | ItemKind::Include(_))
    {
        let cut = attached_comment_start(&leading);
        if cut < leading.len() {
            let attached = leading.split_off(cut);
            first.lead_len += attached.len();
            first.text.insert_str(0, &attached);
        }
    }

    Ok(Segmented {
        leading,
        items,
        trailing: pending,
    })
}

fn tag_name(tag: Option<rustledger_parser::cst::ast::Tag>) -> Result<String> {
    match tag {
        Some(t) => Ok(t.text().trim_start_matches('#').to_string()),
        None => bail!("pushtag/poptag without a tag"),
    }
}

fn meta_key(key: Option<rustledger_parser::cst::ast::MetaKey>) -> Result<String> {
    match key {
        Some(k) => Ok(k.text_without_colon().to_string()),
        None => bail!("pushmeta/popmeta without a key"),
    }
}

/// The node's text from its first to its last non-trivia token, and the
/// offset of that first token within the node's text.
fn content_text(node: &SyntaxNode) -> (String, usize) {
    let mut start = None;
    let mut end = None;
    for t in node
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
    {
        if t.kind().is_trivia() {
            continue;
        }
        let r = t.text_range();
        if start.is_none() {
            start = Some(r.start());
        }
        end = Some(r.end());
    }
    match (start, end) {
        (Some(s), Some(e)) => {
            let base = node.text_range().start();
            let text = node.text().to_string();
            let (s, e) = (usize::from(s - base), usize::from(e - base));
            (text.get(s..e).unwrap_or_default().to_string(), s)
        }
        _ => (String::new(), 0),
    }
}

/// Byte offset where the comment block that directly precedes the end of
/// `leading` starts: just after the last blank line (or the start, when there
/// is none and the whole header is one block). `leading.len()` when `leading`
/// does not end in a comment line.
fn attached_comment_start(leading: &str) -> usize {
    // Work line by line from the end.
    let mut lines: Vec<(usize, &str)> = Vec::new();
    let mut offset = 0;
    for line in leading.split_inclusive('\n') {
        lines.push((offset, line));
        offset += line.len();
    }
    let is_comment = |l: &str| {
        let t = l.trim_start_matches('\u{FEFF}').trim();
        t.starts_with(';') || t.starts_with('#') || t.starts_with('%')
    };
    let mut cut = leading.len();
    for &(off, line) in lines.iter().rev() {
        if is_comment(line) {
            cut = off;
        } else {
            break;
        }
    }
    // Never move a BOM.
    if cut == 0 && leading.starts_with('\u{FEFF}') {
        cut = '\u{FEFF}'.len_utf8();
    }
    cut
}
