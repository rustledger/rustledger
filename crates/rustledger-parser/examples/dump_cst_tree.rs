//! Dump the CST tree of a small Beancount file as nested
//! kind+range pairs for diagnostic purposes.

#![allow(clippy::missing_panics_doc, clippy::print_stdout)]

use rustledger_parser::cst::ast::{AstNode, SourceFile};

fn dump(node: &rustledger_parser::SyntaxNode, depth: usize) {
    let r = node.text_range();
    println!(
        "{:indent$}NODE {:?} {:?}",
        "",
        node.kind(),
        r,
        indent = depth * 2
    );
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(t) => {
                let tr = t.text_range();
                let text = {
                    let full = t.text();
                    if full.len() > 30 {
                        let boundary = full
                            .char_indices()
                            .map(|(i, _)| i)
                            .take_while(|i| *i <= 30)
                            .last()
                            .unwrap_or(0);
                        format!("{:?}...", &full[..boundary])
                    } else {
                        format!("{full:?}")
                    }
                };
                println!(
                    "{:indent$}  TOK {:?} {:?} {}",
                    "",
                    t.kind(),
                    tr,
                    text,
                    indent = depth * 2
                );
            }
            rowan::NodeOrToken::Node(n) => dump(&n, depth + 1),
        }
    }
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: dump_cst_tree <path>");
    let src = std::fs::read_to_string(&path).expect("read source");
    let sf = SourceFile::parse(&src);
    dump(sf.syntax(), 0);
}
