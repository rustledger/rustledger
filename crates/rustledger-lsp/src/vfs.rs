//! Virtual File System for document management.
//!
//! The VFS maintains the in-memory state of all open documents,
//! handling incremental updates from the editor.
//!
//! Documents cache their parse results to avoid re-parsing on every request.

use ropey::Rope;
use rustledger_parser::{ParseResult, parse};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// A document in the virtual file system.
#[derive(Debug)]
pub struct Document {
    /// The document content as a rope for efficient editing.
    content: Rope,
    /// The document version (incremented on each change).
    version: i32,
    /// Cached parse result (lazily computed, invalidated on change).
    parse_cache: Option<Arc<ParseResult>>,
    /// The latest parse of this buffer that had no parse error, if it has had
    /// one since it was opened. Kept across edits (unlike `parse_cache`) and
    /// dropped with the document on close: it is what the buffer contributes
    /// to the view other files are validated against while its current text
    /// is broken (see `MainLoopState::publish_diagnostics`).
    last_clean_parse: Option<Arc<ParseResult>>,
}

impl Document {
    /// Create a new document with the given content.
    pub fn new(content: String, version: i32) -> Self {
        Self {
            content: Rope::from_str(&content),
            version,
            parse_cache: None,
            last_clean_parse: None,
        }
    }

    /// Get the document content as a string.
    pub fn text(&self) -> String {
        self.content.to_string()
    }

    /// Get the document version.
    pub fn version(&self) -> i32 {
        self.version
    }

    /// Get or compute the parse result (cached).
    pub fn parse_result(&mut self) -> Arc<ParseResult> {
        if self.parse_cache.is_none() {
            let text = self.content.to_string();
            let parsed = Arc::new(parse(&text));
            if parsed.errors.is_empty() {
                self.last_clean_parse = Some(Arc::clone(&parsed));
            }
            self.parse_cache = Some(parsed);
        }
        self.parse_cache.clone().unwrap()
    }

    /// What this buffer contributes to the clean view: its current parse if
    /// that has no error, else the latest one that had none, else `None` (the
    /// buffer has not parsed cleanly since it was opened).
    pub fn clean_view_parse(&mut self) -> Option<Arc<ParseResult>> {
        let current = self.parse_result();
        if current.errors.is_empty() {
            Some(current)
        } else {
            self.last_clean_parse.clone()
        }
    }

    /// Invalidate the parse cache (called on content change).
    fn invalidate_cache(&mut self) {
        self.parse_cache = None;
    }

    /// Update the document content.
    pub fn update(&mut self, content: String, version: i32) {
        self.content = Rope::from_str(&content);
        self.version = version;
        self.invalidate_cache();
    }
}

/// Virtual file system for managing open documents.
#[derive(Debug, Default)]
pub struct Vfs {
    /// Open documents indexed by path.
    documents: HashMap<PathBuf, Document>,
}

impl Vfs {
    /// Create a new empty VFS.
    pub fn new() -> Self {
        Self::default()
    }

    /// Open a document in the VFS.
    pub fn open(&mut self, path: PathBuf, content: String, version: i32) {
        self.documents.insert(path, Document::new(content, version));
    }

    /// Close a document in the VFS.
    pub fn close(&mut self, path: &Path) {
        self.documents.remove(path);
    }

    /// Get a document by path (immutable).
    pub fn get(&self, path: &Path) -> Option<&Document> {
        self.documents.get(path)
    }

    /// Get a document by path (mutable, for parse caching).
    pub fn get_mut(&mut self, path: &Path) -> Option<&mut Document> {
        self.documents.get_mut(path)
    }

    /// Get document content as a string.
    pub fn get_content(&self, path: &Path) -> Option<String> {
        self.documents.get(path).map(|d| d.text())
    }

    /// Get document content and cached parse result.
    /// This is the preferred method for request handlers.
    pub fn get_document_data(&mut self, path: &Path) -> Option<(String, Arc<ParseResult>)> {
        self.documents.get_mut(path).map(|doc| {
            let text = doc.text();
            let parse_result = doc.parse_result();
            (text, parse_result)
        })
    }

    /// Update a document's content.
    pub fn update(&mut self, path: &Path, content: String, version: i32) {
        if let Some(doc) = self.documents.get_mut(path) {
            doc.update(content, version);
        }
    }

    /// Get all open document paths.
    pub fn paths(&self) -> impl Iterator<Item = &PathBuf> {
        self.documents.keys()
    }

    /// Iterate over all open documents (path and content).
    pub fn iter(&self) -> impl Iterator<Item = (&PathBuf, String)> {
        self.documents.iter().map(|(path, doc)| (path, doc.text()))
    }

    /// Every open document that has a clean-view parse (see
    /// `Document::clean_view_parse`), with that parse.
    pub fn iter_clean_view_parses(&mut self) -> impl Iterator<Item = (&PathBuf, Arc<ParseResult>)> {
        self.documents
            .iter_mut()
            .filter_map(|(path, doc)| Some((path, doc.clean_view_parse()?)))
    }

    /// Iterate over all open documents with parse results.
    pub fn iter_with_parse(
        &mut self,
    ) -> impl Iterator<Item = (&PathBuf, String, Arc<ParseResult>)> {
        self.documents.iter_mut().map(|(path, doc)| {
            let text = doc.text();
            let parse_result = doc.parse_result();
            (path, text, parse_result)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vfs_open_close() {
        let mut vfs = Vfs::new();
        let path = PathBuf::from("/test.beancount");

        vfs.open(path.clone(), "2024-01-01 open Assets:Bank".to_string(), 1);
        assert!(vfs.get(&path).is_some());

        vfs.close(&path);
        assert!(vfs.get(&path).is_none());
    }

    #[test]
    fn test_document_text() {
        let doc = Document::new("hello world".to_string(), 1);
        assert_eq!(doc.text(), "hello world");
    }

    #[test]
    fn test_clean_view_parse_keeps_the_last_clean_parse_until_close() {
        let mut vfs = Vfs::new();
        let path = PathBuf::from("/test.beancount");
        let clean_view = |vfs: &mut Vfs| {
            vfs.get_mut(&path)
                .and_then(Document::clean_view_parse)
                .map(|p| p.directives.len())
        };

        // Broken since open: nothing to contribute.
        vfs.open(path.clone(), "garbage\n".to_string(), 1);
        assert_eq!(clean_view(&mut vfs), None);

        vfs.update(&path, "2024-01-01 open Assets:A\n".to_string(), 2);
        assert_eq!(clean_view(&mut vfs), Some(1));

        // Broken again: the last clean parse stands in for it.
        vfs.update(&path, "2024-01-01 open Assets:A\ngarbage\n".to_string(), 3);
        assert_eq!(clean_view(&mut vfs), Some(1));

        // A newer clean parse replaces it.
        vfs.update(
            &path,
            "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n".to_string(),
            4,
        );
        assert_eq!(clean_view(&mut vfs), Some(2));

        // Closing drops it with the document.
        vfs.close(&path);
        vfs.open(path.clone(), "garbage\n".to_string(), 5);
        assert_eq!(clean_view(&mut vfs), None);
    }
}
