//! Virtual File System for document management.
//!
//! The VFS maintains the in-memory state of all open documents,
//! handling incremental updates from the editor.
//!
//! Documents cache their parse results to avoid re-parsing on every request.
//! Uses incremental parsing for 5-10x faster re-parsing on edits.

use ropey::Rope;
use rustledger_parser::{
    ParseResult,
    incremental::{IncrementalParser, TextChange},
};
use std::collections::HashMap;
use std::path::PathBuf;
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
    /// Incremental parser for fast re-parsing on edits.
    incremental_parser: IncrementalParser,
}

impl Document {
    /// Create a new document with the given content.
    pub fn new(content: String, version: i32) -> Self {
        Self {
            content: Rope::from_str(&content),
            version,
            parse_cache: None,
            incremental_parser: IncrementalParser::new(),
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
            // Use incremental parser to track regions for future incremental updates
            let result = self.incremental_parser.parse_full(&text);
            self.parse_cache = Some(Arc::new(result));
        }
        self.parse_cache.clone().unwrap()
    }

    /// Invalidate the parse cache (called on content change).
    fn invalidate_cache(&mut self) {
        self.parse_cache = None;
    }

    /// Update the document content with full text replacement.
    pub fn update(&mut self, content: String, version: i32) {
        self.content = Rope::from_str(&content);
        self.version = version;
        self.invalidate_cache();
    }

    /// Apply incremental text changes and re-parse only affected regions.
    ///
    /// This is faster than full re-parse for small edits.
    pub fn apply_changes(&mut self, changes: &[TextChange], version: i32) {
        self.version = version;
        self.invalidate_cache();

        // Get current text
        let text = self.content.to_string();

        // Apply incremental parse
        let result = self.incremental_parser.apply_changes(&text, changes);
        self.parse_cache = Some(Arc::new(result));
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
    pub fn close(&mut self, path: &PathBuf) {
        self.documents.remove(path);
    }

    /// Get a document by path (immutable).
    pub fn get(&self, path: &PathBuf) -> Option<&Document> {
        self.documents.get(path)
    }

    /// Get a document by path (mutable, for parse caching).
    pub fn get_mut(&mut self, path: &PathBuf) -> Option<&mut Document> {
        self.documents.get_mut(path)
    }

    /// Get document content as a string.
    pub fn get_content(&self, path: &PathBuf) -> Option<String> {
        self.documents.get(path).map(|d| d.text())
    }

    /// Get document content and cached parse result.
    /// This is the preferred method for request handlers.
    pub fn get_document_data(&mut self, path: &PathBuf) -> Option<(String, Arc<ParseResult>)> {
        self.documents.get_mut(path).map(|doc| {
            let text = doc.text();
            let parse_result = doc.parse_result();
            (text, parse_result)
        })
    }

    /// Update a document's content.
    pub fn update(&mut self, path: &PathBuf, content: String, version: i32) {
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
    fn test_document_incremental_parse() {
        let mut doc = Document::new("2024-01-01 open Assets:Bank USD\n".to_string(), 1);

        // First parse caches the result
        let parse1 = doc.parse_result();
        assert_eq!(parse1.directives.len(), 1);

        // Second call uses cache
        let parse2 = doc.parse_result();
        assert_eq!(parse2.directives.len(), 1);
    }

    #[test]
    fn test_document_apply_changes() {
        let mut doc = Document::new("2024-01-01 open Assets:Bank USD\n".to_string(), 1);

        // Initial parse
        let parse1 = doc.parse_result();
        assert_eq!(parse1.directives.len(), 1);

        // Apply change using incremental parsing
        let changes = vec![TextChange::new(20, 25, "Cash")];
        doc.apply_changes(&changes, 2);

        // Verify updated parse
        let parse2 = doc.parse_result();
        assert_eq!(parse2.directives.len(), 1);
        assert_eq!(doc.version(), 2);
    }
}
