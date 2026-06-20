//! Document and note validation.

use rustc_hash::FxHashMap;
use rustledger_core::{Document, Note};
use std::path::Path;

use crate::LedgerState;
use crate::error::{ErrorCode, ValidationError};

/// Validate a Note directive.
///
/// Checks that the referenced account has been opened.
pub fn validate_note(state: &LedgerState, note: &Note, errors: &mut Vec<ValidationError>) {
    // Check account exists
    if !state.accounts.contains_key(&note.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Invalid reference to unknown account '{}'", note.account),
            note.date,
        ));
    }
}

/// Validate a Document directive.
///
/// When `options.check_documents` is enabled, the referenced file must exist.
/// Relative paths are resolved in this order:
///
/// 1. Absolute path: used as-is.
/// 2. `options.document_base`: joined with the document path.
/// 3. `options.document_dirs`: tried in order; first existing match wins.
/// 4. Fallback: resolved against the directive's own source-file directory
///    (`file_id` → `options.document_source_dirs`), matching Beancount and
///    `include`. When the source directory is unknown (unspanned directive or
///    no source map) it falls back to the process CWD.
///
/// `document_base` takes precedence over `document_dirs` because it
/// represents an explicit base set by the caller (e.g. the main ledger
/// directory), whereas `document_dirs` is a search path derived from
/// `option "documents"` declarations.
///
/// The `exists_cache` is consulted instead of calling `Path::exists()`
/// directly. The caller (see `build_document_exists_cache` in `lib.rs`)
/// resolves each unique `(doc.path, file_id)` once via the same priority chain
/// above, with rayon parallelism across Documents. The cache is empty
/// when `check_documents` is disabled — fine, because the lookups in
/// this function are gated by the same flag.
pub fn validate_document(
    state: &LedgerState,
    doc: &Document,
    file_id: Option<u16>,
    exists_cache: &FxHashMap<(&str, Option<u16>), bool>,
    errors: &mut Vec<ValidationError>,
) {
    // Check account exists
    if !state.accounts.contains_key(&doc.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Invalid reference to unknown account '{}'", doc.account),
            doc.date,
        ));
    }

    // Check if document file exists (if enabled)
    if state.options.check_documents {
        // Cache should have an entry for every Document we encounter
        // because both walk the same `directives` slice. A miss would
        // indicate a divergence bug between the pre-pass and this
        // function. In release builds, a miss falls back to a fresh
        // syscall — correct behavior either way, just slower.
        let file_was_found = exists_cache
            .get(&(doc.path.as_str(), file_id))
            .copied()
            .unwrap_or_else(|| {
                debug_assert!(
                    false,
                    "Document (path `{}`, file_id {file_id:?}) missing from pre-resolved \
                     exists_cache — build_document_exists_cache enumeration must match this \
                     validator's resolution",
                    doc.path
                );
                // Defensive fallback: redo the resolution via the shared chain.
                crate::document_file_exists(&doc.path, file_id, &state.options)
            });

        if !file_was_found {
            let doc_path = Path::new(&doc.path);
            let mut error = ValidationError::new(
                ErrorCode::DocumentNotFound,
                format!("Document file not found: {}", doc.path),
                doc.date,
            );

            // The error-context message mirrors the resolution chain so the
            // user sees where we actually looked.
            if doc_path.is_relative()
                && state.options.document_base.is_none()
                && !state.options.document_dirs.is_empty()
            {
                let searched: Vec<String> = state
                    .options
                    .document_dirs
                    .iter()
                    .map(|d| d.join(doc_path).display().to_string())
                    .collect();
                error = error.with_context(format!("searched: {}", searched.join(", ")));
            } else {
                // Reconstruct the single resolved path: absolute as-is,
                // document_base join, else the directive's source-file dir
                // (the same fallback `document_file_exists` uses).
                let source_dir =
                    file_id.and_then(|id| state.options.document_source_dirs.get(id as usize));
                let resolved = if doc_path.is_absolute() {
                    doc_path.to_path_buf()
                } else if let Some(base) = &state.options.document_base {
                    base.join(doc_path)
                } else if let Some(dir) = source_dir {
                    dir.join(doc_path)
                } else {
                    doc_path.to_path_buf()
                };
                error = error.with_context(format!("resolved path: {}", resolved.display()));
            }

            errors.push(error);
        }
    }
}
