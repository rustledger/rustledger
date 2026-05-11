//! Document and note validation.

use rustc_hash::FxHashMap;
use rustledger_core::{Document, Note};
use std::path::{Path, PathBuf};

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
/// 4. Fallback: the path is checked as-is (relative to the process CWD).
///
/// `document_base` takes precedence over `document_dirs` because it
/// represents an explicit base set by the caller (e.g. the main ledger
/// directory), whereas `document_dirs` is a search path derived from
/// `option "documents"` declarations.
///
/// The `exists_cache` is consulted instead of calling `Path::exists()`
/// directly. The caller (see `build_document_exists_cache` in `lib.rs`)
/// pre-resolves all candidate paths in one rayon batch before the
/// main per-directive loop, so this function stays syscall-free in the
/// hot path. The cache is empty when `check_documents` is disabled —
/// also fine, because the lookups in this function are gated by the
/// same flag.
pub fn validate_document(
    state: &LedgerState,
    doc: &Document,
    exists_cache: &FxHashMap<PathBuf, bool>,
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
        let doc_path = Path::new(&doc.path);
        let lookup = |p: &Path| exists_cache.get(p).copied().unwrap_or(false);

        let mut file_was_found = false;
        let full_path = if doc_path.is_absolute() {
            file_was_found = lookup(doc_path);
            doc_path.to_path_buf()
        } else if let Some(base) = &state.options.document_base {
            let p = base.join(doc_path);
            file_was_found = lookup(&p);
            p
        } else if !state.options.document_dirs.is_empty() {
            // Try resolving relative path against each document directory
            let mut found = None;
            for dir in &state.options.document_dirs {
                let candidate = dir.join(doc_path);
                if lookup(&candidate) {
                    found = Some(candidate);
                    break;
                }
            }
            match found {
                Some(p) => {
                    file_was_found = true;
                    p
                }
                None => doc_path.to_path_buf(),
            }
        } else {
            file_was_found = lookup(doc_path);
            doc_path.to_path_buf()
        };

        if !file_was_found {
            let mut error = ValidationError::new(
                ErrorCode::DocumentNotFound,
                format!("Document file not found: {}", doc.path),
                doc.date,
            );

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
                error = error.with_context(format!("resolved path: {}", full_path.display()));
            }

            errors.push(error);
        }
    }
}
