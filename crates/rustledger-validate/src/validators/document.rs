//! Document and note validation.

use rustc_hash::FxHashMap;
use rustledger_core::{Document, Note};

use super::helpers::push_unknown_account;
use crate::LedgerState;
use crate::error::{ErrorCode, ValidationError};

/// Validate a Note directive.
///
/// Checks that the referenced account has been opened.
pub fn validate_note(state: &LedgerState, note: &Note, errors: &mut Vec<ValidationError>) {
    // Check account exists
    if !state.accounts.contains_key(&note.account) {
        push_unknown_account(
            state,
            &note.account,
            note.date,
            || format!("Invalid reference to unknown account '{}'", note.account),
            errors,
        );
    }
}

/// Validate a Document directive.
///
/// When `options.check_documents` is enabled, the referenced file must exist.
/// A relative path resolves against the directive's own source file, or
/// `options.document_base` when set; see `resolve_document_path` in `lib.rs`.
/// `option "documents"` roots are not consulted, as in beancount (#2650); a
/// file found under one only adds a hint to the error.
///
/// The `exists_cache` is consulted instead of calling `Path::exists()`
/// directly. The caller (see `build_document_exists_cache` in `lib.rs`)
/// resolves each unique `(doc.path, file_id)` once via the same rule, with rayon parallelism across Documents. The cache is empty
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
        push_unknown_account(
            state,
            &doc.account,
            doc.date,
            || format!("Invalid reference to unknown account '{}'", doc.account),
            errors,
        );
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
            // The context names the one path we looked at, or says there was
            // none to look at.
            let context = crate::resolve_document_path(&doc.path, file_id, &state.options)
                .map_or_else(
                    || "relative path, and no source file to resolve it against".to_string(),
                    |resolved| format!("resolved path: {}", resolved.display()),
                );
            let mut error = ValidationError::new(
                ErrorCode::DocumentNotFound,
                format!("Document file not found: {}", doc.path),
                doc.date,
            )
            .with_context(context);
            if let Some(hint) = crate::document_hint(&doc.path, file_id, &state.options) {
                error = error.with_hint(hint);
            }
            errors.push(error);
        }
    }
}
