//! JSON-RPC 2.0 protocol implementation.
//!
//! This module provides JSON-RPC 2.0 support for the FFI-WASI interface.
//!
//! # Protocol
//!
//! JSON-RPC 2.0 requests are received via stdin as JSON objects or arrays (for batch):
//!
//! ```json
//! {"jsonrpc":"2.0","method":"ledger.load","params":{"source":"..."},"id":1}
//! ```
//!
//! Responses are written to stdout as JSON-RPC 2.0 response objects.
//!
//! # Methods
//!
//! ## Ledger Operations
//! - `ledger.load` - Load beancount source from string
//! - `ledger.loadFile` - Load beancount file from path
//! - `ledger.validate` - Validate beancount source
//! - `ledger.validateFile` - Validate beancount file
//!
//! ## Query Operations
//! - `query.execute` - Execute a BQL query on source
//! - `query.executeFile` - Execute a BQL query on file
//! - `query.batch` - Execute multiple queries on source
//! - `query.batchFile` - Execute multiple queries on file
//!
//! ## Format Operations
//! - `format.source` - Format beancount source
//! - `format.file` - Format beancount file
//! - `format.entry` - Format a single entry from JSON
//! - `format.entries` - Format multiple entries from JSON
//!
//! ## Entry Operations
//! - `entry.create` - Create an entry from JSON
//! - `entry.createBatch` - Create multiple entries from JSON
//! - `entry.filter` - Filter entries by date range
//! - `entry.clamp` - Clamp entries to date range
//!
//! ## Utility Operations
//! - `util.version` - Get API and package version
//! - `util.types` - Get directive types, booking methods, and account types
//! - `util.isEncrypted` - Check if file is encrypted
//! - `util.getAccountType` - Get account type from name

pub mod error;
pub mod request;
pub mod response;
pub mod router;

use request::{BatchElement, RequestBatch};
use response::{Response, ResponseBatch};

use std::io::{self, Read, Write};

/// Process JSON-RPC requests from stdin and write responses to stdout.
pub fn process_stdin() -> i32 {
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        // IO failure reading the transport, NOT a JSON parse failure.
        // JSON-RPC's -32700 is reserved for "received bytes that weren't
        // valid JSON"; treating stdin read errors as that code would
        // make a JSON-RPC client retry the request endlessly. Use
        // internal_error (-32603) to signal a server-side fault.
        let response = Response::internal_error(None, format!("Failed to read stdin: {e}"));
        output_response(&ResponseBatch::single(response));
        return 1;
    }

    let response = process_request(&input);

    // Don't output anything for empty batch (all notifications)
    if response.is_empty() {
        return 0;
    }

    output_response(&response);
    0
}

/// Process a JSON-RPC request string and return a response batch.
pub fn process_request(input: &str) -> ResponseBatch {
    // Parse the request
    let batch = match RequestBatch::parse(input) {
        Ok(batch) => batch,
        Err(err) => return ResponseBatch::single(Response::error(None, err)),
    };

    // Route the request(s)
    match batch {
        RequestBatch::Single(request) => {
            // For notifications (no id), don't return a response
            if request.is_notification() {
                router::route(&request); // Process but discard response
                ResponseBatch::batch(vec![])
            } else {
                ResponseBatch::single(router::route(&request))
            }
        }
        RequestBatch::Batch(elements) => {
            let responses: Vec<Response> = elements
                .into_iter()
                .filter_map(|element| match element {
                    BatchElement::Valid(req) => {
                        if req.is_notification() {
                            router::route(&req); // Process but discard
                            None
                        } else {
                            Some(router::route(&req))
                        }
                    }
                    BatchElement::Invalid { error, id } => {
                        // Per JSON-RPC 2.0 spec, return error response for invalid elements
                        Some(Response::error(id, error))
                    }
                })
                .collect();
            ResponseBatch::batch(responses)
        }
    }
}

/// Write a response to stdout.
fn output_response(response: &ResponseBatch) {
    match serde_json::to_string(response) {
        Ok(json) => {
            let _ = writeln!(io::stdout(), "{json}");
        }
        Err(e) => {
            let err_response =
                Response::internal_error(None, format!("Failed to serialize response: {e}"));
            if let Ok(json) = serde_json::to_string(&err_response) {
                let _ = writeln!(io::stdout(), "{json}");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_version_request() {
        let input = r#"{"jsonrpc":"2.0","method":"util.version","params":{},"id":1}"#;
        let response = process_request(input);
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"result\""));
        assert!(json.contains("apiVersion"));
    }

    #[test]
    fn test_process_invalid_json() {
        let input = r"not valid json";
        let response = process_request(input);
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"error\""));
        assert!(json.contains("-32700")); // Parse error
    }

    #[test]
    fn test_process_method_not_found() {
        let input = r#"{"jsonrpc":"2.0","method":"unknown.method","params":{},"id":1}"#;
        let response = process_request(input);
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"error\""));
        assert!(json.contains("-32601")); // Method not found
    }

    #[test]
    fn test_process_batch_request() {
        let input = r#"[
            {"jsonrpc":"2.0","method":"util.version","params":{},"id":1},
            {"jsonrpc":"2.0","method":"util.version","params":{},"id":2}
        ]"#;
        let response = process_request(input);
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.starts_with('['));
        assert!(json.contains("\"id\":1"));
        assert!(json.contains("\"id\":2"));
    }

    #[test]
    fn test_notification_no_response() {
        // A notification has no id, so no response should be returned
        let input = r#"{"jsonrpc":"2.0","method":"util.version","params":{}}"#;
        let response = process_request(input);
        assert!(response.is_empty());
    }

    #[test]
    fn test_batch_with_invalid_element() {
        // Per JSON-RPC 2.0 spec, invalid elements should return per-element errors
        // without failing the entire batch
        let input = r#"[
            {"jsonrpc":"2.0","method":"util.version","id":1},
            {"invalid":"not a valid request","id":2},
            {"jsonrpc":"2.0","method":"util.version","id":3}
        ]"#;
        let response = process_request(input);
        let json = serde_json::to_string(&response).unwrap();

        // Should be an array with 3 responses
        assert!(json.starts_with('['));

        // First and third should succeed
        assert!(json.contains("\"id\":1"));
        assert!(json.contains("\"id\":3"));

        // Second should be an error with the preserved ID
        assert!(json.contains("\"id\":2"));
        assert!(json.contains("-32600")); // Invalid Request error code
    }
}
