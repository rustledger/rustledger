//! JSON-RPC 2.0 request types.

use serde::{Deserialize, Serialize};

/// JSON-RPC 2.0 request ID.
/// Can be a string, number, or null for notifications.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RequestId {
    /// String ID.
    String(String),
    /// Numeric ID.
    Number(i64),
    /// Null ID (for notifications that don't need a response).
    Null,
}

/// A JSON-RPC 2.0 request object.
#[derive(Debug, Clone, Deserialize)]
pub struct Request {
    /// JSON-RPC version, must be "2.0".
    pub jsonrpc: String,
    /// Method name.
    pub method: String,
    /// Method parameters (optional).
    #[serde(default)]
    pub params: serde_json::Value,
    /// Request ID (optional for notifications).
    #[serde(default)]
    pub id: Option<RequestId>,
}

impl Request {
    /// Check if this is a valid JSON-RPC 2.0 request.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.jsonrpc != "2.0" {
            return Err("jsonrpc must be \"2.0\"");
        }
        if self.method.is_empty() {
            return Err("method must not be empty");
        }
        if self.method.starts_with("rpc.") {
            return Err("method names starting with \"rpc.\" are reserved");
        }
        Ok(())
    }

    /// Check if this is a notification (no response expected).
    pub const fn is_notification(&self) -> bool {
        self.id.is_none()
    }
}

/// Result of parsing a single request in a batch.
#[derive(Debug, Clone)]
pub enum BatchElement {
    /// Successfully parsed request.
    Valid(Request),
    /// Failed to parse - contains error and optional ID if extractable.
    Invalid {
        error: super::error::RpcError,
        id: Option<RequestId>,
    },
}

/// Either a single request or a batch of requests.
#[derive(Debug, Clone)]
pub enum RequestBatch {
    /// Single request.
    Single(Request),
    /// Batch of requests (may include invalid elements with per-element errors).
    Batch(Vec<BatchElement>),
}

impl RequestBatch {
    /// Parse JSON input into a request or batch.
    pub fn parse(input: &str) -> Result<Self, super::error::RpcError> {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Err(super::error::RpcError::invalid_request(
                "Empty request body",
            ));
        }

        // Check if it's an array (batch) or object (single)
        if trimmed.starts_with('[') {
            // First parse into raw JSON values to avoid failing the entire batch
            // on a single non-conforming element (per JSON-RPC 2.0 spec).
            let raw_values: Vec<serde_json::Value> = serde_json::from_str(trimmed)
                .map_err(|e| super::error::RpcError::parse_error(format!("Invalid JSON: {e}")))?;

            if raw_values.is_empty() {
                return Err(super::error::RpcError::invalid_request(
                    "Empty batch request",
                ));
            }

            // Validate and decode each element individually, collecting errors
            let elements: Vec<BatchElement> = raw_values
                .into_iter()
                .map(|value| {
                    // Try to extract ID even if the request is invalid
                    let id = value
                        .get("id")
                        .and_then(|v| serde_json::from_value::<RequestId>(v.clone()).ok());

                    match serde_json::from_value::<Request>(value) {
                        Ok(request) => BatchElement::Valid(request),
                        Err(e) => BatchElement::Invalid {
                            error: super::error::RpcError::invalid_request(format!(
                                "Invalid request: {e}"
                            )),
                            id,
                        },
                    }
                })
                .collect();

            Ok(Self::Batch(elements))
        } else {
            let request: Request = serde_json::from_str(trimmed)
                .map_err(|e| super::error::RpcError::parse_error(format!("Invalid JSON: {e}")))?;

            Ok(Self::Single(request))
        }
    }
}

// Parameter structs for each method

/// Parameters for ledger.load method.
#[derive(Debug, Deserialize)]
pub struct LoadParams {
    /// Beancount source code.
    pub source: String,
    /// Optional filename for error messages.
    #[serde(default)]
    pub filename: Option<String>,
}

/// Parameters for ledger.loadFile method.
#[derive(Debug, Deserialize)]
pub struct LoadFileParams {
    /// Path to beancount file.
    pub path: String,
    /// Optional plugin names to apply.
    #[serde(default)]
    pub plugins: Vec<String>,
    /// Confine the include graph to the entry file's directory tree
    /// (default: `true`). Set to `false` to allow includes that
    /// reference paths outside the entry file's parent directory —
    /// useful for ledgers that share a chart of accounts via
    /// `include "../shared/accounts.bean"`. The default is safe by
    /// design; opt out only when you trust the source of the path
    /// argument.
    #[serde(default = "default_true")]
    pub path_security: bool,
}

const fn default_true() -> bool {
    true
}

/// Parameters for ledger.validate method.
#[derive(Debug, Serialize, Deserialize)]
pub struct ValidateParams {
    /// Beancount source code.
    pub source: String,
}

/// Parameters for ledger.validateFile method.
#[derive(Debug, Deserialize)]
pub struct ValidateFileParams {
    /// Path to beancount file.
    pub path: String,
}

/// Parameters for query.execute method.
#[derive(Debug, Serialize, Deserialize)]
pub struct QueryParams {
    /// Beancount source code.
    pub source: String,
    /// BQL query string.
    pub query: String,
}

/// Parameters for query.executeFile method.
#[derive(Debug, Deserialize)]
pub struct QueryFileParams {
    /// Path to beancount file.
    pub path: String,
    /// BQL query string.
    pub query: String,
}

/// Parameters for query.batch method.
#[derive(Debug, Serialize, Deserialize)]
pub struct BatchParams {
    /// Beancount source code.
    pub source: String,
    /// List of BQL queries to execute.
    pub queries: Vec<String>,
    /// Optional filename for error messages.
    #[serde(default)]
    pub filename: Option<String>,
}

/// Parameters for query.batchFile method.
#[derive(Debug, Deserialize)]
pub struct BatchFileParams {
    /// Path to beancount file.
    pub path: String,
    /// List of BQL queries to execute.
    pub queries: Vec<String>,
}

/// Parameters for format.source method.
#[derive(Debug, Serialize, Deserialize)]
pub struct FormatSourceParams {
    /// Beancount source code.
    pub source: String,
}

/// Parameters for format.file method.
#[derive(Debug, Deserialize)]
pub struct FormatFileParams {
    /// Path to beancount file.
    pub path: String,
}

/// Parameters for format.entry method.
#[derive(Debug, Deserialize)]
pub struct FormatEntryParams {
    /// Entry to format.
    pub entry: crate::types::InputEntry,
}

/// Parameters for format.entries method.
#[derive(Debug, Deserialize)]
pub struct FormatEntriesParams {
    /// Entries to format.
    pub entries: Vec<crate::types::InputEntry>,
}

/// Parameters for entry.create method.
#[derive(Debug, Deserialize)]
pub struct CreateEntryParams {
    /// Entry to create.
    pub entry: crate::types::InputEntry,
}

/// Parameters for entry.createBatch method.
#[derive(Debug, Deserialize)]
pub struct CreateEntriesParams {
    /// Entries to create.
    pub entries: Vec<crate::types::InputEntry>,
}

/// Parameters for entry.filter method.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FilterEntriesParams {
    /// Entries to filter (raw JSON values).
    pub entries: Vec<serde_json::Value>,
    /// Begin date (inclusive).
    pub begin_date: String,
    /// End date (exclusive).
    pub end_date: String,
}

/// Parameters for entry.clamp method.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ClampEntriesParams {
    /// Entries to clamp (raw JSON values).
    pub entries: Vec<serde_json::Value>,
    /// Optional begin date.
    #[serde(default)]
    pub begin_date: Option<String>,
    /// Optional end date.
    #[serde(default)]
    pub end_date: Option<String>,
}

/// Parameters for util.isEncrypted method.
#[derive(Debug, Deserialize)]
pub struct IsEncryptedParams {
    /// Path to check.
    pub path: String,
}

/// Parameters for util.getAccountType method.
#[derive(Debug, Deserialize)]
pub struct GetAccountTypeParams {
    /// Account name.
    pub account: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_single_request() {
        let json = r#"{"jsonrpc":"2.0","method":"ledger.load","params":{"source":""},"id":1}"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Single(req) => {
                assert_eq!(req.method, "ledger.load");
                assert_eq!(req.id, Some(RequestId::Number(1)));
            }
            RequestBatch::Batch(_) => panic!("Expected single request"),
        }
    }

    #[test]
    fn test_parse_batch_request() {
        let json = r#"[
            {"jsonrpc":"2.0","method":"ledger.load","params":{"source":""},"id":1},
            {"jsonrpc":"2.0","method":"util.version","id":2}
        ]"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Batch(elements) => {
                assert_eq!(elements.len(), 2);
                match &elements[0] {
                    BatchElement::Valid(req) => assert_eq!(req.method, "ledger.load"),
                    BatchElement::Invalid { .. } => panic!("Expected valid request"),
                }
                match &elements[1] {
                    BatchElement::Valid(req) => assert_eq!(req.method, "util.version"),
                    BatchElement::Invalid { .. } => panic!("Expected valid request"),
                }
            }
            RequestBatch::Single(_) => panic!("Expected batch request"),
        }
    }

    #[test]
    fn test_parse_notification() {
        let json = r#"{"jsonrpc":"2.0","method":"notify.something","params":{}}"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Single(req) => {
                assert!(req.is_notification());
            }
            RequestBatch::Batch(_) => panic!("Expected single request"),
        }
    }

    #[test]
    fn test_request_validation() {
        let mut req = Request {
            jsonrpc: "2.0".to_string(),
            method: "test".to_string(),
            params: serde_json::Value::Null,
            id: None,
        };
        assert!(req.validate().is_ok());

        req.jsonrpc = "1.0".to_string();
        assert!(req.validate().is_err());

        req.jsonrpc = "2.0".to_string();
        req.method = "rpc.reserved".to_string();
        assert!(req.validate().is_err());
    }

    #[test]
    fn test_string_id() {
        let json = r#"{"jsonrpc":"2.0","method":"test","id":"abc"}"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Single(req) => {
                assert_eq!(req.id, Some(RequestId::String("abc".to_string())));
            }
            RequestBatch::Batch(_) => panic!("Expected single request"),
        }
    }

    #[test]
    fn test_batch_with_invalid_element() {
        // Per JSON-RPC 2.0 spec, invalid elements in batch should return per-element errors
        let json = r#"[
            {"jsonrpc":"2.0","method":"test","id":1},
            {"invalid":"not a valid request","id":2},
            {"jsonrpc":"2.0","method":"test2","id":3}
        ]"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Batch(elements) => {
                assert_eq!(elements.len(), 3);
                // First element should be valid
                assert!(matches!(&elements[0], BatchElement::Valid(req) if req.method == "test"));
                // Second element should be invalid with preserved ID
                match &elements[1] {
                    BatchElement::Invalid { error, id } => {
                        assert_eq!(*id, Some(RequestId::Number(2)));
                        assert_eq!(error.code, crate::jsonrpc::error::ErrorCode::InvalidRequest);
                    }
                    BatchElement::Valid(_) => panic!("Expected invalid element"),
                }
                // Third element should be valid
                assert!(matches!(&elements[2], BatchElement::Valid(req) if req.method == "test2"));
            }
            RequestBatch::Single(_) => panic!("Expected batch"),
        }
    }

    #[test]
    fn test_batch_invalid_element_no_id() {
        // Invalid element without an ID should still work
        let json = r#"[
            {"jsonrpc":"2.0","method":"test","id":1},
            {"totally":"broken"}
        ]"#;
        let batch = RequestBatch::parse(json).unwrap();
        match batch {
            RequestBatch::Batch(elements) => {
                assert_eq!(elements.len(), 2);
                assert!(matches!(&elements[0], BatchElement::Valid(_)));
                match &elements[1] {
                    BatchElement::Invalid { error, id } => {
                        assert!(id.is_none());
                        assert_eq!(error.code, crate::jsonrpc::error::ErrorCode::InvalidRequest);
                    }
                    BatchElement::Valid(_) => panic!("Expected invalid element"),
                }
            }
            RequestBatch::Single(_) => panic!("Expected batch"),
        }
    }
}
