//! JSON-RPC 2.0 response types.

use serde::Serialize;

use super::error::RpcError;
use super::request::RequestId;

/// A JSON-RPC 2.0 response object.
#[derive(Debug, Clone, Serialize)]
pub struct Response {
    /// JSON-RPC version, always "2.0".
    pub jsonrpc: &'static str,
    /// The result on success (mutually exclusive with error).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<serde_json::Value>,
    /// The error on failure (mutually exclusive with result).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<RpcError>,
    /// Request ID (same as the request, or null).
    pub id: Option<RequestId>,
}

impl Response {
    /// Create a success response.
    pub fn success(id: Option<RequestId>, result: impl Serialize) -> Self {
        Self {
            jsonrpc: "2.0",
            result: Some(serde_json::to_value(result).unwrap_or(serde_json::Value::Null)),
            error: None,
            id,
        }
    }

    /// Create an error response.
    pub const fn error(id: Option<RequestId>, error: RpcError) -> Self {
        Self {
            jsonrpc: "2.0",
            result: None,
            error: Some(error),
            id,
        }
    }

    /// Create a parse error response (no ID available).
    ///
    /// Wraps [`RpcError::parse_error`] (code -32700). Per JSON-RPC 2.0,
    /// -32700 is RESERVED for the case where the server received text
    /// that could not be parsed as JSON — i.e. a transport-layer fault
    /// on the request envelope. Use this ONLY for genuinely malformed
    /// JSON input.
    ///
    /// For application-level beancount parse failures (the source file
    /// the user asked us to format/load/validate has syntax errors),
    /// build a response from [`RpcError::beancount_parse_error`] (code
    /// -32000) instead. Conflating the two causes JSON-RPC client
    /// libraries to retry the request, surface 'server sent bad JSON'
    /// to the user, or otherwise misclassify a content-level error as
    /// a transport-level one.
    pub fn parse_error(details: impl Into<String>) -> Self {
        Self::error(None, RpcError::parse_error(details))
    }

    /// Create an invalid request error response.
    pub fn invalid_request(id: Option<RequestId>, details: impl Into<String>) -> Self {
        Self::error(id, RpcError::invalid_request(details))
    }

    /// Create an internal error response.
    pub fn internal_error(id: Option<RequestId>, details: impl Into<String>) -> Self {
        Self::error(id, RpcError::internal_error(details))
    }
}

/// Either a single response or a batch of responses.
#[derive(Debug, Clone)]
pub enum ResponseBatch {
    /// Single response.
    Single(Response),
    /// Batch of responses.
    Batch(Vec<Response>),
}

impl Serialize for ResponseBatch {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Single(response) => response.serialize(serializer),
            Self::Batch(responses) => responses.serialize(serializer),
        }
    }
}

impl ResponseBatch {
    /// Create a single response.
    pub const fn single(response: Response) -> Self {
        Self::Single(response)
    }

    /// Create a batch response.
    pub fn batch(responses: Vec<Response>) -> Self {
        // Filter out notifications (they don't get responses)
        let responses: Vec<_> = responses.into_iter().collect();
        if responses.is_empty() {
            // All were notifications - return nothing (will be handled specially)
            Self::Batch(vec![])
        } else {
            Self::Batch(responses)
        }
    }

    /// Check if this batch is empty (all notifications).
    pub const fn is_empty(&self) -> bool {
        match self {
            Self::Single(_) => false,
            Self::Batch(responses) => responses.is_empty(),
        }
    }
}

/// Result types for different methods.
pub mod results {
    use serde::Serialize;

    /// Result for util.version method.
    #[derive(Serialize)]
    #[serde(rename_all = "camelCase")]
    pub struct VersionResult {
        pub api_version: &'static str,
        pub version: String,
    }

    /// Result for format methods.
    #[derive(Serialize)]
    pub struct FormatResult {
        pub formatted: String,
    }

    /// Result for util.isEncrypted method.
    #[derive(Serialize)]
    pub struct IsEncryptedResult {
        pub encrypted: bool,
    }

    /// Result for util.getAccountType method.
    #[derive(Serialize)]
    #[serde(rename_all = "camelCase")]
    pub struct GetAccountTypeResult {
        pub account_type: String,
    }

    /// Result for entry.create method.
    #[derive(Serialize)]
    pub struct CreateEntryResult {
        pub entry: crate::types::DirectiveJson,
    }

    /// Result for entry.createBatch method.
    #[derive(Serialize)]
    pub struct CreateEntriesResult {
        pub entries: Vec<crate::types::DirectiveJson>,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_success_response() {
        let response =
            Response::success(Some(RequestId::Number(1)), serde_json::json!({"ok": true}));
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"jsonrpc\":\"2.0\""));
        assert!(json.contains("\"result\""));
        assert!(json.contains("\"id\":1"));
        assert!(!json.contains("\"error\""));
    }

    #[test]
    fn test_error_response() {
        let response = Response::error(
            Some(RequestId::Number(1)),
            RpcError::method_not_found("test.method"),
        );
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"jsonrpc\":\"2.0\""));
        assert!(json.contains("\"error\""));
        assert!(json.contains("-32601"));
        assert!(!json.contains("\"result\""));
    }

    #[test]
    fn test_batch_response_serialization() {
        let batch = ResponseBatch::batch(vec![
            Response::success(Some(RequestId::Number(1)), serde_json::json!({})),
            Response::success(Some(RequestId::Number(2)), serde_json::json!({})),
        ]);
        let json = serde_json::to_string(&batch).unwrap();
        assert!(json.starts_with('['));
        assert!(json.ends_with(']'));
    }

    #[test]
    fn test_single_response_serialization() {
        let batch = ResponseBatch::single(Response::success(
            Some(RequestId::Number(1)),
            serde_json::json!({}),
        ));
        let json = serde_json::to_string(&batch).unwrap();
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
    }
}
