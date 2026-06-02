//! JSON-RPC 2.0 error types.

use serde::{Deserialize, Serialize};

/// JSON-RPC 2.0 error codes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    // Standard JSON-RPC errors
    /// Invalid JSON was received.
    ParseError,
    /// The JSON sent is not a valid Request object.
    InvalidRequest,
    /// The method does not exist or is not available.
    MethodNotFound,
    /// Invalid method parameter(s).
    InvalidParams,
    /// Internal JSON-RPC error.
    InternalError,

    // Custom Beancount errors (-32000 to -32099)
    /// Beancount parse/syntax error.
    BeancountParseError,
    /// Beancount validation error.
    BeancountValidationError,
    /// BQL query error.
    QueryError,
    /// File I/O error.
    FileError,
}

impl ErrorCode {
    /// Get the numeric code for this error.
    pub const fn code(self) -> i32 {
        match self {
            Self::ParseError => -32700,
            Self::InvalidRequest => -32600,
            Self::MethodNotFound => -32601,
            Self::InvalidParams => -32602,
            Self::InternalError => -32603,
            Self::BeancountParseError => -32000,
            Self::BeancountValidationError => -32001,
            Self::QueryError => -32002,
            Self::FileError => -32003,
        }
    }
}

impl Serialize for ErrorCode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_i32(self.code())
    }
}

impl<'de> Deserialize<'de> for ErrorCode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let code = i32::deserialize(deserializer)?;
        Ok(match code {
            -32700 => Self::ParseError,
            -32600 => Self::InvalidRequest,
            -32601 => Self::MethodNotFound,
            -32602 => Self::InvalidParams,
            -32603 => Self::InternalError,
            -32000 => Self::BeancountParseError,
            -32001 => Self::BeancountValidationError,
            -32002 => Self::QueryError,
            -32003 => Self::FileError,
            _ => Self::InternalError,
        })
    }
}

/// JSON-RPC 2.0 error object.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcError {
    /// Error code.
    pub code: ErrorCode,
    /// Error message.
    pub message: String,
    /// Optional additional data.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

impl RpcError {
    /// Create a new error with just code and message.
    pub fn new(code: ErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            data: None,
        }
    }

    /// Attach structured `data` per JSON-RPC 2.0. Callers can pass
    /// arbitrary JSON; consumers that recognize the shape (e.g., an
    /// `{"errors": [...]}` array on a parse error) can surface
    /// individual entries without scraping the free-form message.
    #[must_use]
    pub fn with_data(mut self, data: serde_json::Value) -> Self {
        self.data = Some(data);
        self
    }

    /// Create a JSON-RPC parse error (code -32700).
    ///
    /// Per JSON-RPC 2.0, code -32700 is RESERVED for the case where the
    /// server received text that could not be parsed as JSON — i.e., a
    /// transport-layer fault on the request envelope. Use this only for
    /// genuine malformed-JSON conditions.
    ///
    /// For application-level beancount parse failures (the source file
    /// the user asked us to format/load/validate is invalid), use
    /// [`Self::beancount_parse_error`] instead. Conflating the two
    /// causes JSON-RPC client libraries to retry the request, surface
    /// 'server sent bad JSON' to the user, or otherwise misclassify a
    /// content-level error as a transport-level one.
    pub fn parse_error(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::ParseError, details)
    }

    /// Create a beancount parse error (code -32000, application-level).
    ///
    /// Use this when the source the user submitted to `format.source`,
    /// `format.file`, `ledger.load`, etc. has beancount syntax errors.
    /// Distinct from [`Self::parse_error`] which signals malformed JSON
    /// in the transport envelope.
    pub fn beancount_parse_error(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::BeancountParseError, details)
    }

    /// Create an invalid request error.
    pub fn invalid_request(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::InvalidRequest, details)
    }

    /// Create a method not found error.
    pub fn method_not_found(method: &str) -> Self {
        Self::new(
            ErrorCode::MethodNotFound,
            format!("Method not found: {method}"),
        )
    }

    /// Create an invalid params error.
    pub fn invalid_params(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::InvalidParams, details)
    }

    /// Create an internal error.
    pub fn internal_error(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::InternalError, details)
    }

    /// Create a file error.
    pub fn file_error(details: impl Into<String>) -> Self {
        Self::new(ErrorCode::FileError, details)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_codes() {
        assert_eq!(ErrorCode::ParseError.code(), -32700);
        assert_eq!(ErrorCode::InvalidRequest.code(), -32600);
        assert_eq!(ErrorCode::MethodNotFound.code(), -32601);
        assert_eq!(ErrorCode::InvalidParams.code(), -32602);
        assert_eq!(ErrorCode::InternalError.code(), -32603);
        assert_eq!(ErrorCode::BeancountParseError.code(), -32000);
        assert_eq!(ErrorCode::BeancountValidationError.code(), -32001);
        assert_eq!(ErrorCode::QueryError.code(), -32002);
        assert_eq!(ErrorCode::FileError.code(), -32003);
    }

    #[test]
    fn test_error_serialization() {
        let err = RpcError::method_not_found("test.method");
        let json = serde_json::to_string(&err).unwrap();
        assert!(json.contains("-32601"));
        assert!(json.contains("Method not found: test.method"));
    }
}
