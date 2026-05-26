//! Validate Commodity directives have required metadata attributes.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin that validates Commodity directives have required metadata attributes.
///
/// Can be configured with a string specifying required attributes and their allowed values:
/// - `"{'name': null, 'sector': ['Tech', 'Finance']}"` means:
///   - `name` is required but any value is allowed
///   - `sector` is required and must be one of the allowed values
pub struct CommodityAttrPlugin {
    /// Required attributes and their allowed values (None means any value is allowed).
    required_attrs: Vec<(String, Option<Vec<String>>)>,
}

impl CommodityAttrPlugin {
    /// Create with default configuration (no required attributes).
    pub const fn new() -> Self {
        Self {
            required_attrs: Vec::new(),
        }
    }

    /// Create with required attributes.
    pub const fn with_attrs(attrs: Vec<(String, Option<Vec<String>>)>) -> Self {
        Self {
            required_attrs: attrs,
        }
    }

    /// Parse configuration string in Python dict-like format.
    ///
    /// Example: `"{'name': null, 'sector': ['Tech', 'Finance']}"`
    fn parse_config(config: &str) -> Vec<(String, Option<Vec<String>>)> {
        let mut result = Vec::new();

        // Simple parser for the config format
        // Strip outer braces and split by commas
        let trimmed = config.trim();
        let content = if trimmed.starts_with('{') && trimmed.ends_with('}') {
            &trimmed[1..trimmed.len() - 1]
        } else {
            trimmed
        };

        // Split by comma (careful with nested arrays)
        let mut depth = 0;
        let mut current = String::new();
        let mut entries = Vec::new();

        for c in content.chars() {
            match c {
                '[' => {
                    depth += 1;
                    current.push(c);
                }
                ']' => {
                    depth -= 1;
                    current.push(c);
                }
                ',' if depth == 0 => {
                    entries.push(current.trim().to_string());
                    current.clear();
                }
                _ => current.push(c),
            }
        }
        if !current.trim().is_empty() {
            entries.push(current.trim().to_string());
        }

        // Parse each entry: "'key': value"
        for entry in entries {
            if let Some((key_part, value_part)) = entry.split_once(':') {
                let key = key_part
                    .trim()
                    .trim_matches('\'')
                    .trim_matches('"')
                    .to_string();
                let value = value_part.trim();

                if value == "null" || value == "None" {
                    result.push((key, None));
                } else if value.starts_with('[') && value.ends_with(']') {
                    // Parse array of allowed values
                    let inner = &value[1..value.len() - 1];
                    let allowed: Vec<String> = inner
                        .split(',')
                        .map(|s| s.trim().trim_matches('\'').trim_matches('"').to_string())
                        .filter(|s| !s.is_empty())
                        .collect();
                    result.push((key, Some(allowed)));
                }
            }
        }

        result
    }
}

impl Default for CommodityAttrPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CommodityAttrPlugin {
    fn name(&self) -> &'static str {
        "commodity_attr"
    }

    fn description(&self) -> &'static str {
        "Validate commodity metadata attributes"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse config if provided
        let required = if let Some(config) = &input.config {
            Self::parse_config(config)
        } else {
            self.required_attrs.clone()
        };

        // If no required attributes configured, pass through
        if required.is_empty() {
            return PluginOutput {
                ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                errors: Vec::new(),
            };
        }

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Commodity(comm) = &wrapper.data {
                // Check each required attribute
                for (attr_name, allowed_values) in &required {
                    // Find the attribute in metadata
                    let found = comm.metadata.iter().find(|(k, _)| k == attr_name);

                    match found {
                        None => {
                            errors.push(PluginError::error(format!(
                                "Commodity '{}' missing required attribute '{}'",
                                comm.currency, attr_name
                            )));
                        }
                        Some((_, value)) => {
                            // Check if value is in allowed list (if specified)
                            if let Some(allowed) = allowed_values {
                                let value_str = match value {
                                    crate::types::MetaValueData::String(s) => s.clone(),
                                    other => format!("{other:?}"),
                                };
                                if !allowed.contains(&value_str) {
                                    errors.push(PluginError::error(format!(
                                        "Commodity '{}' attribute '{}' has invalid value '{}' (allowed: {:?})",
                                        comm.currency, attr_name, value_str, allowed
                                    )));
                                }
                            }
                        }
                    }
                }
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for CommodityAttrPlugin {}

#[cfg(test)]
mod commodity_attr_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_commodity_attr_missing_required() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![], // Missing 'name'
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'name': null}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("missing required"));
        assert!(output.errors[0].message.contains("name"));
    }

    #[test]
    fn test_commodity_attr_has_required() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![(
                        "name".to_string(),
                        MetaValueData::String("Apple Inc".to_string()),
                    )],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'name': null}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_commodity_attr_invalid_value() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![(
                        "sector".to_string(),
                        MetaValueData::String("Healthcare".to_string()),
                    )],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'sector': ['Tech', 'Finance']}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("invalid value"));
        assert!(output.errors[0].message.contains("Healthcare"));
    }

    #[test]
    fn test_commodity_attr_valid_value() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![(
                        "sector".to_string(),
                        MetaValueData::String("Tech".to_string()),
                    )],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'sector': ['Tech', 'Finance']}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_config_parsing() {
        let config = "{'name': null, 'sector': ['Tech', 'Finance']}";
        let parsed = CommodityAttrPlugin::parse_config(config);

        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0].0, "name");
        assert!(parsed[0].1.is_none());
        assert_eq!(parsed[1].0, "sector");
        assert_eq!(parsed[1].1.as_ref().unwrap(), &vec!["Tech", "Finance"]);
    }
}
