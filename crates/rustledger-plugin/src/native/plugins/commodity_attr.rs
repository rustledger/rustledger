//! Validate Commodity directives have required metadata attributes.

use crate::types::{
    DirectiveData, MetaValueData, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

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

    /// Read the config: a Python dict literal, as beancount evaluates it,
    /// of attribute name to `None` (any value) or a list, tuple or set of
    /// the allowed strings (in the order written, repeats dropped); or the
    /// older form [`Self::parse_config`] reads, with `null` for `None`.
    /// `None` when it is neither.
    fn read_config(config: &str) -> Option<Vec<(String, Option<Vec<String>>)>> {
        use super::py_literal::{self, PyValue};
        let Ok(PyValue::Dict(entries)) = py_literal::parse(config) else {
            let legacy = Self::parse_config(config);
            return (!legacy.is_empty()).then_some(legacy);
        };
        let mut required: Vec<(String, Option<Vec<String>>)> = Vec::new();
        for (key, value) in entries {
            let PyValue::Str(key) = key else { return None };
            let allowed = match value {
                PyValue::None => None,
                PyValue::Seq(items) => {
                    let mut allowed: Vec<String> = Vec::new();
                    for item in items {
                        let PyValue::Str(item) = item else {
                            return None;
                        };
                        if !allowed.contains(&item) {
                            allowed.push(item);
                        }
                    }
                    Some(allowed)
                }
                _ => return None,
            };
            // A repeated key keeps its place and takes the last value, as
            // in a Python dict.
            if let Some(slot) = required.iter_mut().find(|(k, _)| *k == key) {
                slot.1 = allowed;
            } else {
                required.push((key, allowed));
            }
        }
        Some(required)
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
        let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
        let required = match &input.config {
            Some(config) => match Self::read_config(config) {
                Some(required) => required,
                None => {
                    return PluginOutput {
                        ops,
                        errors: vec![PluginError::error(
                            "Invalid configuration for commodity_attr plugin; skipping.",
                        )],
                    };
                }
            },
            None => self.required_attrs.clone(),
        };

        // As beancount's `commodity_attr` reports them (#2539), each at its
        // `commodity` directive. Before, a value outside the allowed set
        // was only checked when the config wrote a list (a tuple or set,
        // as beancount's own examples write, was ignored), and the
        // messages were rledger's own.
        let mut errors = Vec::new();
        for wrapper in &input.directives {
            let DirectiveData::Commodity(comm) = &wrapper.data else {
                continue;
            };
            for (attr_name, allowed_values) in &required {
                let Some((_, value)) = comm.metadata.iter().find(|(k, _)| k == attr_name) else {
                    errors.push(at_entry(
                        PluginError::error(format!(
                            "Missing attribute '{attr_name}' for Commodity directive {}",
                            comm.currency
                        )),
                        wrapper,
                    ));
                    continue;
                };
                let Some(allowed) = allowed_values.as_ref().filter(|a| !a.is_empty()) else {
                    continue;
                };
                // Only a string can equal one of the allowed strings.
                let shown = match value {
                    MetaValueData::String(s) => {
                        if allowed.contains(s) {
                            continue;
                        }
                        s.clone()
                    }
                    MetaValueData::Number(n) => n.clone(),
                    MetaValueData::Bool(true) => "True".to_string(),
                    MetaValueData::Bool(false) => "False".to_string(),
                    other => format!("{other:?}"),
                };
                errors.push(at_entry(
                    PluginError::error(format!(
                        "Invalid value '{shown}' for attribute {attr_name}, Commodity directive \
                         {}; valid options: {}",
                        comm.currency,
                        allowed.join(", ")
                    )),
                    wrapper,
                ));
            }
        }

        PluginOutput { ops, errors }
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
                ..Default::default()
            },
            config: Some("{'name': null}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("Missing attribute"));
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
                ..Default::default()
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
                ..Default::default()
            },
            config: Some("{'sector': ['Tech', 'Finance']}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("Invalid value"));
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
                ..Default::default()
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
