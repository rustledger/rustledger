# Untested Parser Functions - Priority Test Additions

## High Priority (Core Parsing)

| Function | Line | Why Test | Test Idea |
|----------|------|----------|-----------|
| `normalize_date_str()` | 136 | Date normalization logic | Test year shortcuts (24→2024), dashes, leading zeros |
| `describe_invalid_date()` | 152 | Error message generation | Test all invalid date formats |
| `parse_signed_number()` | 187 | Signed number parsing | Test +100, -50.00, +0 |
| `process_string_escapes()` | 210 | Escape sequence handling | Test \\n, \\t, \\", \\x |
| `parse_account()` | 234 | Account parsing | Test valid/invalid accounts |
| `parse_flag()` | 278 | Flag parsing (*, !, #) | Test all flag characters |
| `parse_boolean()` | 323 | Boolean parsing | Test true, false, True, False |
| `parse_expr()` | 442 | Arithmetic expressions | Test 1+2*3, (1+2)*3 |
| `parse_incomplete_amount()` | 474 | Amount without currency | Test 100, 100.00 |
| `parse_posting_metadata_line()` | 726 | Metadata line parsing | Test key: value |
| `parse_posting_metadata()` | 746 | Full metadata block | Test multi-line metadata |

## Medium Priority (Directive Parsing)

| Function | Line | Why Test | Test Idea |
|----------|------|----------|-----------|
| `parse_pushtag_directive()` | 908 | Pushtag directive | Test pushtag #tag |
| `parse_poptag_directive()` | 916 | Poptag directive | Test poptag #tag |
| `parse_pushmeta_directive()` | 924 | Pushmeta directive | Test pushmeta key: value |
| `parse_popmeta_directive()` | 933 | Popmeta directive | Test popmeta key |
| `parse_close_directive()` | 1218 | Close directive | Test close Assets:Bank |
| `parse_commodity_directive()` | 1237 | Commodity directive | Test commodity USD |
| `parse_pad_directive()` | 1257 | Pad directive | Test pad Assets:Bank |
| `parse_event_directive()` | 1278 | Event directive | Test event "Name" |
| `parse_query_directive()` | 1299 | Query directive | Test query "SELECT..." |
| `parse_note_directive()` | 1324 | Note directive | Test note "Text" |
| `parse_document_directive()` | 1346 | Document directive | Test document "Doc" |
| `parse_price_directive()` | 1383 | Price directive | Test price A 100 USD |
| `parse_custom_directive()` | 1404 | Custom directive | Test custom type: value |

## Low Priority (Edge Cases)

| Function | Line | Why Test | Test Idea |
|----------|------|----------|-----------|
| `parse_meta_key()` | 312 | Metadata key parsing | Test various key formats |
| `parse_link()` | 267 | Link parsing (^link) | Test ^http://... |
| `capture_comment()` | 375 | Comment capture | Test ; comment text |
| `parse_primary()` | 393 | Primary expression | Test numbers, parenthesized |
| `parse_term()` | 417 | Term (multiplication) | Test 2*3, 10/2 |
| `parse_cost_spec()` | 497 | Cost spec parsing | Test {100 USD}, {2024-01-01} |
| `parse_price_annotation()` | 603 | Price annotation | Test @ 100 USD |

---

## Test Plan

### Phase 1: Core Functions (High Priority)
```rust
#[test]
fn test_normalize_date_str_with_year_shortcut() {
    assert_eq!(normalize_date_str("24-01-15"), "2024-01-15");
}

#[test]
fn test_process_string_escapes() {
    assert_eq!(process_string_escapes("hello\\nworld"), "hello\nworld");
    assert_eq!(process_string_escapes("tab\\t"), "tab\t");
}

#[test]
fn test_parse_signed_number() {
    assert_eq!(parse_signed_number("+100"), Ok(dec!(100)));
    assert_eq!(parse_signed_number("-50.00"), Ok(dec!(-50.00)));
}
```

### Phase 2: Directive Parsing (Medium Priority)
Add tests for each directive type not currently tested.

### Phase 3: Edge Cases (Low Priority)
Add tests for arithmetic, metadata, and annotation parsing.

---

## Estimated Impact

**Current Coverage:** 40.88%
**After Phase 1:** ~60%
**After Phase 2:** ~75%
**After Phase 3:** ~85%

**Priority:** Start with Phase 1 (core functions) for maximum coverage gain.