______________________________________________________________________

## title: rledger doctor description: Debugging and diagnostic tools

# rledger doctor

Debugging and diagnostic tools for troubleshooting ledger issues.

## Usage

```bash
rledger doctor <SUBCOMMAND> [OPTIONS] [FILE]
```

## Subcommands

| Command | Description |
|---------|-------------|
| `lex` | Dump lexer tokens |
| `parse` | Parse and show directives |
| `context` | Show context at a line number |
| `linked` | Find transactions by link or tag |
| `missing-open` | Generate missing Open directives |
| `list-options` | List available beancount options |
| `print-options` | Print options from a file |
| `stats` | Display ledger statistics |
| `display-context` | Show decimal precision context |
| `roundtrip` | Parse and re-format (test) |
| `directories` | Validate directory structure |
| `region` | Print transactions in a line range |
| `generate-synthetic` | Generate synthetic beancount files for testing |

## Examples

### Context at Line

Find what's happening around a specific line:

```bash
rledger doctor context ledger.beancount 42
```

Output:

```
Context at ledger.beancount:42
============================================================

      40 | 2024-01-15 * "Coffee Shop" "Morning coffee"
      41 |   Expenses:Food:Coffee     5.00 USD
>>>   42 |   Assets:Cash             -5.00 USD
      43 |
      44 | 2024-01-16 * "Grocery Store"
      45 |   Expenses:Food:Groceries  42.00 USD

Directive at this location (lines 40-42):
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee   5.00 USD
  Assets:Cash           -5.00 USD
```

The directive is printed as Beancount text, as the loader parsed it.

### Find Linked Transactions

```bash
# Find by link
rledger doctor linked ledger.beancount ^trip-2024

# Find by tag
rledger doctor linked ledger.beancount "#vacation"
```

### Generate Missing Opens

```bash
# Preview
rledger doctor missing-open ledger.beancount

# Append to ledger
rledger doctor missing-open ledger.beancount >> ledger.beancount
```

### Lexer Debug

```bash
rledger doctor lex ledger.beancount | head -50
```

### Parse Debug

```bash
rledger doctor parse ledger.beancount
```

### Statistics

```bash
rledger doctor stats ledger.beancount
```

### Roundtrip Test

Verify parse/format roundtrip:

```bash
rledger doctor roundtrip ledger.beancount
```

### Print Options

```bash
rledger doctor print-options ledger.beancount
```

### List All Options

```bash
rledger doctor list-options
```

## Use Cases

### Debugging Parse Errors

```bash
# 1. Check the line with error
rledger doctor context ledger.beancount 42

# 2. See the tokens
rledger doctor lex ledger.beancount | sed -n '40,45p'
```

### Finding Orphan Accounts

```bash
# Generate opens for accounts used but never opened
rledger doctor missing-open ledger.beancount
```

### Validating Directory Structure

```bash
# Check that account directories match account hierarchy
rledger doctor directories ledger.beancount documents/
```

### Generate Synthetic Test Data

```bash
# Generate synthetic ledgers into default directory
rledger doctor generate-synthetic

# Specify output directory and options
rledger doctor generate-synthetic --output tests/synthetic --count 10
```

## See Also

- [check](check.md) - Validate ledger
- [Error Reference](../reference/errors.md) - Error codes
