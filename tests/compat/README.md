# Beancount Compatibility Tests

This directory contains test files for verifying compatibility between rustledger and Python beancount.

## Directory Structure

```
tests/compat/
├── README.md           # This file
├── sources.toml        # Documentation of file sources and licenses
└── files/              # Curated test files (~100, committed)
    ├── parser/         # Parser edge cases and syntax variations
    ├── validation/     # Validation scenarios (balancing, accounts)
    ├── plugins/        # Plugin usage and configuration
    ├── real-world/     # Real-world ledger examples
    └── edge-cases/     # Known compatibility differences

tests/compat-full/      # Full test suite (~800 files, gitignored)
                        # Downloaded on-demand via fetch script
```

## Curated vs Full Test Suite

**Curated (`tests/compat/files/`)**: ~100 representative files committed to the repository. These are selected to:
- Cover different beancount features
- Represent each source repository
- Include known edge cases
- Be small enough to commit

**Full (`tests/compat-full/`)**: ~800 files downloaded from 11+ repositories. Use this for comprehensive testing:

```bash
# Download full test suite (inside nix develop)
./scripts/fetch-compat-test-files.sh

# Run compatibility tests
./scripts/compat-test.sh
```

## Running Tests

### Quick Test (Curated Files)
```bash
# Test only curated files
./scripts/compat-test.sh tests/compat/files
```

### Full Test Suite
```bash
# Fetch all test files first
./scripts/fetch-compat-test-files.sh

# Run full compatibility tests
./scripts/compat-test.sh
```

### BQL Query Tests
```bash
./scripts/compat-bql-test.sh
```

## File Categories

| Category | Count | Description |
|----------|-------|-------------|
| parser | ~25 | Parser edge cases from beancount-parser-lima |
| validation | ~20 | Balance assertions, account validation |
| plugins | ~5 | Plugin declarations and configurations |
| real-world | ~35 | Examples from fava, beangulp, community |
| edge-cases | ~10 | Files with known compatibility differences |

## Sources

See `sources.toml` for detailed information about:
- Source repositories and URLs
- License information
- File counts per source
- Curation criteria

## Adding New Test Files

1. Add the source to `sources.toml`
2. Place curated files in appropriate `files/` subdirectory
3. Update file counts in `sources.toml`
4. Run compatibility tests to verify
