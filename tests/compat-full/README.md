# Full Compatibility Test Suite

This directory contains the full compatibility test suite (~800 files) downloaded from various beancount-related repositories.

**These files are NOT committed to the repository.**

## Downloading Files

```bash
# Inside nix develop shell
./scripts/fetch-compat-test-files.sh
```

This will download files from:
- beancount v2/v3 repositories
- beancount-parser-lima
- fava
- beangulp
- ledger2beancount
- beancount-import
- Community projects

## File Sources

See `tests/compat/sources.toml` for detailed source information.
