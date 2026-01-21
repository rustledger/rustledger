---
description: Verify project is ready for release
---
Perform release readiness checks for rustledger:

## 1. Build Check
Verify all crates compile in release mode:
```bash
cargo build --release --all-targets
```

## 2. Test Check
Run full test suite:
```bash
cargo test --all-features
```

## 3. Lint Check
Ensure all lints pass:
```bash
cargo clippy --all-features --all-targets -- -D warnings
```

## 4. Security Audit
Check for vulnerabilities:
```bash
cargo audit
cargo deny check
```

## 5. Documentation
Verify docs build without warnings:
```bash
cargo doc --no-deps --all-features
```

## 6. Release Checklist
Verify:
- All commits follow conventional commit format
- Version numbers are consistent across Cargo.toml files
- No breaking changes without proper semver bump

Report any failures and provide a summary of release readiness.
