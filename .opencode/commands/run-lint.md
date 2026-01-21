---
description: Run complete lint suite (clippy, format check, doc build)
---
Run all lint checks for the rustledger workspace:

1. Run cargo clippy with all features and treat warnings as errors:
   ```bash
   cargo clippy --all-targets --all-features -- -D warnings
   ```

2. Check code formatting with treefmt:
   ```bash
   treefmt --fail-on-change
   ```

3. Build documentation to ensure all docs compile:
   ```bash
   cargo doc --no-deps --all-features
   ```

Report the results of each command. If any fail, analyze the errors and suggest fixes.
