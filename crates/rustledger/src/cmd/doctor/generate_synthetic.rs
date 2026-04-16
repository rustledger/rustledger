use anyhow::{Context, Result};
use rustledger_core::NaiveDate;
use std::fs;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_generate_synthetic<W: Write>(
    output: &PathBuf,
    count: usize,
    seed: Option<u64>,
    skip_validation: bool,
    write_manifest: bool,
    edge_cases_only: bool,
    writer: &mut W,
) -> Result<()> {
    use rustledger_core::synthetic::{ManifestEntry, SyntheticManifest, generate_all_edge_cases};
    use sha2::{Digest, Sha256};
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    writeln!(writer, "Synthetic File Generator")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Determine seed
    let seed = seed.unwrap_or_else(|| {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(12345, |d| d.as_secs())
    });

    writeln!(writer, "Output directory: {}", output.display())?;
    writeln!(writer, "Seed: {seed}")?;
    writeln!(
        writer,
        "Validation: {}",
        if skip_validation {
            "disabled"
        } else {
            "enabled"
        }
    )?;
    writeln!(writer)?;

    // Create output directory
    fs::create_dir_all(output)
        .with_context(|| format!("failed to create output directory: {}", output.display()))?;

    let mut manifest = SyntheticManifest::new(seed);
    let mut generated = 0;
    let mut valid = 0;
    let mut invalid = 0;

    // Generate edge case files
    writeln!(writer, "Generating edge case files...")?;
    for collection in generate_all_edge_cases() {
        let filename = format!("edge_case_{}.beancount", collection.category);
        let filepath = output.join(&filename);
        let content = collection.to_beancount();

        fs::write(&filepath, &content)
            .with_context(|| format!("failed to write {}", filepath.display()))?;

        generated += 1;

        // Validate with bean-check if requested
        let is_valid = if skip_validation {
            true
        } else if let Ok(output) = Command::new("bean-check").arg(&filepath).output() {
            output.status.success()
        } else {
            writeln!(
                writer,
                "  Warning: bean-check not found, skipping validation"
            )?;
            true
        };

        if is_valid {
            valid += 1;
            writeln!(
                writer,
                "  Created: {} ({} directives)",
                filename,
                collection.directives.len()
            )?;

            if write_manifest {
                use std::fmt::Write;
                let hash =
                    Sha256::digest(content.as_bytes())
                        .iter()
                        .fold(String::new(), |mut s, b| {
                            let _ = write!(s, "{b:02x}");
                            s
                        });
                manifest.add_entry(
                    ManifestEntry::new(&filename, "edge-case")
                        .with_directive_count(collection.directives.len())
                        .with_sha256(&hash)
                        .with_size(content.len() as u64)
                        .with_description(format!("Edge cases: {}", collection.category))
                        .with_validation(true),
                );
            }
        } else {
            invalid += 1;
            writeln!(writer, "  Invalid: {filename} (removing)")?;
            let _ = fs::remove_file(&filepath);
        }
    }

    // Generate additional proptest-style files if not edge-cases-only
    if !edge_cases_only && count > 0 {
        writeln!(writer)?;
        writeln!(writer, "Generating proptest-style files...")?;

        // Use a simple PRNG seeded with the user's seed
        let mut rng_state = seed;

        for i in 0..count {
            // Simple LCG for deterministic generation
            rng_state = rng_state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);

            let year = 2020 + (rng_state % 5) as i32;
            let start_date = NaiveDate::from_ymd_opt(year, 1, 1).unwrap();

            let filename = format!("synthetic_{:04}.beancount", i + 1);
            let filepath = output.join(&filename);

            // Generate a simple ledger
            let mut content = String::new();
            content.push_str(&format!("; Synthetic beancount file #{}\n", i + 1));
            content.push_str(&format!("; Seed: {seed}\n\n"));

            // Open accounts
            content.push_str(&format!("{start_date} open Assets:Bank:Checking USD\n"));
            content.push_str(&format!("{start_date} open Assets:Cash USD\n"));
            content.push_str(&format!("{start_date} open Expenses:Food USD\n"));
            content.push_str(&format!("{start_date} open Expenses:Rent USD\n"));
            content.push_str(&format!("{start_date} open Income:Salary USD\n"));
            content.push_str(&format!("{start_date} open Equity:Opening USD\n\n"));

            // Generate transactions
            let num_txns = 10 + (rng_state % 20) as usize;
            for j in 0..num_txns {
                rng_state = rng_state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);

                let month = 1 + (rng_state % 12) as u32;
                let day = 1 + (rng_state % 28) as u32;
                let amount = 10 + (rng_state % 990);
                let amount_str = format!("{}.{:02}", amount / 100, amount % 100);

                let txn_date = NaiveDate::from_ymd_opt(year, month, day).unwrap_or(start_date);

                match j % 3 {
                    0 => {
                        content.push_str(&format!(
                            "{txn_date} * \"Employer\" \"Salary\"\n  Assets:Bank:Checking  {amount_str} USD\n  Income:Salary\n\n"
                        ));
                    }
                    1 => {
                        content.push_str(&format!(
                            "{txn_date} * \"Store\" \"Groceries\"\n  Expenses:Food  {amount_str} USD\n  Assets:Bank:Checking\n\n"
                        ));
                    }
                    _ => {
                        content.push_str(&format!(
                            "{txn_date} * \"Landlord\" \"Rent\"\n  Expenses:Rent  {amount_str} USD\n  Assets:Bank:Checking\n\n"
                        ));
                    }
                }
            }

            fs::write(&filepath, &content)
                .with_context(|| format!("failed to write {}", filepath.display()))?;

            generated += 1;

            // Validate
            let is_valid = if skip_validation {
                true
            } else if let Ok(output) = Command::new("bean-check").arg(&filepath).output() {
                output.status.success()
            } else {
                true
            };

            if is_valid {
                valid += 1;

                if write_manifest {
                    use std::fmt::Write;
                    let hash = Sha256::digest(content.as_bytes()).iter().fold(
                        String::new(),
                        |mut s, b| {
                            let _ = write!(s, "{b:02x}");
                            s
                        },
                    );
                    manifest.add_entry(
                        ManifestEntry::new(&filename, "proptest")
                            .with_directive_count(6 + num_txns) // Opens + transactions
                            .with_sha256(&hash)
                            .with_size(content.len() as u64)
                            .with_validation(true),
                    );
                }
            } else {
                invalid += 1;
                let _ = fs::remove_file(&filepath);
            }

            // Progress indicator every 10 files
            if (i + 1) % 10 == 0 {
                writeln!(writer, "  Progress: {}/{}", i + 1, count)?;
            }
        }
    }

    // Write manifest
    if write_manifest {
        let manifest_path = output.join("manifest.json");
        manifest
            .save(&manifest_path)
            .with_context(|| format!("failed to write manifest: {}", manifest_path.display()))?;
        writeln!(writer)?;
        writeln!(writer, "Manifest written to: {}", manifest_path.display())?;
    }

    // Summary
    writeln!(writer)?;
    writeln!(writer, "Summary")?;
    writeln!(writer, "-------")?;
    writeln!(writer, "Generated: {generated}")?;
    writeln!(writer, "Valid:     {valid}")?;
    writeln!(writer, "Invalid:   {invalid} (removed)")?;

    Ok(())
}
