//! Deterministic cachegrind harness for the CSV importer
//! (`CsvImporter::extract_string`): a large generated CSV parsed into directives
//! in a loop, isolating import from file I/O.
//!
//! ```text
//! cargo build -p rustledger-importer --profile profiling --example profile_import
//! valgrind --tool=cachegrind ./target/profiling/examples/profile_import 20000 5
//! ```

use rustledger_importer::ImporterConfig;
use rustledger_importer::csv_importer::CsvImporter;

fn generate_csv(rows: usize) -> String {
    let mut s = String::from("Date,Description,Amount\n");
    for i in 0..rows {
        let month = i % 12 + 1;
        let day = i % 28 + 1;
        let amt = if i % 2 == 0 {
            -((i % 500) as f64) - 0.50
        } else {
            (i % 1000) as f64 + 1.00
        };
        s.push_str(&format!("{month:02}/{day:02}/2024,Merchant {i},{amt:.2}\n"));
    }
    s
}

fn main() {
    let mut a = std::env::args().skip(1);
    let rows: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let iters: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(5);

    let csv = generate_csv(rows);
    let config = ImporterConfig::csv()
        .account("Assets:Bank:Checking")
        .currency("USD")
        .date_column("Date")
        .narration_column("Description")
        .amount_column("Amount")
        .date_format("%m/%d/%Y")
        .build()
        .unwrap();

    let mut sink = 0usize;
    for _ in 0..iters {
        let r = CsvImporter
            .extract_string(std::hint::black_box(&csv), &config)
            .unwrap();
        sink = sink.wrapping_add(r.directives.len());
    }
    eprintln!(
        "import profile: {rows} rows x {iters} iters; dirs/iter={}",
        sink / iters.max(1)
    );
}
