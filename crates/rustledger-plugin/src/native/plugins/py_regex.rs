//! A regular expression from a plugin's config, read as Python's `re` reads
//! it (#2601). The translator lives in [`rustledger_core::py_regex`], shared
//! with BQL's regex operators and functions (#2656).

pub use rustledger_core::py_regex::*;
