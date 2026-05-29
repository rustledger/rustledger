//! File-wide amount alignment.
//!
//! Beancount alignment is a whole-file property, not a per-directive one:
//! the column at which numbers line up depends on the widest account
//! prefix and the widest number *across every amount-bearing line in the
//! file*. The on-disk formatter therefore works in two phases:
//!
//! 1. **Render** each directive into a [`FormatLine`] sequence. Amount-
//!    bearing lines are split into `(prefix, number, suffix)` so the
//!    alignment phase can move the number; everything else is [`Plain`]
//!    and emitted verbatim.
//! 2. **Align** the whole sequence at once: resolve the prefix/number
//!    column widths from the [`Alignment`] mode, then render every line.
//!
//! This mirrors `beancount.scripts.format.align_beancount`, so a file
//! formatted by `bean-format` is a fixed point of `rledger format` and
//! vice-versa (modulo rledger's stricter canonical directive rendering).
//!
//! [`Plain`]: FormatLine::Plain

/// How to choose the alignment column for amounts.
#[derive(Debug, Clone)]
pub enum Alignment {
    /// Pick widths automatically from the file contents (the default and
    /// `bean-format`'s default). Numbers are right-aligned in a field
    /// sized to the widest number; that field begins two spaces past the
    /// widest account prefix.
    ///
    /// `prefix_width` / `num_width` override the auto-computed values
    /// (the `-w` / `-W` flags); `None` means "compute from contents".
    Auto {
        /// Forced prefix column width, or `None` to auto-size.
        prefix_width: Option<usize>,
        /// Forced number field width, or `None` to auto-size.
        num_width: Option<usize>,
    },
    /// Align so the currency starts at a fixed 1-based column (the `-c`
    /// flag). Overrides the auto widths.
    CurrencyColumn(usize),
}

impl Default for Alignment {
    fn default() -> Self {
        Self::Auto {
            prefix_width: None,
            num_width: None,
        }
    }
}

/// A single rendered output line, classified for alignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatLine {
    /// Emitted verbatim — directive headers, metadata, comments, blank
    /// lines, and amount-free directives. Carries no trailing newline.
    Plain(String),
    /// An amount-bearing line, split at the number so the aligner can
    /// reposition it. `prefix` is the indented text up to (but not
    /// including) the number with no trailing whitespace; `number` is the
    /// numeric token; `suffix` is the currency and everything after it
    /// (cost, price, tolerance, trailing comment).
    Aligned {
        /// Indented text before the number, right-trimmed.
        prefix: String,
        /// The numeric token (may carry a leading `-`/`+`).
        number: String,
        /// Currency and anything following it.
        suffix: String,
    },
}

/// Char-count widths used to render [`FormatLine::Aligned`] lines.
#[derive(Debug, Clone, Copy)]
struct ResolvedWidths {
    prefix_width: usize,
    num_width: usize,
}

/// Compute the auto prefix/number widths from the aligned lines, honoring
/// any forced overrides.
fn resolve_auto_widths(
    lines: &[FormatLine],
    forced_prefix: Option<usize>,
    forced_num: Option<usize>,
) -> ResolvedWidths {
    let mut prefix_width = 0;
    let mut num_width = 0;
    for line in lines {
        if let FormatLine::Aligned { prefix, number, .. } = line {
            prefix_width = prefix_width.max(prefix.chars().count());
            num_width = num_width.max(number.chars().count());
        }
    }
    ResolvedWidths {
        prefix_width: forced_prefix.unwrap_or(prefix_width),
        num_width: forced_num.unwrap_or(num_width),
    }
}

/// Render an aligned line in auto/forced-width mode:
/// `{prefix:<PW}  {number:>NW} {suffix}`, trailing whitespace trimmed.
fn render_auto(prefix: &str, number: &str, suffix: &str, widths: ResolvedWidths) -> String {
    let prefix_pad = widths.prefix_width.saturating_sub(prefix.chars().count());
    let num_pad = widths.num_width.saturating_sub(number.chars().count());
    let mut out = String::with_capacity(
        prefix.len() + prefix_pad + 2 + num_pad + number.len() + 1 + suffix.len(),
    );
    out.push_str(prefix);
    out.extend(std::iter::repeat_n(' ', prefix_pad));
    out.push_str("  ");
    out.extend(std::iter::repeat_n(' ', num_pad));
    out.push_str(number);
    out.push(' ');
    out.push_str(suffix);
    let trimmed = out.trim_end();
    out.truncate(trimmed.len());
    out
}

/// Render an aligned line in currency-column mode so the currency lands
/// at `column` (1-based): `prefix + spaces + "  " + number + " " + suffix`,
/// trailing whitespace trimmed.
fn render_currency_column(prefix: &str, number: &str, suffix: &str, column: usize) -> String {
    // Matches beancount: num_of_spaces = column - len(prefix) - len(number) - 4,
    // clamped at zero, then a fixed two-space separator follows.
    let spaces = column
        .saturating_sub(prefix.chars().count())
        .saturating_sub(number.chars().count())
        .saturating_sub(4);
    let mut out =
        String::with_capacity(prefix.len() + spaces + 2 + number.len() + 1 + suffix.len());
    out.push_str(prefix);
    out.extend(std::iter::repeat_n(' ', spaces));
    out.push_str("  ");
    out.push_str(number);
    out.push(' ');
    out.push_str(suffix);
    let trimmed = out.trim_end();
    out.truncate(trimmed.len());
    out
}

/// Resolve `alignment` against a document's full line set into a concrete
/// alignment whose widths are fixed.
///
/// This lets individual lines be rendered one at a time while still aligning
/// to the file-wide columns.
///
/// The on-disk formatter renders the whole file in one [`render_lines`] call,
/// so it never needs this. The LSP, however, emits a separate `TextEdit` per
/// posting line: it resolves the file-wide widths once with this function,
/// then renders each posting against the returned (width-fixed) alignment so
/// editor output matches `rledger format` byte-for-byte. For
/// [`Alignment::CurrencyColumn`] the column is already absolute, so the
/// alignment is returned unchanged.
#[must_use]
pub fn resolve_alignment(lines: &[FormatLine], alignment: &Alignment) -> Alignment {
    match *alignment {
        Alignment::Auto {
            prefix_width,
            num_width,
        } => {
            let widths = resolve_auto_widths(lines, prefix_width, num_width);
            Alignment::Auto {
                prefix_width: Some(widths.prefix_width),
                num_width: Some(widths.num_width),
            }
        }
        Alignment::CurrencyColumn(column) => Alignment::CurrencyColumn(column),
    }
}

/// Render a sequence of [`FormatLine`]s into a single string, aligning all
/// amount-bearing lines against the file-wide widths implied by
/// `alignment`. Every line is terminated with `\n`.
#[must_use]
pub fn render_lines(lines: &[FormatLine], alignment: &Alignment) -> String {
    let mut out = String::new();
    match *alignment {
        Alignment::Auto {
            prefix_width,
            num_width,
        } => {
            let widths = resolve_auto_widths(lines, prefix_width, num_width);
            for line in lines {
                match line {
                    FormatLine::Plain(s) => out.push_str(s),
                    FormatLine::Aligned {
                        prefix,
                        number,
                        suffix,
                    } => out.push_str(&render_auto(prefix, number, suffix, widths)),
                }
                out.push('\n');
            }
        }
        Alignment::CurrencyColumn(column) => {
            for line in lines {
                match line {
                    FormatLine::Plain(s) => out.push_str(s),
                    FormatLine::Aligned {
                        prefix,
                        number,
                        suffix,
                    } => out.push_str(&render_currency_column(prefix, number, suffix, column)),
                }
                out.push('\n');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aligned(prefix: &str, number: &str, suffix: &str) -> FormatLine {
        FormatLine::Aligned {
            prefix: prefix.to_string(),
            number: number.to_string(),
            suffix: suffix.to_string(),
        }
    }

    #[test]
    fn auto_aligns_numbers_to_widest_prefix() {
        let lines = vec![
            aligned("  Assets:Bank:Checking", "5000", "USD"),
            aligned("  Income:Salary", "-5000", "USD"),
        ];
        let out = render_lines(&lines, &Alignment::default());
        // Widest prefix is "  Assets:Bank:Checking" (22 chars); numbers
        // are right-aligned in a 5-char field two spaces past it, so the
        // currencies line up. The number field starts at column 24.
        let rows: Vec<&str> = out.lines().collect();
        assert_eq!(rows[0], "  Assets:Bank:Checking   5000 USD");
        for row in &rows {
            assert_eq!(row.find("USD").unwrap(), 30, "row: {row:?}");
        }
    }

    #[test]
    fn auto_includes_balance_prefix_in_width() {
        // The balance line has the widest prefix, so postings align to it.
        let lines = vec![
            aligned("  Assets:Bank:Checking", "5000", "USD"),
            aligned("2024-01-16 balance Assets:Bank:Checking", "5000", "USD"),
        ];
        let out = render_lines(&lines, &Alignment::default());
        let widest = "2024-01-16 balance Assets:Bank:Checking";
        for line in out.lines() {
            let num_pos = line.find("5000").unwrap();
            assert_eq!(num_pos, widest.chars().count() + 2, "line: {line:?}");
        }
    }

    #[test]
    fn plain_lines_pass_through_verbatim() {
        let lines = vec![
            FormatLine::Plain("; a comment".to_string()),
            FormatLine::Plain("2024-01-01 open Assets:Bank USD".to_string()),
        ];
        let out = render_lines(&lines, &Alignment::default());
        assert_eq!(out, "; a comment\n2024-01-01 open Assets:Bank USD\n");
    }

    #[test]
    fn currency_column_places_currency_at_column() {
        let lines = vec![aligned("  Assets:Bank", "5000", "USD")];
        let out = render_lines(&lines, &Alignment::CurrencyColumn(60));
        let line = out.trim_end();
        // Currency starts at 1-based column 60 → 0-based index 59.
        assert_eq!(line.find("USD").unwrap(), 59, "line: {line:?}");
    }

    #[test]
    fn currency_column_keeps_min_two_spaces_when_overflowing() {
        // Prefix + number already exceed the column → clamp to 2 spaces.
        let lines = vec![aligned(
            "  Assets:Very:Long:Account:Name:That:Overflows",
            "5000",
            "USD",
        )];
        let out = render_lines(&lines, &Alignment::CurrencyColumn(10));
        assert_eq!(
            out,
            "  Assets:Very:Long:Account:Name:That:Overflows  5000 USD\n"
        );
    }

    #[test]
    fn auto_trims_trailing_space_when_suffix_empty() {
        let lines = vec![aligned("  Assets:Bank", "5000", "")];
        let out = render_lines(&lines, &Alignment::default());
        assert_eq!(out, "  Assets:Bank  5000\n");
    }

    #[test]
    fn resolve_alignment_fixes_auto_widths_for_per_line_render() {
        // resolve_alignment must capture the file-wide widths so a single
        // line rendered later (as the LSP does) aligns to the same column
        // as render_lines over the whole file.
        let lines = vec![
            aligned("  Assets:Bank:Checking", "5000", "USD"),
            aligned("  Income:Salary", "-5000", "USD"),
        ];
        let resolved = resolve_alignment(&lines, &Alignment::default());
        match resolved {
            Alignment::Auto {
                prefix_width,
                num_width,
            } => {
                assert_eq!(prefix_width, Some("  Assets:Bank:Checking".chars().count()));
                assert_eq!(num_width, Some("-5000".chars().count()));
            }
            Alignment::CurrencyColumn(_) => panic!("expected Auto"),
        }
        // Rendering one line against the resolved alignment matches the
        // whole-file column.
        let whole = render_lines(&lines, &Alignment::default());
        let single = render_lines(&lines[1..2], &resolved);
        assert_eq!(whole.lines().nth(1).unwrap(), single.trim_end_matches('\n'));
    }

    #[test]
    fn resolve_alignment_passes_currency_column_through() {
        let lines = vec![aligned("  Assets:Bank", "5000", "USD")];
        let resolved = resolve_alignment(&lines, &Alignment::CurrencyColumn(60));
        assert!(matches!(resolved, Alignment::CurrencyColumn(60)));
    }

    #[test]
    fn forced_widths_override_auto() {
        let lines = vec![aligned("  A", "5", "USD")];
        let out = render_lines(
            &lines,
            &Alignment::Auto {
                prefix_width: Some(10),
                num_width: Some(4),
            },
        );
        // prefix "  A" padded to 10, "  ", "5" right-justified in 4, " USD".
        let line = out.trim_end();
        assert_eq!(line.find('5').unwrap(), 15, "line: {line:?}");
        assert!(line.ends_with("5 USD"));
    }
}
