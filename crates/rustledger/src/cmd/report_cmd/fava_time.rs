//! Fava's time-filter syntax, for `rledger report ... --time EXPR`.
//!
//! A line-for-line port of `fava.util.date.parse_date` (Fava 1.30.16) and of
//! the checks Fava's `TimeFilter` applies to its result. Every form Fava
//! accepts is accepted here and resolves to the same `[begin, end)` window,
//! and every form Fava rejects is rejected; the parity table
//! (`tests/fixtures/fava_time/table.jsonl`, generated from Fava itself) pins
//! both, including the odd corners:
//!
//! - **Ranges** split at the FIRST `-` or `to` that is followed by optional
//!   whitespace, any number of `fy`, and four digits (Fava's `IS_RANGE_RE`).
//!   The range takes the left side's begin and the right side's end, and the
//!   right side may itself be a range, so `2020-2021-2022` is 2020 through
//!   2022.
//! - **Relative forms** (`year`, `month-1`, `(quarter+2)`, `week`, `day`,
//!   `fiscal_year`, `fiscal_quarter`) are textual substitutions made before
//!   anything else is parsed, exactly as Fava's `substitute` makes them:
//!   every match is found in the original string, then each is replaced
//!   everywhere it occurs. That is why `today` is rejected (its `day` is
//!   substituted, leaving `to <date>`: a range with no begin), and why an
//!   offset too large for the calendar can still sit harmlessly in the middle
//!   of a range. Offsets are arbitrary-precision, as Python's are.
//! - **"Today"** is the local date, as Fava's `datetime.date.today()` is.
//! - **Unicode digits** are digits: Fava's patterns use Python's `\d`, which
//!   matches any Unicode decimal digit, and `int()` reads them, so `２０２４`
//!   is 2024.
//! - **Calendar overflow** behaves as Python's `datetime` does: an end past
//!   9999-12-31 becomes 9999-12-31 where Fava's interval arithmetic catches the
//!   error (so `9999` is `[9999-01-01, 9999-12-31)`), and is an error where
//!   Fava does not catch it.
//!
//! The fiscal year comes from the ledger's own Fava option,
//! `custom "fava-option" "fiscal-year-end" "MM-DD"`, read the way Fava reads it
//! (see [`fiscal_year_end_from_directives`]).

use std::sync::LazyLock;

use bigdecimal::num_bigint::BigInt;
use regex::Regex;
use rustledger_core::{Directive, MetaValue, NaiveDate};

/// The end of a fiscal year: Fava's `FiscalYearEnd`.
///
/// `month` may exceed 12 (or be 0), as in Fava, where `15-31` ends the fiscal
/// year on March 31 of the FOLLOWING calendar year.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FiscalYearEnd {
    month: i64,
    day: i64,
}

/// Fava's `END_OF_YEAR`: the calendar year.
pub const END_OF_YEAR: FiscalYearEnd = FiscalYearEnd { month: 12, day: 31 };

impl Default for FiscalYearEnd {
    fn default() -> Self {
        END_OF_YEAR
    }
}

impl FiscalYearEnd {
    /// The calendar month the fiscal year ends in.
    const fn month_of_year(self) -> i64 {
        (self.month - 1).rem_euclid(12) + 1
    }

    /// How many years into the future the fiscal year end lies.
    const fn year_offset(self) -> i64 {
        (self.month - 1).div_euclid(12)
    }

    /// Whether a fiscal year starts on the first of a month, which is what
    /// fiscal quarters need.
    fn has_quarters(self) -> bool {
        py_date(2001, self.month_of_year(), self.day)
            .ok()
            .and_then(|d| d.tomorrow().ok())
            .is_some_and(|d| d.day() == 1)
    }
}

/// Parse a `fiscal-year-end` option value (`MM-DD`), as Fava's
/// `parse_fye_string`: two digits each (Unicode digits included), and the day
/// must exist in month `(MM - 1) % 12 + 1` of a non-leap year.
#[must_use]
pub fn parse_fye_string(value: &str) -> Option<FiscalYearEnd> {
    // `re.match(r"^(?P<month>\d{2})-(?P<day>\d{2})$")`: Python's `$` also
    // matches before one trailing newline.
    let s = value.strip_suffix('\n').unwrap_or(value);
    let chars: Vec<char> = s.chars().collect();
    if chars.len() != 5 || chars[2] != '-' {
        return None;
    }
    let month = digits_value(&chars[..2])?;
    let day = digits_value(&chars[3..])?;
    let month = i64::try_from(month).ok()?;
    let day = i64::try_from(day).ok()?;
    let fye = FiscalYearEnd { month, day };
    py_date(2001, fye.month_of_year(), day).ok()?;
    Some(fye)
}

/// The ledger's fiscal year end, read the way Fava reads its options.
///
/// Every `custom "fava-option"` whose first value is `fiscal-year-end` (or
/// `fiscal_year_end`) sets it, in order, so the last valid one wins. An
/// invalid value is an error in Fava and leaves the previous value in place;
/// the returned messages say which ones were ignored.
#[must_use]
pub fn fiscal_year_end_from_directives(
    directives: &[Directive],
) -> (FiscalYearEnd, Vec<(NaiveDate, String)>) {
    let mut fye = END_OF_YEAR;
    let mut ignored = Vec::new();
    for directive in directives {
        let Directive::Custom(custom) = directive else {
            continue;
        };
        if custom.custom_type != "fava-option" {
            continue;
        }
        let Some(MetaValue::String(key)) = custom.values.first() else {
            continue;
        };
        if key.replace('-', "_") != "fiscal_year_end" {
            continue;
        }
        let value = match custom.values.get(1) {
            Some(MetaValue::String(v)) => v.as_str(),
            // Fava: a missing value is the empty string, which does not parse.
            None => "",
            Some(_) => {
                ignored.push((
                    custom.date,
                    "the fava-option fiscal-year-end value must be a string".to_string(),
                ));
                continue;
            }
        };
        match parse_fye_string(value) {
            Some(parsed) => fye = parsed,
            None => ignored.push((
                custom.date,
                format!("invalid fava-option fiscal-year-end {value:?} (expected MM-DD); ignored"),
            )),
        }
    }
    (fye, ignored)
}

/// Why Fava would reject a time expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeFilterError(pub String);

impl std::fmt::Display for TimeFilterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for TimeFilterError {}

/// A Python exception inside `parse_date`: Fava rejects the whole expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Raised;

type Bounds = (Option<NaiveDate>, Option<NaiveDate>);

/// The window Fava's time filter selects for `expr`: `[begin, end)`.
///
/// Fava's `TimeFilter` rejects an expression when `parse_date` raises, when
/// either bound is missing, and when `begin` is not before `end`.
///
/// # Errors
///
/// [`TimeFilterError`] in exactly those cases.
pub fn time_window(
    expr: &str,
    fye: FiscalYearEnd,
    today: NaiveDate,
) -> Result<(NaiveDate, NaiveDate), TimeFilterError> {
    let fail = || {
        TimeFilterError(format!(
            "failed to parse --time {expr:?} (Fava's time-filter syntax: e.g. 2024, 2024-Q1, \
             2024-03, 2024-W05, 2024-03-15, FY2024, year-1, month, 2024-01 - 2024-03)"
        ))
    };
    match parse_date(expr, fye, today) {
        Ok((Some(begin), Some(end))) if begin < end => Ok((begin, end)),
        Ok((Some(begin), Some(end))) => Err(TimeFilterError(format!(
            "--time {expr:?} is the window [{begin}, {end}), which is empty: its end is not after \
             its begin"
        ))),
        _ => Err(fail()),
    }
}

/// Fava's `parse_date`: the (inclusive) begin and (exclusive) end of `string`,
/// either of which may be missing.
///
/// # Errors
///
/// [`Raised`] where Fava's `parse_date` raises.
pub fn parse_date(string: &str, fye: FiscalYearEnd, today: NaiveDate) -> Result<Bounds, Raised> {
    let string = py_strip(string).to_lowercase();
    if string.is_empty() {
        return Ok((None, None));
    }
    let string = substitute(&string, fye, today)?.to_lowercase();

    if let Some((left, right)) = split_range(&string) {
        let begin = parse_date(left, fye, today)?.0;
        let end = parse_date(right, fye, today)?.1;
        return Ok((begin, end));
    }

    let chars: Vec<char> = string.chars().collect();

    // YEAR_RE: ^\d{4}$
    if chars.len() == 4 && chars.iter().all(|c| digit_value(*c).is_some()) {
        let year = small(&chars)?;
        let start = py_date(year, 1, 1)?;
        return Ok((Some(start), Some(next_year(start))));
    }
    // MONTH_RE: ^(\d{4})-(\d{2})$
    if chars.len() == 7 && chars[4] == '-' && all_digits(&chars[..4]) && all_digits(&chars[5..]) {
        let start = py_date(small(&chars[..4])?, small(&chars[5..])?, 1)?;
        return Ok((Some(start), Some(next_month(start))));
    }
    // DAY_RE: ^(\d{4})-(\d{2})-(\d{2})$
    if chars.len() == 10
        && chars[4] == '-'
        && chars[7] == '-'
        && all_digits(&chars[..4])
        && all_digits(&chars[5..7])
        && all_digits(&chars[8..])
    {
        let start = py_date(
            small(&chars[..4])?,
            small(&chars[5..7])?,
            small(&chars[8..])?,
        )?;
        return Ok((
            Some(start),
            Some(start.tomorrow().unwrap_or(NaiveDate::MAX)),
        ));
    }
    // WEEK_RE: ^(\d{4})-w(\d{2})$
    if chars.len() == 8
        && chars[4] == '-'
        && chars[5] == 'w'
        && all_digits(&chars[..4])
        && all_digits(&chars[6..])
    {
        let start = iso_week_monday(small(&chars[..4])?, small(&chars[6..])?)?;
        return Ok((Some(start), Some(next_week(start))));
    }
    // QUARTER_RE: ^(\d{4})-q([1234])$
    if chars.len() == 7
        && chars[4] == '-'
        && chars[5] == 'q'
        && all_digits(&chars[..4])
        && ('1'..='4').contains(&chars[6])
    {
        let quarter = i64::from(chars[6] as u8 - b'0');
        let first = py_date(small(&chars[..4])?, (quarter - 1) * 3 + 1, 1)?;
        return Ok((Some(first), Some(next_quarter(first))));
    }
    // FY_RE: ^fy(\d{4})$
    if chars.len() == 6 && chars[0] == 'f' && chars[1] == 'y' && all_digits(&chars[2..]) {
        return fiscal_period(small(&chars[2..])?, fye, None);
    }
    // FY_QUARTER_RE: ^fy(\d{4})-q([1234])$
    if chars.len() == 9
        && chars[0] == 'f'
        && chars[1] == 'y'
        && all_digits(&chars[2..6])
        && chars[6] == '-'
        && chars[7] == 'q'
        && ('1'..='4').contains(&chars[8])
    {
        let quarter = i64::from(chars[8] as u8 - b'0');
        return fiscal_period(small(&chars[2..6])?, fye, Some(quarter));
    }
    Ok((None, None))
}

/// Fava's `IS_RANGE_RE`, `(.*?)(?:-|to)(?=\s*(?:fy)*\d{4})(.*)`, applied with
/// `re.match`: the left side is the SHORTEST prefix followed by `-` or `to`
/// and then by optional whitespace, any number of `fy`, and four digits. `.`
/// does not match a newline, so neither side extends past one.
fn split_range(s: &str) -> Option<(&str, &str)> {
    for (i, c) in s.char_indices() {
        let rest = &s[i..];
        let token = if rest.starts_with('-') {
            1
        } else if rest.starts_with("to") {
            2
        } else if c == '\n' {
            // The lazy `.*?` cannot step over a newline.
            return None;
        } else {
            continue;
        };
        let after = &rest[token..];
        if range_lookahead(after) {
            let right = after.split('\n').next().unwrap_or("");
            return Some((&s[..i], right));
        }
        if c == '\n' {
            return None;
        }
    }
    None
}

/// The lookahead `\s*(?:fy)*\d{4}`.
fn range_lookahead(s: &str) -> bool {
    let mut rest = s.trim_start_matches(py_isspace);
    while let Some(r) = rest.strip_prefix("fy") {
        rest = r;
    }
    let mut chars = rest.chars();
    (0..4).all(|_| chars.next().and_then(digit_value).is_some())
}

/// Fava's `VARIABLE_RE`.
static VARIABLE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"\(?(fiscal_year|year|fiscal_quarter|quarter|month|week|day)(?:([-+])(\d+))?\)?")
        .expect("valid regex")
});

/// Fava's `substitute`: replace the variables that refer to today.
fn substitute(string: &str, fye: FiscalYearEnd, today: NaiveDate) -> Result<String, Raised> {
    let mut out = string.to_string();
    let (ty, tm, td) = (
        i64::from(today.year()),
        i64::from(today.month()),
        i64::from(today.day()),
    );
    for caps in VARIABLE_RE.captures_iter(string) {
        let complete = caps.get(0).map_or("", |m| m.as_str());
        let interval = caps.get(1).map_or("", |m| m.as_str());
        let modulus = match caps.get(3) {
            Some(m) => big_digits(m.as_str()).ok_or(Raised)?,
            None => BigInt::from(0),
        };
        let offset = if caps.get(2).map(|m| m.as_str()) == Some("+") {
            modulus
        } else {
            -modulus
        };
        let replacement = match interval {
            "fiscal_year" => {
                let after_fye = (tm, td) > (fye.month_of_year(), fye.day);
                let year = ty + i64::from(after_fye) - fye.year_offset();
                format!("FY{}", BigInt::from(year) + offset)
            }
            "year" => (BigInt::from(ty) + offset).to_string(),
            "fiscal_quarter" => {
                if !fye.has_quarters() {
                    return Err(Raised);
                }
                // month_offset(today.replace(day=1), offset * 3)
                let (year_delta, month0) =
                    floor_divmod(&(BigInt::from(tm - 1) + offset * BigInt::from(3)), 12);
                let target_year =
                    i64::try_from(BigInt::from(ty) + year_delta).map_err(|_| Raised)?;
                let target = py_date(target_year, month0 + 1, 1)?;
                let target_month = i64::from(target.month());
                let after_fye = target_month > fye.month_of_year();
                let year = i64::from(target.year()) + i64::from(after_fye) - fye.year_offset();
                let quarter = (target_month - fye.month_of_year() - 1)
                    .div_euclid(3)
                    .rem_euclid(4)
                    + 1;
                format!("FY{year}-Q{quarter}")
            }
            "quarter" => {
                let quarter_today = (tm - 1) / 3 + 1;
                let (year_delta, quarter0) =
                    floor_divmod(&(BigInt::from(quarter_today - 1) + offset), 4);
                format!("{}-Q{}", BigInt::from(ty) + year_delta, quarter0 + 1)
            }
            "month" => {
                let (year_delta, month0) = floor_divmod(&(BigInt::from(tm - 1) + offset), 12);
                format!("{}-{:02}", BigInt::from(ty) + year_delta, month0 + 1)
            }
            "week" => {
                let date = add_days(today, offset * BigInt::from(7))?;
                let iso = date.iso_week_date();
                format!("{}-W{:02}", py_year(i64::from(iso.year())), iso.week())
            }
            "day" => {
                let date = add_days(today, offset)?;
                format!("{:04}-{:02}-{:02}", date.year(), date.month(), date.day())
            }
            _ => continue,
        };
        out = out.replace(complete, &replacement);
    }
    Ok(out)
}

/// `get_fiscal_period`.
fn fiscal_period(year: i64, fye: FiscalYearEnd, quarter: Option<i64>) -> Result<Bounds, Raised> {
    let end_of_previous = py_date(year - 1 + fye.year_offset(), fye.month_of_year(), fye.day)?;
    let mut start = py_add_days(end_of_previous, 1)?;
    // Special case 02-28 because of leap years.
    if fye.month_of_year() == 2 && fye.day == 28 {
        start = py_date(i64::from(start.year()), 3, 1)?;
    }
    let Some(quarter) = quarter else {
        let end = py_date(
            i64::from(start.year()) + 1,
            i64::from(start.month()),
            i64::from(start.day()),
        )?;
        return Ok((Some(start), Some(end)));
    };
    if !fye.has_quarters() {
        return Ok((None, None));
    }
    let start = month_offset(start, (quarter - 1) * 3)?;
    let end = month_offset(start, 3)?;
    Ok((Some(start), Some(end)))
}

/// Fava's `month_offset`: keep the day, raise where it does not exist.
fn month_offset(date: NaiveDate, months: i64) -> Result<NaiveDate, Raised> {
    let total = i64::from(date.month()) - 1 + months;
    let (year_delta, month0) = (total.div_euclid(12), total.rem_euclid(12));
    py_date(
        i64::from(date.year()) + year_delta,
        month0 + 1,
        i64::from(date.day()),
    )
}

/// `datetime.date.strptime(f"{year}-W{week}-1", "%G-W%V-%w")`: the Monday of
/// ISO week `week` of ISO year `year`, with Python's quirks — `%G` needs four
/// digits (so years before 1000 raise), and the week must exist: 1 through
/// the year's last ISO week (52, or 53 in a long year), as `CPython` 3.13's
/// `_strptime` checks.
fn iso_week_monday(year: i64, week: i64) -> Result<NaiveDate, Raised> {
    if !(1000..=9999).contains(&year) {
        return Err(Raised);
    }
    // December 28 always lies in the year's last ISO week.
    let weeks = i64::from(py_date(year, 12, 28)?.iso_week_date().week());
    if !(1..=weeks).contains(&week) {
        return Err(Raised);
    }
    // _calc_julian_from_V: ordinal = week * 7 + 1 - (isoweekday(Jan 4) + 3),
    // counted from Jan 1 of `year` (day 1).
    let jan4 = py_date(year, 1, 4)?;
    let correction = i64::from(jan4.weekday().to_monday_one_offset()) + 3;
    let ordinal = week * 7 + 1 - correction;
    let jan1 = py_date(year, 1, 1)?;
    py_add_days(jan1, ordinal - 1)
}

/// Python formats a year as its plain integer for `%G` (no padding).
fn py_year(year: i64) -> String {
    year.to_string()
}

fn next_year(start: NaiveDate) -> NaiveDate {
    py_date(i64::from(start.year()) + 1, 1, 1).unwrap_or(NaiveDate::MAX)
}

fn next_month(start: NaiveDate) -> NaiveDate {
    let month = i64::from(start.month());
    let (year, month) = if month == 12 {
        (i64::from(start.year()) + 1, 1)
    } else {
        (i64::from(start.year()), month + 1)
    };
    py_date(year, month, 1).unwrap_or(NaiveDate::MAX)
}

fn next_quarter(start: NaiveDate) -> NaiveDate {
    let month = (i64::from(start.month()) - 1) / 3 * 3 + 4;
    let year = i64::from(start.year()) + i64::from(month > 12);
    py_date(year, month % 12, 1).unwrap_or(NaiveDate::MAX)
}

fn next_week(start: NaiveDate) -> NaiveDate {
    let weekday = i64::from(start.weekday().to_monday_zero_offset());
    py_add_days(start, 7 - weekday).unwrap_or(NaiveDate::MAX)
}

/// `datetime.date(year, month, day)`: years 1 through 9999 only.
fn py_date(year: i64, month: i64, day: i64) -> Result<NaiveDate, Raised> {
    if !(1..=9999).contains(&year) {
        return Err(Raised);
    }
    let year = i16::try_from(year).map_err(|_| Raised)?;
    let month = i8::try_from(month).map_err(|_| Raised)?;
    let day = i8::try_from(day).map_err(|_| Raised)?;
    NaiveDate::new(year, month, day).map_err(|_| Raised)
}

/// `date + timedelta(days)`, raising past Python's date range.
fn py_add_days(date: NaiveDate, days: i64) -> Result<NaiveDate, Raised> {
    let span = jiff::Span::new().try_days(days).map_err(|_| Raised)?;
    let out = date.checked_add(span).map_err(|_| Raised)?;
    if out.year() < 1 {
        return Err(Raised);
    }
    Ok(out)
}

/// `today + timedelta(offset)` for an arbitrary-precision offset.
/// `timedelta` itself refuses more than 999 999 999 days.
fn add_days(date: NaiveDate, days: BigInt) -> Result<NaiveDate, Raised> {
    let days = i64::try_from(days).map_err(|_| Raised)?;
    if days.abs() > 999_999_999 {
        return Err(Raised);
    }
    py_add_days(date, days)
}

/// Python's `divmod(a, b)` for a positive divisor: floor division.
fn floor_divmod(a: &BigInt, b: i64) -> (BigInt, i64) {
    let b_big = BigInt::from(b);
    let mut q = a / &b_big;
    let mut r = a % &b_big;
    if r < BigInt::from(0) {
        q -= 1;
        r += &b_big;
    }
    // 0 <= r < b, so it fits.
    (q, i64::try_from(r).unwrap_or(0))
}

/// Python's `str.strip()`: whitespace as `str.isspace` defines it.
fn py_strip(s: &str) -> &str {
    s.trim_matches(py_isspace)
}

/// Python's `str.isspace` / `re`'s `\s`: Unicode whitespace plus the four
/// information separators (U+001C through U+001F), which Rust's
/// `char::is_whitespace` does not count.
fn py_isspace(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// The Unicode decimal-digit class (`\p{Nd}`), as Python's `\d` matches it.
static DIGIT_RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^\d$").expect("valid regex"));

fn is_unicode_digit(c: char) -> bool {
    if c.is_ascii_digit() {
        return true;
    }
    let mut buf = [0u8; 4];
    DIGIT_RE.is_match(c.encode_utf8(&mut buf))
}

/// The value of a Unicode decimal digit, as Python's `int()` reads it.
///
/// Unicode encodes every decimal digit in a contiguous run of ten, zero
/// first, and runs that touch (the mathematical digits) are whole runs, so a
/// digit's value is its distance from the start of its block of digits,
/// modulo ten.
fn digit_value(c: char) -> Option<u32> {
    if c.is_ascii_digit() {
        return c.to_digit(10);
    }
    if !is_unicode_digit(c) {
        return None;
    }
    let mut distance = 0u32;
    let mut code = u32::from(c);
    while let Some(prev) = code.checked_sub(1).and_then(char::from_u32) {
        if !is_unicode_digit(prev) {
            break;
        }
        distance += 1;
        code -= 1;
    }
    Some(distance % 10)
}

fn all_digits(chars: &[char]) -> bool {
    chars.iter().all(|c| digit_value(*c).is_some())
}

/// The value of a run of decimal digits (any script), or `None`.
fn digits_value(chars: &[char]) -> Option<u64> {
    chars.iter().try_fold(0u64, |acc, c| {
        acc.checked_mul(10)?
            .checked_add(u64::from(digit_value(*c)?))
    })
}

/// A short run of digits (a year, month, day or week) as `i64`.
fn small(chars: &[char]) -> Result<i64, Raised> {
    digits_value(chars)
        .and_then(|v| i64::try_from(v).ok())
        .ok_or(Raised)
}

/// An arbitrarily long run of digits, as Python's `int()`.
fn big_digits(s: &str) -> Option<BigInt> {
    let ascii: String = s
        .chars()
        .map(|c| digit_value(c).and_then(|v| char::from_digit(v, 10)))
        .collect::<Option<_>>()?;
    ascii.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn date(s: &str) -> NaiveDate {
        s.parse().expect("valid date")
    }

    fn show(d: Option<NaiveDate>) -> serde_json::Value {
        d.map_or(serde_json::Value::Null, |d| {
            serde_json::Value::String(format!("{:04}-{:02}-{:02}", d.year(), d.month(), d.day()))
        })
    }

    /// Every case in the table generated from Fava's own `parse_date` and
    /// `TimeFilter` (see `tests/fixtures/fava_time/generate.py`): the raw
    /// bounds AND the accepted window agree with Fava on all of them.
    #[test]
    fn matches_favas_parse_date_on_the_generated_table() {
        let table = include_str!("../../../tests/fixtures/fava_time/table.jsonl");
        let mut checked = 0usize;
        let mut accepted = 0usize;
        let mut failures = Vec::new();
        for line in table.lines() {
            let case: serde_json::Value = serde_json::from_str(line).expect("table line is JSON");
            let today = date(case[0].as_str().expect("today"));
            let fye = case[1]
                .as_str()
                .and_then(parse_fye_string)
                .unwrap_or(END_OF_YEAR);
            let expr = case[2].as_str().expect("expr");
            let raw = match parse_date(expr, fye, today) {
                Ok((b, e)) => serde_json::Value::Array(vec![show(b), show(e)]),
                Err(Raised) => serde_json::Value::String("error".into()),
            };
            let window = match time_window(expr, fye, today) {
                Ok((b, e)) => {
                    accepted += 1;
                    serde_json::Value::Array(vec![show(Some(b)), show(Some(e))])
                }
                Err(_) => serde_json::Value::String("error".into()),
            };
            if raw != case[3] || window != case[4] {
                failures.push(format!(
                    "today={today} fye={:?} expr={expr:?}: got raw={raw} window={window}, \
                     Fava raw={} window={}",
                    case[1], case[3], case[4]
                ));
            }
            checked += 1;
        }
        // A table that silently stopped loading must not pass.
        assert!(checked > 5000, "only {checked} cases loaded");
        assert!(accepted > 500, "only {accepted} accepted cases");
        assert!(
            failures.is_empty(),
            "{} of {checked} cases differ from Fava:\n{}",
            failures.len(),
            failures
                .iter()
                .take(40)
                .cloned()
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    /// The fye strings the table uses parse exactly as Fava's
    /// `parse_fye_string` does (None for the invalid ones).
    #[test]
    fn fiscal_year_end_strings() {
        assert_eq!(
            parse_fye_string("03-31"),
            Some(FiscalYearEnd { month: 3, day: 31 })
        );
        assert_eq!(
            parse_fye_string("15-31"),
            Some(FiscalYearEnd { month: 15, day: 31 })
        );
        assert_eq!(
            parse_fye_string("00-31"),
            Some(FiscalYearEnd { month: 0, day: 31 })
        );
        assert_eq!(
            parse_fye_string("03-31\n"),
            Some(FiscalYearEnd { month: 3, day: 31 })
        );
        assert_eq!(parse_fye_string("02-29"), None);
        assert_eq!(parse_fye_string("13-00"), None);
        assert_eq!(parse_fye_string("3-31"), None);
    }

    #[test]
    fn fiscal_year_end_is_read_from_fava_options_last_valid_wins() {
        let src = "2020-01-01 custom \"fava-option\" \"fiscal-year-end\" \"03-31\"\n\
                   2020-01-02 custom \"fava-option\" \"fiscal_year_end\" \"09-30\"\n\
                   2020-01-03 custom \"fava-option\" \"fiscal-year-end\" \"02-30\"\n\
                   2020-01-04 custom \"fava-option\" \"language\" \"en\"\n";
        let directives: Vec<Directive> = rustledger_parser::parse(src)
            .directives
            .into_iter()
            .map(|s| s.value)
            .collect();
        let (fye, ignored) = fiscal_year_end_from_directives(&directives);
        assert_eq!(fye, FiscalYearEnd { month: 9, day: 30 });
        assert_eq!(ignored.len(), 1, "{ignored:?}");
        let window = time_window("fy2025", fye, date("2026-10-20")).expect("fy2025");
        assert_eq!(window, (date("2024-10-01"), date("2025-10-01")));
    }
}
