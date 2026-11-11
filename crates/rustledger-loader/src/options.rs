//! Beancount options parsing and storage.

use rust_decimal::Decimal;
use rustc_hash::{FxHashMap, FxHashSet};

/// Known beancount option names.
const KNOWN_OPTIONS: &[&str] = &[
    "title",
    "filename",
    "operating_currency",
    "name_assets",
    "name_liabilities",
    "name_equity",
    "name_income",
    "name_expenses",
    "account_rounding",
    "account_previous_balances",
    "account_previous_earnings",
    "account_previous_conversions",
    "account_current_earnings",
    "account_current_conversions",
    "account_unrealized_gains",
    "conversion_currency",
    "inferred_tolerance_default",
    "inferred_tolerance_multiplier",
    "infer_tolerance_from_cost",
    "use_precise_interpolation",
    "booking_method",
    "render_commas",
    "display_precision",
    "allow_pipe_separator",
    "long_string_maxlines",
    "documents",
    "insert_pythonpath",
    "plugin_processing_mode",
    "plugin",               // Known, but read-only: see `READONLY_OPTIONS`
    "tolerance_multiplier", // Renamed from inferred_tolerance_multiplier
];

/// The E7004 message for a deprecated option, if it is one.
///
/// One table rather than three inline strings: the include-scope check has to
/// report deprecation as well, and a second copy of these messages would drift
/// from the arms that raise them.
fn deprecation_message(key: &str) -> Option<&'static str> {
    match key {
        "inferred_tolerance_multiplier" => Some("Renamed to 'tolerance_multiplier'."),
        "allow_pipe_separator" => Some("Option 'allow_pipe_separator' is deprecated"),
        _ => None,
    }
}

/// Options that survive an `include` boundary.
///
/// Everything else is taken from the TOP-LEVEL file only. The split is by what
/// an option governs, not by one blanket rule (#2151):
///
/// * These describe the file that declares them. A sub-ledger naming its own
///   operating currency or document root is describing itself, not overriding
///   its includer, so they accumulate.
/// * Everything else defines global computation or the ledger's identity.
///   `booking_method` decides which lot a sale consumes and
///   `inferred_tolerance_default` decides what counts as balanced, so letting
///   an included file set them means a sub-ledger silently changes results for
///   every other entity in the tree — including the master's own transactions.
///
/// Note this is NOT the same list as [`REPEATABLE_OPTIONS`]. Repeating within
/// one file and carrying across an include are different properties:
/// `inferred_tolerance_default` accumulates within a file and must still not
/// cross an include, which is exactly the combination that let an unbalanced
/// transaction pass.
///
/// Plugins are absent for a reason that needs the two spellings kept apart.
/// The `plugin "name"` DIRECTIVE never reaches this function: it is collected
/// separately and already accumulates from any file, which is deliberate.
/// bean-query discards plugins declared in included files, leaving the user
/// with errors about accounts a plugin they did declare would have opened.
///
/// The `option "plugin"` form is a different thing: a known option that may
/// not be set ([`READONLY_OPTIONS`]), so it is an E7005 error from any file,
/// as in beancount. The include-scope branch lets the read-only options
/// through to that error rather than scoping them out with the E7009 warning,
/// and it re-raises E7004 for a deprecated option for the same reason: being
/// ignored must not quietly downgrade an error that existed before this list
/// did.
const ACCUMULATE_ACROSS_INCLUDES: &[&str] = &[
    "operating_currency",
    "documents",
    "insert_pythonpath",
    "display_precision",
];

/// Options that can be specified multiple times.
const REPEATABLE_OPTIONS: &[&str] = &[
    "operating_currency",
    "insert_pythonpath",
    "documents",
    "inferred_tolerance_default",
    "display_precision",
];

/// Options that are read-only and cannot be set by users (E7005).
///
/// beancount's `READ_ONLY_OPTIONS`, which holds `plugin` too: `option
/// "plugin"` is "may not be set" there, not deprecated (#2925). The `plugin`
/// directive is the way to load one.
const READONLY_OPTIONS: &[&str] = &["filename", "plugin"];

/// Every option name the loader knows, read-only ones included, in the
/// loader's order. The one list: `rledger doctor list-options` prints this
/// rather than keeping its own.
#[must_use]
pub const fn known_options() -> &'static [&'static str] {
    KNOWN_OPTIONS
}

/// Whether `key` is a known option that may not be set (E7005).
#[must_use]
pub fn is_read_only_option(key: &str) -> bool {
    READONLY_OPTIONS.contains(&key)
}

/// The kind of value a known option takes, as [`Options::set`] reads it, or
/// `None` for a name that is not a known option.
#[must_use]
pub fn option_value_kind(key: &str) -> Option<&'static str> {
    let kind = match key {
        "title" | "filename" | "plugin" => "string",
        "operating_currency" | "conversion_currency" => "currency",
        "name_assets" | "name_liabilities" | "name_equity" | "name_income" | "name_expenses" => {
            "account root"
        }
        "account_rounding"
        | "account_previous_balances"
        | "account_previous_earnings"
        | "account_previous_conversions"
        | "account_current_earnings"
        | "account_current_conversions"
        | "account_unrealized_gains" => "account leaf",
        "inferred_tolerance_default" | "display_precision" => "CURRENCY:NUMBER",
        "inferred_tolerance_multiplier" | "tolerance_multiplier" => "decimal",
        "infer_tolerance_from_cost"
        | "use_precise_interpolation"
        | "render_commas"
        | "allow_pipe_separator"
        | "insert_pythonpath" => "bool",
        "booking_method" => "booking method",
        // Any value is accepted (beancount has no converter and never reads
        // it); a count is recorded.
        "long_string_maxlines" => "any",
        "documents" => "path",
        "plugin_processing_mode" => "default | raw",
        _ => return None,
    };
    Some(kind)
}

/// beancount's default for `account_current_conversions`, a leaf under the
/// equity root.
pub const DEFAULT_CURRENT_CONVERSIONS: &str = "Conversions:Current";

/// Which of beancount's two readings of a boolean option a value goes
/// through (#2925).
///
/// beancount has two, and they disagree on `yes` and `on`:
///
/// * The options with a converter (`render_commas`, `use_precise_interpolation`,
///   `allow_pipe_separator`, `insert_pythonpath`) go through
///   `options_validate_boolean`: `value.lower() in ("1", "true", "yes")`.
/// * `infer_tolerance_from_cost` has no converter, so `grammar.option`'s bool
///   branch reads it: `value.lower() in {"true", "on"} or value == "1"`.
///
/// Neither ever rejects a value: anything else reads as false. rledger reads
/// it as false too, and reports a word that is in neither the true list nor
/// its false counterpart as the E7011 warning, so `check` passes as bean-check
/// does while the typo is still visible.
///
/// Deliberately not [`rustledger_core::parse_bool_word`]: that is the
/// vocabulary of metadata such as `render_commas:`, and it must not move with
/// these.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoolVocabulary {
    /// beancount's `options_validate_boolean` converter.
    Converter,
    /// beancount's `grammar.option` bool branch.
    Grammar,
}

impl BoolVocabulary {
    /// The words read as true, and the words this reports as a deliberate
    /// false, all lowercase.
    const fn words(self) -> (&'static [&'static str], &'static [&'static str]) {
        match self {
            Self::Converter => (&["1", "true", "yes"], &["0", "false", "no"]),
            // `value == "1"` in beancount is the lowercase `"1"` too: no other
            // string lowercases to it.
            Self::Grammar => (&["1", "true", "on"], &["0", "false", "off"]),
        }
    }

    /// beancount's reading of `value`, and whether the word is one this
    /// vocabulary names (`None` when it is not: it reads as false).
    fn read(self, value: &str) -> Option<bool> {
        // Python's `str.lower()`, which is Unicode-aware like this.
        let lower = value.to_lowercase();
        let (truthy, falsy) = self.words();
        if truthy.contains(&lower.as_str()) {
            Some(true)
        } else if falsy.contains(&lower.as_str()) {
            Some(false)
        } else {
            None
        }
    }
}

/// Read a `CURRENCY:NUMBER` value, as beancount's `options_validate_tolerance_map`
/// does for `inferred_tolerance_default` and `display_precision` (#2925).
///
/// beancount matches `(.*):([\d\.]+)`, so the currency is everything before
/// the LAST colon that is followed by a digit or a dot (`A:B:0.01` is
/// currency `A:B`), and the number is digits and dots only, so a sign is
/// rejected (`USD:-0.01`). `.` does not match a newline, so the colon must be
/// on the value's first line (`"A\nB:0.5"` is invalid). The number is then
/// read with `D()`. Trailing whitespace ([`is_python_space`]) is ignored, as
/// beancount ignores everything after the number.
///
/// Stricter than Python: beancount's `re.match` ignores whatever follows the
/// number, so `USD:0.01abc` reads as `0.01 USD`. We reject other text after
/// the number with E7002 (a decision on #2925): it is a typo, and taking the
/// prefix silently would set a tolerance the user may not have written. That
/// includes an exponent: beancount reads `USD:1e-2` as 1, we reject it.
///
/// Not fixable locally: see [`exact_decimal`] for the numbers rustledger
/// cannot hold. Also, Python's `\d` matches non-ASCII decimal digits
/// (`USD:١` is 1 in beancount); only ASCII digits are read here.
fn parse_tolerance_map(value: &str) -> Result<(&str, Decimal), String> {
    let is_number_char = |c: char| c.is_ascii_digit() || c == '.';
    let first_line = value.split('\n').next().unwrap_or_default();
    let Some(colon) = first_line
        .rmatch_indices(':')
        .map(|(at, _)| at)
        .find(|&at| first_line[at + 1..].starts_with(is_number_char))
    else {
        return Err(format!(
            "Invalid value '{value}': expected CURRENCY:NUMBER, e.g. USD:0.01"
        ));
    };
    let currency = &value[..colon];
    let rest = &value[colon + 1..];
    let end = rest
        .find(|c: char| !is_number_char(c))
        .unwrap_or(rest.len());
    let (number, trailing) = rest.split_at(end);
    let trailing_text = trailing.trim_matches(is_python_space);
    if !trailing_text.is_empty() {
        return Err(format!(
            "Invalid value '{value}': unexpected text '{trailing_text}' after the number"
        ));
    }
    if !is_python_number_part(number, true) {
        return Err(format!(
            "Invalid value '{value}': '{number}' is not a number"
        ));
    }
    let number = exact_decimal(number, 0).ok_or_else(|| {
        format!("Invalid value '{value}': '{number}' cannot be held exactly by rustledger")
    })?;
    Ok((currency, number))
}

/// Read a number as beancount's `D()` reads an option value (#2925): the
/// converter of `tolerance_multiplier`.
///
/// An empty value is 0. Otherwise commas and spaces are stripped (`D` treats
/// them as thousands separators) and the rest is read as Python's `Decimal`
/// reads a string: surrounding whitespace ([`is_python_space`]), a sign and an
/// exponent are accepted, and every `_` is dropped wherever it sits (`1__0`
/// is 10, `_1` is 1, `1._5` is 1.5, `1e_1` is 10); a value that is only
/// underscores is invalid. A zero significand is 0 whatever its exponent
/// (`0e100`), within the exponents Python can build.
///
/// Not fixable locally: Python's `Decimal` also reads `NaN`, `sNaN` and
/// `Infinity`, and non-ASCII decimal digits (`"١"` and `"１"` are 1), all
/// rejected here (E7002), as is any number [`exact_decimal`] cannot hold.
fn parse_beancount_decimal(value: &str) -> Result<Decimal, String> {
    if value.is_empty() {
        return Ok(Decimal::ZERO);
    }
    // In beancount's order: `D()` drops commas and spaces, then `Decimal`
    // strips surrounding whitespace, then drops every `_`. So whitespace left
    // next to an `_` stays inside the number and makes it invalid (`"_\t1"`).
    let cleaned: String = value.chars().filter(|c| !matches!(c, ',' | ' ')).collect();
    let text: String = cleaned
        .trim_matches(is_python_space)
        .chars()
        .filter(|&c| c != '_')
        .collect();
    let text = text.as_str();
    let unsigned = text.trim_start_matches(['+', '-']);
    if ["nan", "snan", "inf", "infinity"]
        .iter()
        .any(|word| unsigned.eq_ignore_ascii_case(word))
    {
        return Err(format!(
            "Invalid value '{value}': not a finite number, which rustledger \
             cannot hold"
        ));
    }
    let invalid = || format!("Invalid value '{value}': expected a decimal number");
    let (mantissa, exponent) = match text.find(['e', 'E']) {
        Some(at) => (&text[..at], Some(&text[at + 1..])),
        None => (text, None),
    };
    if !is_python_number_part(mantissa, true) {
        return Err(invalid());
    }
    if exponent.is_some_and(|e| !is_python_number_part(e, false)) {
        return Err(invalid());
    }
    let (negative, digits) = match mantissa.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, mantissa.strip_prefix('+').unwrap_or(mantissa)),
    };
    let not_held =
        || format!("Invalid value '{value}': it cannot be held exactly by rustledger's decimal");
    let exponent = match exponent {
        Some(e) => Some(parse_exponent(e).ok_or_else(not_held)?),
        None => None,
    };
    // Zero at any exponent is zero, as `Decimal("0e100")` is, as long as
    // Python can build that exponent: its context allows a final exponent
    // from `MIN_ETINY` to `MAX_EMAX`, so `0e1000000000000000000` is an error
    // in beancount and here.
    if digits.bytes().all(|b| b == b'0' || b == b'.') {
        let places = digits.split_once('.').map_or(0, |(_, frac)| frac.len());
        let places = i128::try_from(places).map_err(|_| not_held())?;
        let final_exponent = exponent.unwrap_or(0) - places;
        if !(PYTHON_MIN_ETINY..=PYTHON_MAX_EMAX).contains(&final_exponent) {
            return Err(format!(
                "Invalid value '{value}': the exponent is outside what beancount's \
                 Decimal can build"
            ));
        }
        return Ok(Decimal::ZERO);
    }
    let exponent = i64::try_from(exponent.unwrap_or(0)).map_err(|_| not_held())?;
    let number = exact_decimal(digits, exponent).ok_or_else(not_held)?;
    Ok(if negative { -number } else { number })
}

/// `CPython`'s `decimal.MAX_EMAX` on a 64-bit build: the largest exponent a
/// `Decimal` built from a string may have.
const PYTHON_MAX_EMAX: i128 = 999_999_999_999_999_999;

/// `CPython`'s `decimal.MIN_ETINY` on a 64-bit build: the smallest.
const PYTHON_MIN_ETINY: i128 = -1_999_999_999_999_999_997;

/// The value of an exponent written after `e` (an optional sign, then ASCII
/// digits), or `None` when it is too long to be any exponent Python builds.
/// Linear in its length: leading zeros are skipped once.
fn parse_exponent(text: &str) -> Option<i128> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    let digits = digits.trim_start_matches('0');
    if digits.len() > 30 {
        return None;
    }
    let n: i128 = if digits.is_empty() {
        0
    } else {
        digits.parse().ok()?
    };
    Some(if negative { -n } else { n })
}

/// The largest coefficient a `rust_decimal::Decimal` holds: 2^96 - 1.
const DECIMAL_MAX_MANTISSA: i128 = 79_228_162_514_264_337_593_543_950_335;

/// The exact value of `digits` (ASCII digits with at most one `.`, at least
/// one digit, no sign) times `10^exponent`, or `None` when a
/// `rust_decimal::Decimal` cannot hold it exactly.
///
/// Not fixable locally (deviation 3 on #2925): Python's `Decimal` holds any
/// such number exactly, while `rust_decimal` holds a 96-bit coefficient (about
/// 28 to 29 significant digits) at a scale of at most 28. A value outside that
/// range (`1e100`, `1e-29`) or needing more digits than it holds
/// (`0.0000000000000000000000000000001`, which beancount holds as 1E-31) is
/// rejected (E7002) rather than silently rounded. No real tolerance is.
///
/// The written scale is kept where it fits, since `display_precision` reads
/// it: a trailing zero is dropped only while the scale is past 28 or the
/// coefficient past 96 bits (`79228162514264337593543950335.0` is held). So
/// `display_precision` reads at most 28 places, where beancount keeps any
/// number of places, and dropping a trailing zero to fit 96 bits lowers it
/// (`USD:10000000000000000000000000000.0` reads as 0 places, beancount 1).
///
/// Linear in the input's length: the value is untrusted ledger text, read on
/// every LSP edit, so no step may rescan it per digit.
fn exact_decimal(digits: &str, exponent: i64) -> Option<Decimal> {
    let (int_part, frac_part) = digits.split_once('.').unwrap_or((digits, ""));
    let mut scale = i64::try_from(frac_part.len()).ok()?.checked_sub(exponent)?;
    let coefficient: Vec<u8> = int_part.bytes().chain(frac_part.bytes()).collect();
    let Some(first) = coefficient.iter().position(|&b| b != b'0') else {
        // Zero: keep the written scale, as far as a `Decimal` holds one.
        return Decimal::try_from_i128_with_scale(0, u32::try_from(scale.clamp(0, 28)).ok()?).ok();
    };
    let significant = &coefficient[first..];
    let trailing_zeros = significant.iter().rev().take_while(|&&b| b == b'0').count();
    // Trailing zeros that must go before the rest can fit: the scale past
    // 28, and the digits past the 29 a 96-bit coefficient can have.
    let len = i64::try_from(significant.len()).ok()?;
    let must_pop = scale.saturating_sub(28).max(len - 29).max(0);
    if must_pop > i64::try_from(trailing_zeros).ok()? {
        return None;
    }
    let mut kept = significant.len() - usize::try_from(must_pop).ok()?;
    scale -= must_pop;
    let mut n: i128 = std::str::from_utf8(&significant[..kept])
        .ok()?
        .parse()
        .ok()?;
    // A 29-digit coefficient can still be past 96 bits: drop one more
    // trailing zero while there is one and the scale allows it.
    while n > DECIMAL_MAX_MANTISSA && scale > 0 && significant[kept - 1] == b'0' {
        n /= 10;
        kept -= 1;
        scale -= 1;
    }
    while scale < 0 {
        n = n.checked_mul(10)?;
        scale += 1;
    }
    if n > DECIMAL_MAX_MANTISSA {
        return None;
    }
    Decimal::try_from_i128_with_scale(n, u32::try_from(scale).ok()?).ok()
}

/// Whether `c` is whitespace to Python's `str.isspace`, which `str.strip` and
/// `Decimal(str)` strip: Unicode `White_Space` (what `char::is_whitespace`
/// tests) plus the separators U+001C to U+001F.
const fn is_python_space(c: char) -> bool {
    c.is_whitespace() || matches!(c, '\u{1c}'..='\u{1f}')
}

/// Whether `text` is one part of a Python decimal string (underscores
/// already dropped): an optional sign, then ASCII digits, with one `.` allowed
/// when `fraction` is set, and at least one digit.
fn is_python_number_part(text: &str, fraction: bool) -> bool {
    let body = text.strip_prefix(['+', '-']).unwrap_or(text);
    let mut digits = 0;
    let mut dot = false;
    for b in body.bytes() {
        match b {
            b'0'..=b'9' => digits += 1,
            b'.' if fraction && !dot => dot = true,
            _ => return false,
        }
    }
    digits > 0
}

/// The full name of an account option given as a leaf under `root`.
///
/// beancount's `account.join(root, leaf)`, which resolves `account_previous_*`
/// and `account_current_*` onto `name_equity`. The one join every consumer
/// uses, the loader's accessors and the component's options alike (#2408).
#[must_use]
pub fn resolve_leaf_account(root: &str, leaf: &str) -> String {
    format!("{root}:{leaf}")
}

/// Where an `option` line was written: its file and 1-based line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionSite {
    /// The file the option is in, as the loader names it.
    pub file: String,
    /// The 1-based line of the `option`.
    pub line: usize,
}

/// An option value that was rejected (and so not applied) in a way that
/// changes what the ledger's figures mean.
///
/// Today only `booking_method`: see [`Options::query_refusal`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RejectedOption {
    /// The option's name.
    pub key: String,
    /// The value that was rejected.
    pub value: String,
    /// Where the option was written, when the loader knows (an option set
    /// through [`Options::set`] has no site).
    pub site: Option<OptionSite>,
}

impl RejectedOption {
    /// Why a query over the ledger refuses to answer: the option and where
    /// it is, that its value is not a booking method, and the method the
    /// figures would be booked with. One text for every surface that refuses
    /// on it.
    ///
    /// It names only the rejected value as wrong, never `booked_with`: the
    /// refusal is made only when the two differ ([`Options::query_refusal`]).
    #[must_use]
    pub fn query_refusal_message(&self, booked_with: &str) -> String {
        let site = self
            .site
            .as_ref()
            .map(|s| format!(" at {}:{}", s.file, s.line))
            .unwrap_or_default();
        format!(
            "option \"{}\"{site}: \"{}\" is not a booking method (E7002); refusing to \
             derive figures, which would be booked with {booked_with}",
            self.key, self.value,
        )
    }
}

/// Option validation warning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionWarning {
    /// Warning code (E7001 through E7011).
    pub code: &'static str,
    /// Warning message.
    pub message: String,
    /// Option name.
    pub option: String,
    /// Option value.
    pub value: String,
    /// Where the `option` line is: its file and 1-based line, as beancount
    /// locates every option error (#2925). `None` only for an option set
    /// through [`Options::set`] / [`Options::set_scoped`], which have no
    /// source to point at.
    ///
    /// Every surface reads it from here: `rledger check` (text and JSON, and
    /// `ag-rledger check` through it), the LSP's diagnostic range, WASM's
    /// `option_errors`, and the FFI.
    pub site: Option<OptionSite>,
}

impl OptionWarning {
    /// Whether this is a hard error rather than a warning.
    ///
    /// Lives on the warning, not in each consumer, because the consumers had
    /// already drifted: `rledger check` reported `E7009` as a warning while
    /// the LSP published the same code as an error, so one surface said the
    /// file was fine and the other put a red squiggle on it (#2291).
    ///
    /// `E7001` (unknown option) and `E7002` (invalid value) are errors, which
    /// matches `bean-check` exiting non-zero on both.
    ///
    /// `E7003` (duplicate non-repeatable option) is a WARNING, matching
    /// `bean-check` (last value wins, exit 0), the loader, and `validate`. A
    /// master ledger that includes self-contained sub-ledgers, each declaring
    /// its own `option "title"` for standalone use, is a legitimate beancount
    /// layout; erroring on it rejected that pattern (#1546).
    ///
    /// `E7009` (option in an included file is ignored) is a warning for the
    /// same reason and about the same ledger: #1546's repro declares a title
    /// in the master and in each sub-ledger, so once #2151 stopped the
    /// included values from governing, that layout began reporting E7009.
    /// Treating it as an error made the exact file #1546 was about exit
    /// non-zero again. The unit tests all passed; only running the repro end
    /// to end caught it.
    ///
    /// `E7011` (a boolean option value beancount does not recognize) is a
    /// warning because bean-check reports nothing for it: the word reads as
    /// false there and here (#2925).
    #[must_use]
    pub fn is_error(&self) -> bool {
        !matches!(self.code, "E7003" | "E7009" | "E7010" | "E7011")
    }

    /// The processing phase these belong to.
    ///
    /// Here for the same reason as [`is_error`](Self::is_error): both surfaces
    /// that report option warnings were choosing it independently, each with
    /// its own `"parse"` literal, and a series of bugs in this family (#2291,
    /// #2297) all came from one surface deciding something about a diagnostic
    /// that the other decided differently.
    ///
    /// `parse` because options are read while the file is being loaded, before
    /// anything is booked or validated.
    #[must_use]
    pub const fn phase(&self) -> &'static str {
        "parse"
    }
}

/// Beancount file options.
///
/// These correspond to the `option` directives in beancount files.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Options {
    /// Title for the ledger.
    pub title: Option<String>,

    /// Source filename (auto-set).
    pub filename: Option<String>,

    /// Operating currencies (for reporting).
    pub operating_currency: Vec<String>,

    /// Name prefix for Assets accounts.
    pub name_assets: String,

    /// Name prefix for Liabilities accounts.
    pub name_liabilities: String,

    /// Name prefix for Equity accounts.
    pub name_equity: String,

    /// Name prefix for Income accounts.
    pub name_income: String,

    /// Name prefix for Expenses accounts.
    pub name_expenses: String,

    /// Account for rounding errors.
    pub account_rounding: Option<String>,

    /// Account for previous balances (opening balances), as a LEAF name
    /// relative to the equity root, as beancount defines it; the full name is
    /// [`Self::previous_balances_account`].
    pub account_previous_balances: String,

    /// Account for previous earnings: a leaf under the equity root; the full
    /// name is [`Self::previous_earnings_account`].
    pub account_previous_earnings: String,

    /// Account for previous conversions: a leaf under the equity root; the
    /// full name is [`Self::previous_conversions_account`].
    pub account_previous_conversions: String,

    /// Account for current earnings: a leaf under the equity root; the full
    /// name is [`Self::current_earnings_account`].
    pub account_current_earnings: String,

    /// Account for current conversion differences: a leaf under the equity
    /// root when set (`Conversions:Current` when not); the full name is
    /// [`Self::current_conversions_account`].
    pub account_current_conversions: Option<String>,

    /// Account for unrealized gains: a leaf, which beancount joins onto the
    /// INCOME root (`doctor`), not the equity one. rledger does not post to it.
    pub account_unrealized_gains: Option<String>,

    /// Currency for conversion (if specified).
    pub conversion_currency: Option<String>,

    /// Default tolerances per currency (e.g., "USD:0.005" or "*:0.001").
    pub inferred_tolerance_default: FxHashMap<String, Decimal>,

    /// Tolerance multiplier for balance assertions.
    pub inferred_tolerance_multiplier: Decimal,

    /// Whether to infer tolerance from cost.
    pub infer_tolerance_from_cost: bool,

    /// Beancount 3.x `use_precise_interpolation` flag, parsed for compatibility.
    /// rustledger always interpolates with exact `rust_decimal` arithmetic, so
    /// this is effectively always-on; the field records the user's declared
    /// value but does not change booking results (issue #1416).
    pub use_precise_interpolation: bool,

    /// Default booking method.
    pub booking_method: String,

    /// Whether to render commas in numbers.
    pub render_commas: bool,

    /// Display precision per currency (e.g., "USD:2" means format USD with 2 decimal places).
    /// Format: CURRENCY:PRECISION where PRECISION is the number of decimal places.
    pub display_precision: FxHashMap<String, u32>,

    /// Whether to allow pipe separator in numbers.
    pub allow_pipe_separator: bool,

    /// Maximum lines in multi-line strings.
    pub long_string_maxlines: u32,

    /// Directories to scan for document files.
    pub documents: Vec<String>,

    /// Plugin processing mode: "default" or "raw".
    pub plugin_processing_mode: String,

    /// Any other custom options.
    pub custom: FxHashMap<String, String>,

    /// Options that have been set (for duplicate detection).
    #[doc(hidden)]
    pub set_options: FxHashSet<String>,

    /// Validation warnings collected during parsing.
    pub warnings: Vec<OptionWarning>,

    /// The latest `booking_method` value that was rejected, if no accepted
    /// value came after it (a later accepted value clears it: the last value
    /// wins). The option keeps its previous method, and a query over the
    /// ledger refuses when that method is not the one this value asks for
    /// (see [`Self::query_refusal`]).
    pub rejected_booking_method: Option<RejectedOption>,

    /// Where each applied value was written, `(option, value, site)`, for the
    /// diagnostics raised once every option is set (E7006 through
    /// [`Self::locate`], E7010 in [`Self::rooted_leaf_warnings`]). Transient,
    /// like `warnings`: filled by [`Self::set_scoped_at`] and not cached.
    value_sites: Vec<(String, String, OptionSite)>,
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
}

impl Options {
    /// The account previous-period balances summarize against
    /// (`account_previous_balances`), as a full account name.
    ///
    /// These options are LEAF names relative to the equity root, as beancount
    /// v2 and v3 define them ("Leaf name of the equity account ...") and as
    /// fava reads them: `get_previous_accounts` / `get_current_accounts` join
    /// `name_equity` on. So `Opening-Balances` is `Equity:Opening-Balances`,
    /// and a ledger with `option "name_equity" "Eigenkapital"` gets
    /// `Eigenkapital:Opening-Balances`. rledger used to take the value as a
    /// full name and rejected beancount's form with E7002 (#2408); a value
    /// written that old way now resolves as beancount resolves it and raises
    /// E7010 ([`Self::rooted_leaf_warnings`]). The same rule resolves the
    /// other previous- and current-period accounts.
    #[must_use]
    pub fn previous_balances_account(&self) -> String {
        resolve_leaf_account(&self.name_equity, &self.account_previous_balances)
    }

    /// The account previous-period income and expenses move to
    /// (`account_previous_earnings`), resolved as
    /// [`Self::previous_balances_account`] is.
    #[must_use]
    pub fn previous_earnings_account(&self) -> String {
        resolve_leaf_account(&self.name_equity, &self.account_previous_earnings)
    }

    /// The account a previous-period conversion residual goes to
    /// (`account_previous_conversions`), resolved as
    /// [`Self::previous_balances_account`] is.
    #[must_use]
    pub fn previous_conversions_account(&self) -> String {
        resolve_leaf_account(&self.name_equity, &self.account_previous_conversions)
    }

    /// The account a period's income and expenses move to under `CLEAR`
    /// (`account_current_earnings`), resolved as
    /// [`Self::previous_balances_account`] is.
    #[must_use]
    pub fn current_earnings_account(&self) -> String {
        resolve_leaf_account(&self.name_equity, &self.account_current_earnings)
    }

    /// The account a period's conversion residual goes to under `CLOSE`
    /// (`account_current_conversions`), resolved as
    /// [`Self::previous_balances_account`] is.
    #[must_use]
    pub fn current_conversions_account(&self) -> String {
        resolve_leaf_account(
            &self.name_equity,
            self.account_current_conversions
                .as_deref()
                .unwrap_or(DEFAULT_CURRENT_CONVERSIONS),
        )
    }

    /// The currency a conversions entry prices its postings in
    /// (`conversion_currency`): beancount's `NOTHING` when unset.
    #[must_use]
    pub fn conversion_currency_or_default(&self) -> String {
        self.conversion_currency
            .clone()
            .unwrap_or_else(|| "NOTHING".to_string())
    }

    /// The options that name an account as a leaf under the equity root,
    /// with their leaf values: beancount's `get_previous_accounts` and
    /// `get_current_accounts` join these onto `name_equity`.
    fn equity_leaf_options(&self) -> [(&'static str, &str); 5] {
        [
            ("account_previous_balances", &self.account_previous_balances),
            ("account_previous_earnings", &self.account_previous_earnings),
            (
                "account_previous_conversions",
                &self.account_previous_conversions,
            ),
            ("account_current_earnings", &self.account_current_earnings),
            (
                "account_current_conversions",
                self.account_current_conversions
                    .as_deref()
                    .unwrap_or(DEFAULT_CURRENT_CONVERSIONS),
            ),
        ]
    }

    /// E7010 for every account option whose value begins with one of the
    /// ledger's root names.
    ///
    /// Such a value is legal, and resolves as beancount resolves it: the
    /// equity root is joined on, so `Equity:Anfang` names
    /// `Equity:Equity:Anfang`. It is almost always the full-name form rledger
    /// used to document and require (#2408), so it is reported rather than
    /// reinterpreted: reinterpreting it would make the same ledger name
    /// different accounts in rledger and in beancount or fava.
    ///
    /// Run once all options are set, since `name_*` can come after the
    /// account options in the file.
    #[must_use]
    pub fn rooted_leaf_warnings(&self) -> Vec<OptionWarning> {
        let roots = self.account_types();
        self.equity_leaf_options()
            .into_iter()
            .filter(|(key, _)| self.set_options.contains(*key))
            .filter_map(|(key, leaf)| {
                let (first, rest) = match leaf.split_once(':') {
                    Some((first, rest)) => (first, Some(rest)),
                    None => (leaf, None),
                };
                if !roots.contains(&first) {
                    return None;
                }
                let full = resolve_leaf_account(&self.name_equity, leaf);
                // The fix depends on WHICH root: dropping the equity root
                // keeps the account meant; any other root cannot be kept,
                // since these options only name accounts under equity.
                let advice = match rest {
                    Some(rest) if first == self.name_equity => {
                        format!("write \"{rest}\" for {leaf}")
                    }
                    None if first == self.name_equity => {
                        "it names an account under the equity root, not the root itself".to_string()
                    }
                    _ => format!(
                        "it names an account under the equity root ({}), so it cannot name \
                         an account under {first}",
                        self.name_equity
                    ),
                };
                Some(OptionWarning {
                    code: "E7010",
                    message: format!(
                        "Option \"{key}\" names a leaf under the equity root, so \"{leaf}\" \
                         resolves to \"{full}\"; {advice}"
                    ),
                    option: key.to_string(),
                    value: leaf.to_string(),
                    site: self.site_of(key, leaf).cloned(),
                })
            })
            .collect()
    }

    /// The ledger-wide booking method: the file's `option "booking_method"`
    /// when the file set it (an `include`d file cannot, see `set_scoped`) and
    /// it parses, otherwise `default`, the embedder's own choice
    /// (`LoadOptions::booking_method`).
    ///
    /// One rule for every consumer. Booking resolved it this way, but the
    /// engines that realize balances afterwards never saw the option: `report`
    /// and BQL replayed with `BookingEngine::new()`'s FIFO and the LSP booked
    /// with STRICT, so a global `NONE` ledger that `check` accepted failed in
    /// `report balances` (#2386).
    #[must_use]
    pub fn effective_booking_method(
        &self,
        default: rustledger_core::BookingMethod,
    ) -> rustledger_core::BookingMethod {
        if self.set_options.contains("booking_method") {
            self.booking_method.parse().unwrap_or(default)
        } else {
            default
        }
    }
}

impl Options {
    /// Create new options with defaults.
    #[must_use]
    pub fn new() -> Self {
        Self {
            title: None,
            filename: None,
            operating_currency: Vec::new(),
            name_assets: "Assets".to_string(),
            name_liabilities: "Liabilities".to_string(),
            name_equity: "Equity".to_string(),
            name_income: "Income".to_string(),
            name_expenses: "Expenses".to_string(),
            account_rounding: None,
            // beancount's defaults: LEAF names, joined onto the equity root
            // where they are used (#2408); see `previous_balances_account`.
            account_previous_balances: "Opening-Balances".to_string(),
            account_previous_earnings: "Earnings:Previous".to_string(),
            account_previous_conversions: "Conversions:Previous".to_string(),
            account_current_earnings: "Earnings:Current".to_string(),
            account_current_conversions: None,
            account_unrealized_gains: None,
            conversion_currency: None,
            inferred_tolerance_default: FxHashMap::default(),
            inferred_tolerance_multiplier: Decimal::new(5, 1), // 0.5
            infer_tolerance_from_cost: false,
            use_precise_interpolation: false,
            booking_method: "STRICT".to_string(),
            render_commas: false, // Python beancount default is FALSE
            display_precision: FxHashMap::default(),
            allow_pipe_separator: false,
            long_string_maxlines: 64,
            documents: Vec::new(),
            plugin_processing_mode: "default".to_string(),
            custom: FxHashMap::default(),
            set_options: FxHashSet::default(),
            warnings: Vec::new(),
            rejected_booking_method: None,
            value_sites: Vec::new(),
        }
    }

    /// Set an option by name.
    ///
    /// Validates the option and collects any warnings in `self.warnings`.
    pub fn set(&mut self, key: &str, value: &str) {
        self.set_scoped(key, value, true);
    }

    /// Raise E7004 if `key` is deprecated.
    ///
    /// The three arms that handle deprecated options and the include-scope
    /// branch all need this, and all four previously spelled it out. Reaching
    /// for `deprecation_message(key).unwrap_or_default()` in the arms was the
    /// worst of those: an entry dropped from the table would have produced an
    /// E7004 with an EMPTY message rather than any visible failure.
    fn warn_if_deprecated(&mut self, key: &str, value: &str) {
        let Some(message) = deprecation_message(key) else {
            return;
        };
        self.warnings.push(OptionWarning {
            code: "E7004",
            message: message.to_string(),
            option: key.to_string(),
            value: value.to_string(),
            site: None,
        });
    }

    /// Apply an option, knowing whether it came from the top-level file.
    ///
    /// See the `ACCUMULATE_ACROSS_INCLUDES` list. An option outside it, seen in
    /// an INCLUDED file, is reported and dropped rather than applied: the
    /// top-level file's value governs, so an included sub-ledger cannot change
    /// how the whole tree books or balances.
    pub fn set_scoped(&mut self, key: &str, value: &str, top_level: bool) {
        self.set_scoped_at(key, value, top_level, None);
    }

    /// [`Self::set_scoped`] for an option written at `site`. Every diagnostic
    /// the option raises carries the site ([`OptionWarning::site`]), as
    /// beancount locates every option error, and so does a rejection that
    /// refuses queries ([`Self::query_refusal`]).
    pub fn set_scoped_at(
        &mut self,
        key: &str,
        value: &str,
        top_level: bool,
        site: Option<OptionSite>,
    ) {
        let mark = self.warnings.len();
        let applied = self.set_scoped_inner(key, value, top_level);
        let Some(site) = site else {
            return;
        };
        for warning in &mut self.warnings[mark..] {
            warning.site.get_or_insert_with(|| site.clone());
        }
        // A new rejection starts with no site (see the `booking_method` arm);
        // this is where it was written.
        if key == "booking_method"
            && let Some(rejected) = &mut self.rejected_booking_method
            && rejected.site.is_none()
        {
            rejected.site = Some(site.clone());
        }
        if applied {
            self.value_sites
                .push((key.to_string(), value.to_string(), site));
        }
    }

    /// Where `option` was last applied with `value`, when it was set through
    /// [`Self::set_scoped_at`].
    #[must_use]
    pub fn site_of(&self, option: &str, value: &str) -> Option<&OptionSite> {
        self.value_sites
            .iter()
            .rev()
            .find(|(k, v, _)| k == option && v == value)
            .map(|(_, _, site)| site)
    }

    /// These options with every location dropped: each diagnostic's site,
    /// the applied values' sites and the rejected `booking_method`'s.
    ///
    /// For comparing what two loads MEAN rather than where they were written:
    /// `rledger merge` and `split` move options to other files and lines, and
    /// must still find the result the same ledger.
    #[must_use]
    pub fn without_locations(&self) -> Self {
        let mut options = self.clone();
        options.value_sites.clear();
        for warning in &mut options.warnings {
            warning.site = None;
        }
        if let Some(rejected) = &mut options.rejected_booking_method {
            rejected.site = None;
        }
        options
    }

    /// Give each of `warnings` that has no site the site of the `option`
    /// line it is about ([`Self::site_of`]). For the diagnostics raised after
    /// the options are set, such as the E7006 of
    /// [`crate::document_root_warnings`], which reads only the values.
    pub fn locate(&self, warnings: &mut [OptionWarning]) {
        for warning in warnings {
            if warning.site.is_none() {
                warning.site = self.site_of(&warning.option, &warning.value).cloned();
            }
        }
    }

    /// The rejected option that stops a query over this ledger from
    /// answering, if any (#2911): the last `booking_method` value, when it
    /// was rejected and the ledger is booked with `booked_with`
    /// (`Ledger::booking_method`), a method other than the one it asked for.
    ///
    /// The option keeps its previous method, as in beancount, so `check`
    /// reports the E7002 and books as before. A query or report does not
    /// answer, though: every lot reduction would be booked with a method the
    /// user did not ask for (`fifo` alone was meant as FIFO and is booked
    /// STRICT), and the figures would look right.
    ///
    /// Only then. A later accepted value clears the rejection (the last
    /// value wins), so `fifo` then `FIFO` books FIFO and answers. A rejected
    /// value whose case-insensitive reading names the method booked does not
    /// refuse either: `FIFO` then `fifo` books FIFO, which is what both lines
    /// ask for. Anything else refuses: `fifo` alone, `bogus`, `FIFO` then
    /// `bogus`.
    ///
    /// Stricter than Python: bean-query answers here, with the figures
    /// booked under the kept method. We refuse because those figures
    /// silently use a booking method the ledger did not ask for. The other
    /// rejected options keep their default and answer: none of them changes
    /// which lots a sale consumes.
    ///
    /// Part of the query rule `Ledger::blocks_queries` applies.
    #[must_use]
    pub fn query_refusal(
        &self,
        booked_with: rustledger_core::BookingMethod,
    ) -> Option<&RejectedOption> {
        let rejected = self.rejected_booking_method.as_ref()?;
        let asked = rejected
            .value
            .parse::<rustledger_core::BookingMethod>()
            .ok();
        (asked != Some(booked_with)).then_some(rejected)
    }

    /// Whether the value was applied.
    fn set_scoped_inner(&mut self, key: &str, value: &str, top_level: bool) -> bool {
        // A read-only option is not scoped out: it may not be set from any
        // file, so it gets its E7005 error from `set_inner`, which never
        // applies it. Scoping it out would turn that error into the E7009
        // warning in an included file, the one place `option "plugin"` would
        // stop failing the build.
        if !top_level
            && KNOWN_OPTIONS.contains(&key)
            && !ACCUMULATE_ACROSS_INCLUDES.contains(&key)
            && !READONLY_OPTIONS.contains(&key)
        {
            // beancount parses an included file with its own `Builder` and
            // fresh options, so the option's converter runs there: every value
            // it rejects is an error at the included file's line, and the
            // value, valid or not, is then dropped, since only the top-level
            // file's options are kept (#2925). The same here: the value is
            // read into a scratch `Options` that starts from the defaults, its
            // diagnostics are kept, and the scratch is discarded. That raises
            // E7004 for a deprecated option too (its arm in `apply` does), so
            // being ignored cannot downgrade that error either. A rejected
            // `booking_method` stays in the scratch: the top-level method
            // governs, so it refuses no query.
            //
            // Stricter than Python, deliberately (#2925): an included file's
            // `name_*` root does not govern that file's own accounts. beancount
            // checks account roots while parsing the file, with that file's
            // options, so `option "name_equity" "Capital"` followed by
            // `open Capital:Z` in the same included file loads the account
            // (with no account type) and bean-check is clean. rledger keeps
            // one set of roots for the whole tree, the top-level file's, so
            // that `open` is E1005: an account no ledger-wide root covers.
            // Pinned by `included_name_option_does_not_root_its_own_file`.
            let mut scratch = Self::new();
            let accepted = scratch.apply(key, value);
            self.warnings.append(&mut scratch.warnings);
            // Only for a value beancount would have accepted: a rejected one
            // already has its error, and "is ignored" would add nothing.
            //
            // Its own code, not E7003. That one means "specified twice, last
            // wins" and is mapped downstream to `ErrorCode::DuplicateOption`;
            // this option may be the only one of its name in the tree.
            if accepted {
                self.warnings.push(OptionWarning {
                    code: "E7009",
                    message: format!(
                        "Option \"{key}\" set in an included file is ignored; \
                         the top-level ledger's value governs"
                    ),
                    option: key.to_string(),
                    value: value.to_string(),
                    site: None,
                });
            }
            return false;
        }
        self.set_inner(key, value)
    }

    /// Whether the value was applied.
    fn set_inner(&mut self, key: &str, value: &str) -> bool {
        // Check for unknown options (E7001)
        let is_known = KNOWN_OPTIONS.contains(&key);
        if !is_known {
            self.warnings.push(OptionWarning {
                code: "E7001",
                message: format!("Invalid option \"{key}\""),
                option: key.to_string(),
                value: value.to_string(),
                site: None,
            });
        }

        // Check for read-only options (E7005)
        if READONLY_OPTIONS.contains(&key) {
            self.warnings.push(OptionWarning {
                code: "E7005",
                message: format!("Option '{key}' may not be set"),
                option: key.to_string(),
                value: value.to_string(),
                site: None,
            });
            return false; // Don't apply the value
        }

        // Check for duplicate non-repeatable options (E7003).
        //
        // Emitted as a WARNING (not an error), matching `bean-check`, which
        // silently lets the last value win (exit 0). A master ledger that
        // `include`s self-contained sub-ledgers — each setting its own
        // `option "title"` / `booking_method` / ... for standalone use — is a
        // legitimate layout (issue #1546). The value below is applied last-wins
        // to match. `cmd::check` and `validate` both surface this as a warning.
        //
        // Only when the new value is ACCEPTED: a rejected value does not win,
        // so "the last value wins" would be false (#2911). Inserted ahead of
        // the value's own diagnostics, where it was raised before.
        let is_repeatable = REPEATABLE_OPTIONS.contains(&key);
        let already_set = self.set_options.contains(key);
        let mark = self.warnings.len();

        let applied = self.apply(key, value);
        if applied {
            if is_known && !is_repeatable && already_set {
                self.warnings.insert(
                    mark,
                    OptionWarning {
                        code: "E7003",
                        message: format!(
                            "Option \"{key}\" is set more than once; the last value wins"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                        site: None,
                    },
                );
            }
            // Track that this option was set. A rejected value is not
            // tracked: nothing it would gate (`effective_booking_method`,
            // `rooted_leaf_warnings`) may see a value that was never applied.
            self.set_options.insert(key.to_string());
        }
        applied
    }

    /// Report a value the option's converter rejects, and keep the option as
    /// it was. Always `false`, so an arm can `return self.reject(..)`.
    ///
    /// beancount's `grammar.option` returns on the converter's `ValueError`
    /// without assigning, so the option keeps its default or an earlier valid
    /// setting, and the bad value has no other effect: `option "name_equity"
    /// "capital"` leaves `Equity:A` valid (#2911). Every arm that validates its
    /// value rejects through here, so none can report the error and still
    /// apply the value.
    fn reject(&mut self, code: &'static str, key: &str, value: &str, message: String) -> bool {
        self.warnings.push(OptionWarning {
            code,
            message,
            option: key.to_string(),
            value: value.to_string(),
            site: None,
        });
        false
    }

    /// Reject an account-name option value that is not a valid leaf (E7002).
    /// `true` when the value is valid.
    fn check_leaf(&mut self, key: &str, value: &str) -> bool {
        Self::is_valid_leaf(value)
            || self.reject(
                "E7002",
                key,
                value,
                format!("Invalid leaf account name: '{value}'"),
            )
    }

    /// Reject a `name_*` value that is not a valid account root (E7008).
    /// `true` when the value is valid.
    ///
    /// An invalid root is never applied, so the accounts under the previous
    /// root stay valid and the bad value produces this one error, as in
    /// beancount (#2911). The `account_*` options get the analogous E7002
    /// guard in [`Self::check_leaf`].
    fn check_root(&mut self, key: &str, value: &str) -> bool {
        Self::is_valid_account_root(value)
            || self.reject(
                "E7008",
                key,
                value,
                format!(
                    "Invalid account type name: '{value}' cannot begin an \
                     account name, so the option keeps its previous value"
                ),
            )
    }

    /// Read a boolean option value as beancount does (see [`BoolVocabulary`]),
    /// raising the E7011 warning for a word it does not name. Never rejects:
    /// such a word reads as false, as in beancount.
    fn read_bool(&mut self, key: &str, value: &str, vocabulary: BoolVocabulary) -> bool {
        if let Some(read) = vocabulary.read(value) {
            return read;
        }
        let (truthy, falsy) = vocabulary.words();
        self.warnings.push(OptionWarning {
            code: "E7011",
            message: format!(
                "Value \"{value}\" for option \"{key}\" is not a boolean beancount \
                 recognizes, so it reads as false (true: {}; false: {})",
                truthy.join(", "),
                falsy.join(", ")
            ),
            option: key.to_string(),
            value: value.to_string(),
            site: None,
        });
        false
    }

    /// Read a `CURRENCY:NUMBER` option value ([`parse_tolerance_map`]),
    /// rejecting it with E7002 when it is not one.
    fn read_tolerance_map<'v>(&mut self, key: &str, value: &'v str) -> Option<(&'v str, Decimal)> {
        match parse_tolerance_map(value) {
            Ok(parsed) => Some(parsed),
            Err(message) => {
                self.reject(
                    "E7002",
                    key,
                    value,
                    format!("Error for option \"{key}\": {message}"),
                );
                None
            }
        }
    }

    /// Apply one option value. `false` when the value was rejected, in which
    /// case the option is unchanged (see [`Self::reject`]).
    fn apply(&mut self, key: &str, value: &str) -> bool {
        match key {
            "title" => self.title = Some(value.to_string()),
            "operating_currency" => self.operating_currency.push(value.to_string()),
            "name_assets" | "name_liabilities" | "name_equity" | "name_income"
            | "name_expenses" => {
                if !self.check_root(key, value) {
                    return false;
                }
                let slot = match key {
                    "name_assets" => &mut self.name_assets,
                    "name_liabilities" => &mut self.name_liabilities,
                    "name_equity" => &mut self.name_equity,
                    "name_income" => &mut self.name_income,
                    _ => &mut self.name_expenses,
                };
                *slot = value.to_string();
            }
            "account_rounding" => {
                // An invalid value is the E7002, as in beancount.
                if !self.check_leaf(key, value) {
                    return false;
                }
                // Recorded, and inert, as in beancount 3.2.3: the only reader
                // of `account_rounding` there is `fill_residual_posting`,
                // which nothing calls. A valid value is therefore no
                // diagnostic, as bean-check gives none. It used to raise
                // E7007 ("accepted but has no effect"), an error, which made
                // `check` fail a ledger bean-check passes (#2925).
                self.account_rounding = Some(value.to_string());
            }
            "account_current_conversions" | "account_unrealized_gains" => {
                if !self.check_leaf(key, value) {
                    return false;
                }
                let slot = if key == "account_current_conversions" {
                    &mut self.account_current_conversions
                } else {
                    &mut self.account_unrealized_gains
                };
                *slot = Some(value.to_string());
            }
            "account_previous_balances"
            | "account_previous_earnings"
            | "account_previous_conversions"
            | "account_current_earnings" => {
                if !self.check_leaf(key, value) {
                    return false;
                }
                let slot = match key {
                    "account_previous_balances" => &mut self.account_previous_balances,
                    "account_previous_earnings" => &mut self.account_previous_earnings,
                    "account_previous_conversions" => &mut self.account_previous_conversions,
                    _ => &mut self.account_current_earnings,
                };
                *slot = value.to_string();
            }
            "inferred_tolerance_multiplier" | "tolerance_multiplier" => {
                // `inferred_tolerance_multiplier` is deprecated: renamed to
                // `tolerance_multiplier` in Python beancount.
                self.warn_if_deprecated(key, value);
                // beancount's converter is `D()`: an empty value is 0, and
                // commas and exponents are accepted (#2925). Downstream, a
                // multiplier of 0 is a tolerance of 0, which `0` always gave.
                let d = match parse_beancount_decimal(value) {
                    Ok(d) => d,
                    Err(message) => {
                        return self.reject(
                            "E7002",
                            key,
                            value,
                            format!("Error for option \"{key}\": {message}"),
                        );
                    }
                };
                self.inferred_tolerance_multiplier = d;
            }
            "infer_tolerance_from_cost" => {
                // beancount reads this one through `grammar.option`'s bool
                // branch, not the converter the other booleans have, so `on`
                // is true here and `yes` is not (#2925).
                self.infer_tolerance_from_cost =
                    self.read_bool(key, value, BoolVocabulary::Grammar);
            }
            "booking_method" => {
                // beancount's converter is `data.Booking[value]`, the exact
                // enum name, so `fifo` is rejected there and here.
                let valid_methods = [
                    "STRICT",
                    "STRICT_WITH_SIZE",
                    "FIFO",
                    "LIFO",
                    "HIFO",
                    "AVERAGE",
                    "NONE",
                ];
                if !valid_methods.contains(&value) {
                    // The latest rejection, since the last value is the one
                    // the ledger asks for; its site is filled in by
                    // `set_scoped_at`.
                    self.rejected_booking_method = Some(RejectedOption {
                        key: key.to_string(),
                        value: value.to_string(),
                        site: None,
                    });
                    return self.reject(
                        "E7002",
                        key,
                        value,
                        format!(
                            "Invalid value \"{}\" for option \"{}\": expected one of {}",
                            value,
                            key,
                            valid_methods.join(", ")
                        ),
                    );
                }
                self.booking_method = value.to_string();
                // Last wins: an accepted method is what the ledger asks for,
                // so an earlier rejection no longer refuses queries.
                self.rejected_booking_method = None;
            }
            "render_commas" => {
                // beancount's `options_validate_boolean` converter (#2925).
                self.render_commas = self.read_bool(key, value, BoolVocabulary::Converter);
            }
            "display_precision" => {
                // "CURRENCY:EXAMPLE", where EXAMPLE's decimal places are the
                // precision: "CHF:0.01" is 2 places for CHF. Read by the
                // parser `inferred_tolerance_default` uses, as beancount reads
                // both with one converter.
                let Some((curr, example)) = self.read_tolerance_map(key, value) else {
                    return false;
                };
                self.display_precision
                    .insert(curr.to_string(), example.scale());
            }
            "filename" => self.filename = Some(value.to_string()),
            "conversion_currency" => self.conversion_currency = Some(value.to_string()),
            "inferred_tolerance_default" => {
                // "CURRENCY:TOLERANCE" or "*:TOLERANCE".
                let Some((curr, tol)) = self.read_tolerance_map(key, value) else {
                    return false;
                };
                self.inferred_tolerance_default
                    .insert(curr.to_string(), tol);
            }
            "use_precise_interpolation" => {
                // Accepted for beancount 3.x compatibility. rustledger already
                // interpolates with exact decimals, so this is a no-op on
                // results — recorded only to reflect the user's declaration.
                self.use_precise_interpolation =
                    self.read_bool(key, value, BoolVocabulary::Converter);
            }
            "allow_pipe_separator" => {
                // This option is deprecated in Python beancount
                self.warn_if_deprecated(key, value);
                self.allow_pipe_separator = self.read_bool(key, value, BoolVocabulary::Converter);
            }
            "insert_pythonpath" => {
                // A boolean with the converter in beancount. rledger records
                // the value as written (it has no field), but reports an
                // unrecognized word as the other booleans do.
                self.read_bool(key, value, BoolVocabulary::Converter);
                self.custom.insert(key.to_string(), value.to_string());
            }
            "long_string_maxlines" => {
                // beancount has no converter for this option and its lexer
                // never reads it (3.2.3), so any value is accepted there with
                // no diagnostic (#2925). rledger does not read it either: a
                // value that is not a count is accepted and leaves the field
                // as it was.
                if let Ok(n) = value.parse::<u32>() {
                    self.long_string_maxlines = n;
                }
            }
            "documents" => {
                // NO existence check here. A relative `documents` path is
                // relative to the LEDGER FILE, as it is in beancount and as
                // `include` is — and option parsing does not know where that
                // file is. `Path::new(value).exists()` therefore asked about
                // the process CWD, so `rledger check path/to/ledger` reported
                // E7006 for a document root that was present (#1999), while
                // `query` — which resolves through `resolve_document_dirs` —
                // found it.
                //
                // The check now happens where the source map exists, in
                // `Loader::load`, through that same canonical resolver.
                self.documents.push(value.to_string());
            }
            "plugin_processing_mode" => {
                // Valid values are "default" and "raw" (case-sensitive, like Python)
                if value != "default" && value != "raw" {
                    return self.reject("E7002", key, value, format!("Invalid value '{value}'"));
                }
                self.plugin_processing_mode = value.to_string();
            }
            _ => {
                // Unknown options go to custom map
                self.custom.insert(key.to_string(), value.to_string());
            }
        }
        true
    }

    /// Get a custom option value.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.custom.get(key).map(String::as_str)
    }

    /// Config-aware [`rustledger_core::AccountTypes`] classifier honoring the
    /// `name_*` renames. Consumers that route or sign accounts by root type
    /// must use this, not the rename-blind `ACCOUNT_TYPES` defaults.
    #[must_use]
    pub fn to_account_types(&self) -> rustledger_core::AccountTypes {
        rustledger_core::AccountTypes {
            assets: self.name_assets.clone(),
            liabilities: self.name_liabilities.clone(),
            equity: self.name_equity.clone(),
            income: self.name_income.clone(),
            expenses: self.name_expenses.clone(),
        }
    }

    /// The options a plugin is given: the ledger's operating currencies,
    /// title, account roots and tolerance options.
    ///
    /// The one place every host that runs plugins over a loaded ledger
    /// builds them from, so a new field cannot reach one surface and not
    /// another: a plugin given defaults misjudges a ledger that renames its
    /// roots (#1964) or sets its tolerances (#2653), silently.
    #[cfg(feature = "plugins")]
    #[must_use]
    pub fn plugin_options(&self) -> rustledger_plugin::PluginOptions {
        // Sorted, so a plugin sees the same input on every run: the map's
        // order is not stable.
        let mut inferred_tolerance_default: Vec<(String, String)> = self
            .inferred_tolerance_default
            .iter()
            .map(|(currency, number)| (currency.clone(), number.to_string()))
            .collect();
        inferred_tolerance_default.sort();
        rustledger_plugin::PluginOptions {
            operating_currencies: self.operating_currency.clone(),
            title: self.title.clone(),
            account_types: rustledger_plugin::PluginAccountTypes {
                assets: self.name_assets.clone(),
                liabilities: self.name_liabilities.clone(),
                equity: self.name_equity.clone(),
                income: self.name_income.clone(),
                expenses: self.name_expenses.clone(),
            },
            inferred_tolerance_default,
            tolerance_multiplier: self.inferred_tolerance_multiplier.to_string(),
            infer_tolerance_from_cost: self.infer_tolerance_from_cost,
        }
    }

    /// Get all account type prefixes.
    #[must_use]
    pub fn account_types(&self) -> [&str; 5] {
        [
            &self.name_assets,
            &self.name_liabilities,
            &self.name_equity,
            &self.name_income,
            &self.name_expenses,
        ]
    }

    /// beancount's `is_valid_leaf`: one or more account components, with no
    /// root required, as the account-name options take them (#2408), EVERY
    /// component a full match of `ACC_COMP_NAME_RE` (so `Conv:😀` and
    /// `Rounding:éclair` are rejected, as there, #2906).
    ///
    /// Checked by running the canonical strict predicate,
    /// [`rustledger_parser::is_valid_account_name_strict`], on
    /// `Assets:<leaf>`, so a leaf is valid exactly when it can extend a real
    /// account under beancount's `account.is_valid` (with the `\p{Lo}` /
    /// `\p{Lt}` start of #816).
    fn is_valid_leaf(value: &str) -> bool {
        rustledger_parser::is_valid_account_name_strict(&format!("Assets:{value}"))
    }

    /// beancount's `is_valid_root`, for a `name_*` option value: a single
    /// component that fully matches `ACC_COMP_TYPE_RE` (so `A😀` is rejected,
    /// as there). Checked by running the canonical strict predicate on
    /// `value:X`: a root is valid exactly when it can head a real account.
    fn is_valid_account_root(value: &str) -> bool {
        !value.contains(':')
            && rustledger_parser::is_valid_account_name_strict(&format!("{value}:X"))
    }
}

#[cfg(test)]
mod tests {

    /// The phase both surfaces report for option warnings.
    ///
    /// Pinned because two consumers read it and the point of moving it here
    /// was that neither should be choosing it. A change to the value should
    /// have to be deliberate.
    #[test]
    fn option_warnings_are_reported_in_the_parse_phase() {
        let warning = OptionWarning {
            code: "E7009",
            message: String::new(),
            option: String::new(),
            value: String::new(),
            site: None,
        };
        assert_eq!(warning.phase(), "parse");
    }

    /// The one rule both `rledger check` and the LSP read (#2291).
    ///
    /// Enumerated rather than spot-checked: the bug was a consumer holding a
    /// second, shorter copy of this list, and a test that only checked the two
    /// warnings would not notice a code quietly moving out of the error class.
    #[test]
    fn only_e7003_and_e7009_are_warnings() {
        let warn = |code: &'static str| OptionWarning {
            code,
            message: String::new(),
            option: String::new(),
            value: String::new(),
            site: None,
        };

        for code in ["E7003", "E7009", "E7010", "E7011"] {
            assert!(
                !warn(code).is_error(),
                "{code} must stay a warning; `rledger check` exits 0 on it"
            );
        }
        for code in ["E7001", "E7002", "E7004", "E7005", "E7006", "E7008"] {
            assert!(
                warn(code).is_error(),
                "{code} must stay an error; `rledger check` exits non-zero on it"
            );
        }
    }
    use super::*;
    use std::str::FromStr;

    /// Every known option has a value kind, so `doctor list-options`, which
    /// prints the loader's list, can never print one without a type.
    #[test]
    fn test_option_value_kind_covers_every_known_option() {
        for key in known_options() {
            assert!(option_value_kind(key).is_some(), "{key} has no kind");
        }
        assert_eq!(option_value_kind("experiment_explicit_tolerances"), None);
        assert_eq!(option_value_kind("insert_pythonpath"), Some("bool"));
        assert!(is_read_only_option("plugin") && is_read_only_option("filename"));
    }

    /// Drift guard between `option_value_kind` and `Options::apply`: a value
    /// of each option's declared kind is accepted with no value diagnostic,
    /// so the kind `doctor list-options` prints cannot disagree with what
    /// `set` takes (#2925 review). A read-only option is E7005 instead.
    #[test]
    fn test_option_value_kind_matches_what_set_accepts() {
        for &key in known_options() {
            let kind = option_value_kind(key).expect("covered above");
            let value = match kind {
                "string" => "Some text",
                "currency" => "USD",
                "account root" => "Capital",
                "account leaf" => "Rounding",
                "CURRENCY:NUMBER" => "USD:0.01",
                "decimal" => "0.6",
                "bool" => "TRUE",
                "booking method" => "FIFO",
                "any" => "not a number",
                "path" => "documents",
                "default | raw" => "raw",
                other => panic!("{key}: no representative value for kind {other:?}"),
            };
            let mut opts = Options::new();
            opts.set(key, value);
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            if is_read_only_option(key) {
                assert_eq!(codes, ["E7005"], "{key}");
            } else {
                assert!(
                    codes.iter().all(|c| *c == "E7004"),
                    "{key} = {value:?} ({kind}) must be accepted: {codes:?}"
                );
            }
        }
    }

    #[test]
    fn test_default_options() {
        let opts = Options::new();
        assert_eq!(opts.name_assets, "Assets");
        assert_eq!(opts.booking_method, "STRICT");
        assert!(!opts.infer_tolerance_from_cost);
    }

    #[test]
    fn test_set_options() {
        let mut opts = Options::new();
        opts.set("title", "My Ledger");
        opts.set("operating_currency", "USD");
        opts.set("operating_currency", "EUR");
        opts.set("booking_method", "FIFO");

        assert_eq!(opts.title, Some("My Ledger".to_string()));
        assert_eq!(opts.operating_currency, vec!["USD", "EUR"]);
        assert_eq!(opts.booking_method, "FIFO");
    }

    #[test]
    fn test_custom_options() {
        let mut opts = Options::new();
        opts.set("my_custom_option", "my_value");

        assert_eq!(opts.get("my_custom_option"), Some("my_value"));
        assert_eq!(opts.get("nonexistent"), None);
    }

    #[test]
    fn test_unknown_option_warning() {
        let mut opts = Options::new();
        opts.set("unknown_option", "value");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7001");
        assert!(opts.warnings[0].message.contains("Invalid option"));
    }

    /// #1416: the beancount 3.x `use_precise_interpolation` option must be
    /// accepted (no E7001) — rustledger already interpolates precisely.
    #[test]
    fn test_use_precise_interpolation_accepted() {
        let mut opts = Options::new();
        opts.set("use_precise_interpolation", "TRUE");

        assert!(
            opts.warnings.is_empty(),
            "should not warn on a known option: {:?}",
            opts.warnings
        );
        assert!(opts.use_precise_interpolation);
    }

    #[test]
    fn test_duplicate_option_warning() {
        let mut opts = Options::new();
        opts.set("title", "First Title");
        opts.set("title", "Second Title");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7003");
        // Wording matters here: the old text said the option "can only be
        // specified once", which is not true -- bean-check accepts a
        // redefinition and takes the last value, which is why #1546 asked for
        // this to stop being an error. Saying so is the difference between a
        // warning a reader can act on and one that looks like a rule.
        assert!(
            opts.warnings[0].message.contains("the last value wins"),
            "got: {}",
            opts.warnings[0].message,
        );
        // ...and last-wins is what actually happened.
        assert_eq!(opts.title.as_deref(), Some("Second Title"));
    }

    /// An option set in an INCLUDED file does not govern the ledger.
    ///
    /// The value-changing cases are the point. `booking_method` decides which
    /// lot a sale consumes and `inferred_tolerance_default` decides what
    /// counts as balanced, so a sub-ledger setting either used to change
    /// results for every other entity in the tree, including the master's own
    /// transactions (#2151).
    #[test]
    fn included_files_do_not_govern_scoped_options() {
        let mut opts = Options::new();
        opts.set_scoped("title", "Master", true);
        opts.set_scoped("booking_method", "LIFO", false);
        opts.set_scoped("title", "Sub-ledger", false);

        assert_eq!(
            opts.title.as_deref(),
            Some("Master"),
            "the top-level ledger names the combined result, not whichever \
             sub-ledger was included last",
        );
        assert!(
            !opts.set_options.contains("booking_method"),
            "an included booking_method must not reach the booker",
        );
        assert_eq!(opts.warnings.len(), 2, "each ignored option is reported");
        assert!(
            opts.warnings.iter().all(|w| w.code == "E7009"),
            "must not reuse E7003: that one means specified-twice-last-wins and \
             maps downstream to DuplicateOption, but an ignored option may be \
             the only one of its name in the tree",
        );
        assert!(
            opts.warnings
                .iter()
                .all(|w| w.message.contains("is ignored")),
            "the warning has to say the value was dropped, or the user cannot \
             tell why their setting had no effect",
        );
    }

    /// Scoping must not downgrade a diagnostic that already existed.
    ///
    /// `inferred_tolerance_multiplier` is deprecated and raises E7004, which
    /// `rledger check` treats as an error. Reporting only the E7009 notice
    /// would silently turn that into a warning, making an included file the
    /// one place a deprecated option stopped failing the build.
    #[test]
    fn scoping_out_an_option_still_reports_its_deprecation() {
        let mut opts = Options::new();
        opts.set_scoped("inferred_tolerance_multiplier", "0.6", false);

        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert!(
            codes.contains(&"E7004"),
            "deprecation survives scoping: {codes:?}"
        );
        assert!(
            codes.contains(&"E7009"),
            "and the ignore is still reported: {codes:?}"
        );
        assert!(
            opts.warnings
                .iter()
                .any(|w| w.code == "E7004" && w.message.contains("Renamed")),
            "the message must come from the shared table, not an empty default",
        );
    }

    fn site(file: &str, line: usize) -> OptionSite {
        OptionSite {
            file: file.to_string(),
            line,
        }
    }

    /// An invalid value in an included file is reported as its converter
    /// rejects it, at the included file's line, and nothing is applied, as
    /// bean-check 3.2.3 reports it (#2925). One case per option family whose
    /// value beancount validates and which does not cross an include.
    #[test]
    fn test_set_scoped_at_included_invalid_value_is_its_converter_error() {
        let cases: &[(&str, &str, &[&str])] = &[
            ("name_assets", "assets", &["E7008"]),
            ("name_liabilities", "liab", &["E7008"]),
            ("name_equity", "capital", &["E7008"]),
            ("name_income", "inc", &["E7008"]),
            ("name_expenses", "exp", &["E7008"]),
            ("account_rounding", "bad leaf", &["E7002"]),
            ("account_previous_balances", "bad leaf", &["E7002"]),
            ("account_previous_earnings", "bad leaf", &["E7002"]),
            ("account_previous_conversions", "bad leaf", &["E7002"]),
            ("account_current_earnings", "bad leaf", &["E7002"]),
            ("account_current_conversions", "bad leaf", &["E7002"]),
            ("account_unrealized_gains", "bad leaf", &["E7002"]),
            ("inferred_tolerance_default", "USD:-0.01", &["E7002"]),
            ("tolerance_multiplier", "abc", &["E7002"]),
            // Deprecated as well as invalid: both, as bean-check prints both.
            ("inferred_tolerance_multiplier", "abc", &["E7004", "E7002"]),
            ("booking_method", "fifo", &["E7002"]),
            ("plugin_processing_mode", "weird", &["E7002"]),
        ];
        for (key, value, expected) in cases {
            let mut opts = Options::new();
            opts.set_scoped_at(key, value, false, Some(site("sub.beancount", 7)));
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(&codes, expected, "{key} = {value:?}");
            assert!(
                opts.warnings.iter().all(OptionWarning::is_error),
                "{key}: an error, so check exits 1 as bean-check does"
            );
            assert!(
                opts.warnings
                    .iter()
                    .all(|w| w.site == Some(site("sub.beancount", 7))),
                "{key}: at the included file's line: {:?}",
                opts.warnings
            );
            assert!(
                opts.set_options.is_empty(),
                "{key}: an included value is never applied"
            );
            assert_eq!(
                opts.rejected_booking_method, None,
                "{key}: the top-level method governs, so an included rejection refuses no query"
            );
        }
    }

    /// A value the converter accepts is still ignored in an included file,
    /// with the E7009 warning at its line, and not applied (#2151, #2925).
    #[test]
    fn test_set_scoped_at_included_valid_value_is_e7009() {
        let cases: &[(&str, &str)] = &[
            ("title", "Sub"),
            ("name_equity", "Capital"),
            ("account_rounding", "Rounding"),
            ("account_previous_balances", "Opening"),
            ("inferred_tolerance_default", "USD:0.01"),
            ("tolerance_multiplier", "0.6"),
            ("booking_method", "FIFO"),
            ("render_commas", "TRUE"),
            ("infer_tolerance_from_cost", "TRUE"),
            ("use_precise_interpolation", "TRUE"),
            ("plugin_processing_mode", "raw"),
            ("long_string_maxlines", "abc"),
            ("conversion_currency", "NOTHING"),
        ];
        for (key, value) in cases {
            let mut opts = Options::new();
            opts.set_scoped_at(key, value, false, Some(site("sub.beancount", 3)));
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7009"], "{key} = {value:?}");
            assert_eq!(opts.warnings[0].site, Some(site("sub.beancount", 3)));
            assert!(!opts.warnings[0].is_error(), "{key}: a warning, exit 0");
            assert_eq!(
                opts,
                Options {
                    warnings: opts.warnings.clone(),
                    ..Options::new()
                },
                "{key}: nothing applied"
            );
        }
        // An unrecognized boolean word reads as false there too: its E7011
        // warning, then the E7009, both warnings, as bean-check is clean.
        let mut opts = Options::new();
        opts.set_scoped_at("render_commas", "bogus", false, Some(site("s", 1)));
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7011", "E7009"]);
        assert!(opts.warnings.iter().all(|w| !w.is_error()));
    }

    /// Every diagnostic an option raises carries its site, the ones raised
    /// later from the applied values too (#2925).
    #[test]
    fn test_set_scoped_at_stamps_every_diagnostic_with_its_site() {
        let mut opts = Options::new();
        opts.set_scoped_at("nosuch", "x", true, Some(site("m", 1)));
        opts.set_scoped_at("title", "a", true, Some(site("m", 2)));
        opts.set_scoped_at("title", "b", true, Some(site("m", 3)));
        opts.set_scoped_at("filename", "f", true, Some(site("m", 4)));
        opts.set_scoped_at("allow_pipe_separator", "TRUE", true, Some(site("m", 5)));
        opts.set_scoped_at(
            "account_previous_balances",
            "Equity:Open",
            true,
            Some(site("m", 6)),
        );
        opts.set_scoped_at("documents", "missing", true, Some(site("m", 7)));
        let rooted = opts.rooted_leaf_warnings();
        opts.warnings.extend(rooted);
        let mut docs = vec![OptionWarning {
            code: "E7006",
            message: String::new(),
            option: "documents".to_string(),
            value: "missing".to_string(),
            site: None,
        }];
        opts.locate(&mut docs);
        opts.warnings.extend(docs);

        let located: Vec<(&str, usize)> = opts
            .warnings
            .iter()
            .map(|w| (w.code, w.site.as_ref().map_or(0, |s| s.line)))
            .collect();
        assert_eq!(
            located,
            [
                ("E7001", 1),
                ("E7003", 3),
                ("E7005", 4),
                ("E7004", 5),
                ("E7010", 6),
                ("E7006", 7),
            ]
        );
        // `set` has no source, so its diagnostics have no site.
        let mut bare = Options::new();
        bare.set("nosuch", "x");
        assert_eq!(bare.warnings[0].site, None);
    }

    /// `option "plugin"` may not be set, as in beancount, from the top-level
    /// file or an included one: E7005, an error, and nothing applied (#2925).
    /// It used to be the deprecation E7004; scoping it out in an included
    /// file must not turn the error into the E7009 warning.
    #[test]
    fn test_set_scoped_plugin_option_is_read_only_everywhere() {
        for top_level in [true, false] {
            let mut opts = Options::new();
            opts.set_scoped("plugin", "some.module", top_level);
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7005"], "top_level = {top_level}");
            assert_eq!(opts.warnings[0].message, "Option 'plugin' may not be set");
            assert!(opts.warnings[0].is_error());
            assert!(opts.custom.is_empty() && opts.set_options.is_empty());
        }
    }

    /// Options that describe the file declaring them still accumulate.
    ///
    /// A sub-ledger naming its own operating currency or document root is
    /// describing itself rather than overriding its includer, so scoping must
    /// not swallow these.
    #[test]
    fn included_files_still_contribute_accumulating_options() {
        let mut opts = Options::new();
        opts.set_scoped("operating_currency", "USD", true);
        opts.set_scoped("operating_currency", "EUR", false);
        opts.set_scoped("documents", "docs-from-include", false);

        assert!(
            opts.operating_currency.iter().any(|c| c == "EUR"),
            "an included operating_currency must still be collected",
        );
        assert!(
            opts.documents.iter().any(|d| d == "docs-from-include"),
            "an included documents root must still be collected",
        );
    }

    #[test]
    fn test_repeatable_option_no_warning() {
        let mut opts = Options::new();
        opts.set("operating_currency", "USD");
        opts.set("operating_currency", "EUR");

        // No warnings for repeatable options
        assert!(
            opts.warnings.is_empty(),
            "Should not warn for repeatable options: {:?}",
            opts.warnings
        );
        assert_eq!(opts.operating_currency, vec!["USD", "EUR"]);
    }

    #[test]
    fn test_invalid_tolerance_value() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_multiplier", "not_a_number");

        // E7004 (deprecated name) + E7002 (invalid value)
        assert_eq!(opts.warnings.len(), 2);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(opts.warnings[0].message.contains("Renamed"));
        assert_eq!(opts.warnings[1].code, "E7002");
        assert!(
            opts.warnings[1]
                .message
                .contains("expected a decimal number")
        );
    }

    #[test]
    fn test_tolerance_multiplier_new_name() {
        let mut opts = Options::new();
        opts.set("tolerance_multiplier", "1.5");

        assert!(opts.warnings.is_empty());
        assert_eq!(opts.inferred_tolerance_multiplier, Decimal::new(15, 1));
    }

    #[test]
    fn test_inferred_tolerance_multiplier_deprecated() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_multiplier", "1.01");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(
            opts.warnings[0]
                .message
                .contains("Renamed to 'tolerance_multiplier'")
        );
        assert_eq!(
            opts.inferred_tolerance_multiplier,
            Decimal::from_str("1.01").unwrap()
        );
    }

    /// The value of a boolean option as `Options` holds it.
    fn bool_option(opts: &Options, key: &str) -> bool {
        match key {
            "render_commas" => opts.render_commas,
            "use_precise_interpolation" => opts.use_precise_interpolation,
            "allow_pipe_separator" => opts.allow_pipe_separator,
            "infer_tolerance_from_cost" => opts.infer_tolerance_from_cost,
            other => panic!("not a boolean option: {other}"),
        }
    }

    /// The options with beancount's `options_validate_boolean` converter read
    /// `1`, `true` and `yes` as true, case-insensitively, and nothing else
    /// (#2925). `render_commas "yes"` used to be an E7002 error and false.
    #[test]
    fn test_set_converter_boolean_options_read_like_beancount() {
        for key in [
            "render_commas",
            "use_precise_interpolation",
            "allow_pipe_separator",
        ] {
            for (value, expected) in [
                ("TRUE", true),
                ("true", true),
                ("1", true),
                ("yes", true),
                ("YES", true),
                ("FALSE", false),
                ("0", false),
                ("no", false),
                // `on` / `off` are the grammar branch's words, not the converter's.
                ("on", false),
                ("off", false),
            ] {
                let mut opts = Options::new();
                opts.set(key, value);
                let warns = matches!(value, "on" | "off");
                assert_eq!(
                    opts.warnings.iter().any(|w| w.code == "E7011"),
                    warns,
                    "{key} = {value:?}: {:?}",
                    opts.warnings
                );
                assert_eq!(bool_option(&opts, key), expected, "{key} = {value:?}");
            }
        }
    }

    /// `infer_tolerance_from_cost` has no converter in beancount, so
    /// `grammar.option`'s bool branch reads it: `true` and `on`
    /// case-insensitively, or `1`. So `on` is true and `yes` is not (#2925).
    #[test]
    fn test_set_infer_tolerance_from_cost_reads_like_grammar_option() {
        for (value, expected, warns) in [
            ("TRUE", true, false),
            ("1", true, false),
            ("on", true, false),
            ("ON", true, false),
            ("FALSE", false, false),
            ("0", false, false),
            ("off", false, false),
            ("yes", false, true),
        ] {
            let mut opts = Options::new();
            opts.set("infer_tolerance_from_cost", value);
            assert_eq!(opts.infer_tolerance_from_cost, expected, "{value:?}");
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            let expected_codes: &[&str] = if warns { &["E7011"] } else { &[] };
            assert_eq!(codes, expected_codes, "{value:?}");
        }
    }

    /// An unrecognized boolean word reads as false, as in beancount, and is
    /// the E7011 WARNING, not an error, so `check` passes as bean-check does
    /// (a decision on #2925). The word is still applied: a later `bogus`
    /// turns an earlier `TRUE` off, as it does in beancount.
    #[test]
    fn test_set_unrecognized_boolean_word_is_false_with_a_warning() {
        for key in ["render_commas", "infer_tolerance_from_cost"] {
            let mut opts = Options::new();
            opts.set(key, "TRUE");
            opts.set(key, "bogus");
            assert!(!bool_option(&opts, key), "{key}");
            let w = opts
                .warnings
                .iter()
                .find(|w| w.code == "E7011")
                .unwrap_or_else(|| panic!("{key}: expected E7011: {:?}", opts.warnings));
            assert!(!w.is_error(), "E7011 must not fail `check`");
            assert!(
                w.message.contains("reads as false"),
                "the message says what the value does: {}",
                w.message
            );
            assert!(opts.warnings.iter().all(|w| w.code != "E7002"), "{key}");
        }
    }

    /// `insert_pythonpath` has the converter too, so a typo is reported the
    /// same way; its value is still recorded as written.
    #[test]
    fn test_set_insert_pythonpath_unrecognized_word_warns() {
        let mut opts = Options::new();
        opts.set("insert_pythonpath", "TRUE");
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
        opts.set("insert_pythonpath", "maybe");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7011"]);
        assert_eq!(opts.get("insert_pythonpath"), Some("maybe"));
    }

    /// The option vocabularies are not `parse_bool_word`, which serves
    /// `render_commas:` metadata: that one must not move with them (#2925).
    #[test]
    fn test_set_boolean_options_leave_metadata_vocabulary_alone() {
        assert_eq!(rustledger_core::parse_bool_word("yes"), None);
        assert_eq!(rustledger_core::parse_bool_word("on"), None);
        assert_eq!(rustledger_core::parse_bool_word("TRUE"), Some(true));
        let mut opts = Options::new();
        opts.set("render_commas", "yes");
        assert!(opts.render_commas);
    }

    /// #2401: the previous-period summary accounts resolve under the
    /// ledger's own equity root when unset, and are the name written when set.
    #[test]
    fn previous_summary_accounts_resolve_under_the_equity_root() {
        let defaults = Options::new();
        assert_eq!(
            defaults.previous_balances_account(),
            "Equity:Opening-Balances"
        );
        assert_eq!(
            defaults.previous_earnings_account(),
            "Equity:Earnings:Previous"
        );
        assert_eq!(
            defaults.previous_conversions_account(),
            "Equity:Conversions:Previous"
        );

        let mut renamed = Options::new();
        renamed.set("name_equity", "Eigenkapital");
        assert_eq!(
            renamed.previous_balances_account(),
            "Eigenkapital:Opening-Balances"
        );
        assert_eq!(
            renamed.previous_earnings_account(),
            "Eigenkapital:Earnings:Previous"
        );
        assert_eq!(
            renamed.previous_conversions_account(),
            "Eigenkapital:Conversions:Previous"
        );

        // Set: a leaf under the equity root, as beancount reads it (#2408).
        let mut set = Options::new();
        set.set("name_equity", "Eigenkapital");
        set.set("account_previous_balances", "Anfang");
        set.set("account_previous_earnings", "Vorjahr");
        set.set("account_previous_conversions", "Umrechnung");
        assert_eq!(set.previous_balances_account(), "Eigenkapital:Anfang");
        assert_eq!(set.previous_earnings_account(), "Eigenkapital:Vorjahr");
        assert_eq!(
            set.previous_conversions_account(),
            "Eigenkapital:Umrechnung"
        );
    }

    /// #2406: the current-period accounts and the conversion currency resolve
    /// the same way: under the equity root when unset, as written when set.
    #[test]
    fn current_summary_accounts_and_conversion_currency_resolve() {
        let defaults = Options::new();
        assert_eq!(
            defaults.current_earnings_account(),
            "Equity:Earnings:Current"
        );
        assert_eq!(
            defaults.current_conversions_account(),
            "Equity:Conversions:Current"
        );
        assert_eq!(defaults.conversion_currency_or_default(), "NOTHING");

        let mut renamed = Options::new();
        renamed.set("name_equity", "Eigenkapital");
        assert_eq!(
            renamed.current_earnings_account(),
            "Eigenkapital:Earnings:Current"
        );
        assert_eq!(
            renamed.current_conversions_account(),
            "Eigenkapital:Conversions:Current"
        );

        let mut set = Options::new();
        set.set("name_equity", "Eigenkapital");
        set.set("account_current_earnings", "Laufend");
        set.set("account_current_conversions", "Umrechnung:Laufend");
        set.set("conversion_currency", "EUR");
        assert_eq!(set.current_earnings_account(), "Eigenkapital:Laufend");
        assert_eq!(
            set.current_conversions_account(),
            "Eigenkapital:Umrechnung:Laufend"
        );
        assert_eq!(set.conversion_currency_or_default(), "EUR");
    }

    /// #2408: a value written as a full name (rledger's old documented form)
    /// resolves as beancount resolves it, the equity root joined on, and
    /// raises E7010 naming what to write instead. A warning, not an error:
    /// the value is legal beancount.
    #[test]
    fn a_rooted_account_option_resolves_like_beancount_and_warns() {
        let mut opts = Options::new();
        opts.set("account_previous_balances", "Equity:Anfang");
        opts.set("account_current_earnings", "Income:Oops");
        assert!(
            opts.warnings.is_empty(),
            "legal leaves: {:?}",
            opts.warnings
        );
        assert_eq!(opts.previous_balances_account(), "Equity:Equity:Anfang");
        assert_eq!(opts.current_earnings_account(), "Equity:Income:Oops");

        let warnings = opts.rooted_leaf_warnings();
        assert_eq!(warnings.len(), 2, "{warnings:?}");
        assert!(warnings.iter().all(|w| w.code == "E7010" && !w.is_error()));
        assert!(
            warnings[0].message.contains("\"Equity:Equity:Anfang\"")
                && warnings[0].message.contains("write \"Anfang\""),
            "{}",
            warnings[0].message
        );

        // Against the ledger's own root names, whenever `name_*` was set.
        let mut renamed = Options::new();
        renamed.set("account_previous_balances", "Eigenkapital:Anfang");
        renamed.set("name_equity", "Eigenkapital");
        assert_eq!(renamed.rooted_leaf_warnings().len(), 1);
        assert_eq!(
            renamed.previous_balances_account(),
            "Eigenkapital:Eigenkapital:Anfang"
        );

        // The advice depends on which root. Only the EQUITY root can be
        // dropped to keep the account meant; a value that is the root itself,
        // or another root's account, cannot be written as a leaf at all.
        let advice = |value: &str| {
            let mut opts = Options::new();
            opts.set("account_previous_balances", value);
            opts.rooted_leaf_warnings()[0].message.clone()
        };
        assert!(advice("Equity:Anfang").ends_with("write \"Anfang\" for Equity:Anfang"));
        assert!(
            advice("Equity").ends_with("not the root itself"),
            "{}",
            advice("Equity")
        );
        let other = advice("Income:Oops");
        assert!(
            other.contains("\"Equity:Income:Oops\"")
                && other.ends_with("so it cannot name an account under Income")
                && !other.contains("write"),
            "{other}"
        );

        // Defaults and ordinary leaves raise nothing.
        assert!(Options::new().rooted_leaf_warnings().is_empty());
        let mut leaf = Options::new();
        leaf.set("account_previous_balances", "Anfang");
        assert!(leaf.rooted_leaf_warnings().is_empty());
    }

    #[test]
    fn test_invalid_booking_method() {
        let mut opts = Options::new();
        opts.set("booking_method", "RANDOM");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("STRICT"));
    }

    #[test]
    fn test_valid_booking_methods() {
        for method in &["STRICT", "FIFO", "LIFO", "AVERAGE", "NONE"] {
            let mut opts = Options::new();
            opts.set("booking_method", method);
            assert!(
                opts.warnings.is_empty(),
                "Should accept {method} as valid booking method"
            );
        }
    }

    #[test]
    fn test_readonly_option_warning() {
        let mut opts = Options::new();
        opts.set("filename", "/some/path.beancount");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7005");
        assert!(opts.warnings[0].message.contains("may not be set"));
    }

    /// A valid `account_rounding` is stored and gives no diagnostic, as in
    /// beancount 3.2.3, where the option is inert (#2925). It used to raise
    /// the E7007 error, which made `check` fail a ledger bean-check passes.
    #[test]
    fn test_set_account_rounding_valid_value_no_diagnostic() {
        let mut opts = Options::new();
        opts.set("account_rounding", "Equity:Rounding");

        assert_eq!(opts.account_rounding.as_deref(), Some("Equity:Rounding"));
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
    }

    #[test]
    fn test_invalid_account_name_validation() {
        // account_rounding with an invalid value: only the invalid-account
        // error (E7002), as in beancount (#2911).
        let mut opts = Options::new();
        opts.set("account_rounding", "invalid");

        assert_eq!(opts.warnings.len(), 1, "{:?}", opts.warnings);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("Invalid leaf account"));
        assert_eq!(opts.account_rounding, None);
    }

    #[test]
    fn test_valid_account_name() {
        let mut opts = Options::new();
        opts.set("account_rounding", "Equity:Rounding");

        // A valid account name does not trip E7002; the value is stored.
        assert!(!opts.warnings.iter().any(|w| w.code == "E7002"));
        assert_eq!(opts.account_rounding, Some("Equity:Rounding".to_string()));
    }

    #[test]
    fn test_render_commas_with_numeric_values() {
        let mut opts = Options::new();
        opts.set("render_commas", "1");
        assert!(opts.render_commas);
        assert!(opts.warnings.is_empty());

        let mut opts2 = Options::new();
        opts2.set("render_commas", "0");
        assert!(!opts2.render_commas);
        assert!(opts2.warnings.is_empty());
    }

    #[test]
    fn test_plugin_processing_mode_validation() {
        // Valid values
        let mut opts = Options::new();
        opts.set("plugin_processing_mode", "default");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.plugin_processing_mode, "default");

        let mut opts2 = Options::new();
        opts2.set("plugin_processing_mode", "raw");
        assert!(opts2.warnings.is_empty());
        assert_eq!(opts2.plugin_processing_mode, "raw");

        // Invalid value
        let mut opts3 = Options::new();
        opts3.set("plugin_processing_mode", "invalid");
        assert_eq!(opts3.warnings.len(), 1);
        assert_eq!(opts3.warnings[0].code, "E7002");
    }

    /// The two options beancount 3.2.3 no longer has are unknown, E7001, as
    /// beancount's "Invalid option" (#2925). They used to be accepted
    /// silently, with no effect.
    #[test]
    fn test_set_dead_tolerance_options_are_unknown() {
        for key in [
            "experiment_explicit_tolerances",
            "use_legacy_fixed_tolerances",
        ] {
            let mut opts = Options::new();
            opts.set(key, "TRUE");
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7001"], "{key}");
            assert!(opts.warnings[0].is_error(), "{key}");
        }
    }

    /// `long_string_maxlines` has no converter in beancount and nothing reads
    /// it, so any value is accepted with no diagnostic (#2925). A count is
    /// recorded; anything else leaves the field as it was.
    #[test]
    fn test_set_long_string_maxlines_accepts_any_value() {
        let mut opts = Options::new();
        opts.set("long_string_maxlines", "10");
        opts.set("long_string_maxlines", "abc");
        assert!(
            opts.warnings.iter().all(|w| w.code == "E7003"),
            "{:?}",
            opts.warnings
        );
        assert_eq!(opts.long_string_maxlines, 10);
    }

    #[test]
    fn test_deprecated_allow_pipe_separator() {
        let mut opts = Options::new();
        opts.set("allow_pipe_separator", "true");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(opts.warnings[0].message.contains("deprecated"));
    }

    #[test]
    fn test_is_valid_leaf() {
        // beancount's `is_valid_leaf` (#2408): one or more components, no
        // root required.
        assert!(Options::is_valid_leaf("Opening-Balances"));
        assert!(Options::is_valid_leaf("Earnings:Previous"));
        assert!(Options::is_valid_leaf("Anfang"));
        // A value that happens to start with a root is a legal leaf too (it
        // resolves under the equity root and raises E7010, not E7002).
        assert!(Options::is_valid_leaf("Equity:Rounding:Precision"));
        assert!(Options::is_valid_leaf("Капитал:Retained"));
        assert!(Options::is_valid_leaf("银行:支票"));

        assert!(!Options::is_valid_leaf("anfang")); // Lowercase ASCII
        assert!(!Options::is_valid_leaf("Bad Name")); // Space
        assert!(!Options::is_valid_leaf("Anfang:")); // Empty component
        assert!(!Options::is_valid_leaf(":Anfang")); // Empty first component
        assert!(!Options::is_valid_leaf("")); // Nothing
        // Every component is a full `ACC_COMP_NAME_RE` match in beancount
        // (#2906): bean-check reports `Invalid leaf account name` for these.
        assert!(!Options::is_valid_leaf("Conv:\u{1F600}"));
        assert!(!Options::is_valid_leaf("Rounding:\u{e9}clair"));
        assert!(!Options::is_valid_leaf("Conv\u{1F600}"));
        assert!(!Options::is_valid_leaf("Conv:A_b"));
        // ...and accepts these.
        assert!(Options::is_valid_leaf("\u{663}"));
        assert!(Options::is_valid_leaf("Conv:\u{663}"));
        assert!(Options::is_valid_leaf("Conv:A-b"));
    }

    #[test]
    fn test_account_validation_options() {
        // Test all account options that require validation
        let account_options = [
            "account_rounding",
            "account_current_conversions",
            "account_unrealized_gains",
            "account_previous_balances",
            "account_previous_earnings",
            "account_previous_conversions",
            "account_current_earnings",
        ];

        for opt in account_options {
            let mut opts = Options::new();
            opts.set(opt, "lowercase:invalid");

            assert!(
                !opts.warnings.is_empty(),
                "Option '{opt}' should warn on invalid account name"
            );
            assert_eq!(opts.warnings[0].code, "E7002");
        }
    }

    /// Both tolerance-map options split on the LAST colon followed by a
    /// number, as beancount's `(.*):([\d\.]+)` does, so `A:B:0.01` is currency
    /// `A:B` (#2925). It used to be rejected.
    #[test]
    fn test_parse_tolerance_map_splits_on_last_colon_before_number() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_default", "A:B:0.01");
        opts.set("display_precision", "A:B:0.001");
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
        assert_eq!(
            opts.inferred_tolerance_default.get("A:B"),
            Some(&rust_decimal_macros::dec!(0.01))
        );
        assert_eq!(opts.display_precision.get("A:B"), Some(&3));

        // The number is digits and dots, so a leading dot is one.
        assert_eq!(
            parse_tolerance_map("USD:.5"),
            Ok(("USD", rust_decimal_macros::dec!(0.5)))
        );
        // The last colon followed by a number, not merely the last colon.
        assert_eq!(
            parse_tolerance_map("X:1y:2"),
            Ok(("X:1y", rust_decimal_macros::dec!(2)))
        );
    }

    /// A sign is not part of beancount's number, so a negative tolerance or
    /// precision is rejected with E7002 and not applied (#2925). It used to
    /// be accepted.
    #[test]
    fn test_parse_tolerance_map_rejects_sign() {
        for key in ["inferred_tolerance_default", "display_precision"] {
            for value in ["USD:-0.01", "USD:+0.01", "USD", "USD:", "USD:1.2.3"] {
                let mut opts = Options::new();
                opts.set(key, value);
                let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
                assert_eq!(codes, ["E7002"], "{key} = {value:?}");
                assert!(opts.inferred_tolerance_default.is_empty());
                assert!(opts.display_precision.is_empty());
            }
        }
    }

    /// Deliberate deviation: beancount reads `USD:0.01abc` as 0.01 USD
    /// because its `re.match` ignores what follows the number. rledger keeps
    /// rejecting it with E7002 (a decision on #2925).
    #[test]
    fn test_parse_tolerance_map_trailing_text_is_rejected() {
        for key in ["inferred_tolerance_default", "display_precision"] {
            let mut opts = Options::new();
            opts.set(key, "USD:0.01abc");
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7002"], "{key}");
            assert!(
                opts.warnings[0].message.contains("'abc'"),
                "names the stray text: {}",
                opts.warnings[0].message
            );
            assert!(opts.inferred_tolerance_default.is_empty());
            assert!(opts.display_precision.is_empty());
        }
    }

    /// The same deviation covers an exponent: beancount reads `USD:1e-2` as
    /// 1 (the `e-2` is ignored), rledger rejects it.
    #[test]
    fn test_parse_tolerance_map_exponent_is_rejected() {
        let err = parse_tolerance_map("USD:1e-2").expect_err("trailing exponent");
        assert!(err.contains("'e-2'"), "{err}");
    }

    /// beancount's `(.*)` does not cross a newline, so the colon must be on
    /// the first line: `"A\nB:0.5"` is invalid there and here.
    #[test]
    fn test_parse_tolerance_map_colon_after_newline_is_rejected() {
        assert!(parse_tolerance_map("A\nB:0.5").is_err());
        let mut opts = Options::new();
        opts.set("inferred_tolerance_default", "A\nB:0.5");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7002"]);
    }

    /// Not fixable locally (deviation 3): a number `rust_decimal` cannot hold
    /// exactly, and a non-ASCII digit Python's `\d` would match, are rejected
    /// rather than rounded. beancount holds `0.000...01` (31 places) as 1E-31.
    #[test]
    fn test_parse_tolerance_map_unrepresentable_number_is_rejected() {
        for value in [
            "USD:123456789012345678901234567890",
            "USD:0.0000000000000000000000000000001",
            "USD:\u{661}",
        ] {
            assert!(parse_tolerance_map(value).is_err(), "{value:?}");
            let mut opts = Options::new();
            opts.set("display_precision", value);
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7002"], "{value:?}");
        }
        // The written scale is kept where it fits: display_precision reads it.
        assert_eq!(
            parse_tolerance_map("USD:0.010").map(|(_, d)| d.scale()),
            Ok(3)
        );
    }

    /// Trailing whitespace after the number is ignored, as beancount ignores
    /// everything after it; deviation 2 is about other text only.
    #[test]
    fn test_parse_tolerance_map_trailing_whitespace_is_accepted() {
        for value in ["USD:0.5 ", "USD:0.5\n", "USD:0.5\t", "USD:0.5 \r\n"] {
            assert_eq!(
                parse_tolerance_map(value),
                Ok(("USD", rust_decimal_macros::dec!(0.5))),
                "{value:?}"
            );
        }
        for value in ["USD:0.5 x", "USD:0.5\nx"] {
            assert!(parse_tolerance_map(value).is_err(), "{value:?}");
        }
    }

    /// `tolerance_multiplier` is read by beancount's `D()` (#2925): empty is
    /// 0, commas, spaces and every `_` are stripped, and a sign and an exponent
    /// are accepted.
    #[test]
    fn test_parse_beancount_decimal_matches_d() {
        use rust_decimal_macros::dec;
        for (value, expected) in [
            ("", dec!(0)),
            ("0", dec!(0)),
            ("0.5", dec!(0.5)),
            ("1,000", dec!(1000)),
            ("1,000.25", dec!(1000.25)),
            (" 0.5 ", dec!(0.5)),
            ("1e-3", dec!(0.001)),
            ("1E2", dec!(100)),
            ("2.5e+1", dec!(25)),
            ("-0.5", dec!(-0.5)),
            ("+0.5", dec!(0.5)),
            (".5", dec!(0.5)),
            ("5.", dec!(5)),
            ("1_000", dec!(1000)),
            // CPython's `Decimal` drops every `_`, wherever it sits.
            ("1__0", dec!(10)),
            ("1_", dec!(1)),
            ("_1", dec!(1)),
            ("1._5", dec!(1.5)),
            ("._5", dec!(0.5)),
            ("1e_1", dec!(10)),
            ("1_e1", dec!(10)),
            // A zero significand is zero at any exponent.
            ("0e100", dec!(0)),
            ("0E-50", dec!(0)),
            ("-0e5", dec!(0)),
        ] {
            assert_eq!(parse_beancount_decimal(value), Ok(expected), "{value:?}");
        }
        for value in [
            "abc", "0.5abc", ",", "  ", "_", "__", "1e", "e3", ".", "1.2.3",
        ] {
            assert!(parse_beancount_decimal(value).is_err(), "{value:?}");
        }
    }

    /// Not fixable locally (deviation 3 on #2925): a value `rust_decimal`
    /// cannot hold exactly, which Python's `Decimal` holds, is rejected rather
    /// than rounded, and so are non-ASCII digits, which Python reads.
    #[test]
    fn test_parse_beancount_decimal_unrepresentable_is_rejected() {
        for value in [
            "1e100",
            "1e-29",
            "123456789012345678901234567890",
            "0.0000000000000000000000000000001",
            "\u{661}",
            "\u{ff11}",
        ] {
            assert!(parse_beancount_decimal(value).is_err(), "{value:?}");
            let mut opts = Options::new();
            opts.set("tolerance_multiplier", value);
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7002"], "{value:?}");
        }
    }

    /// The range is checked on the value, not the exponent: these are in
    /// range however they are written.
    #[test]
    fn test_parse_beancount_decimal_in_range_by_value() {
        use rust_decimal_macros::dec;
        for (value, expected) in [
            ("10e-29", dec!(0.0000000000000000000000000001)),
            ("0.1e29", dec!(10000000000000000000000000000)),
            (
                "10000000000000000000000000000",
                dec!(10000000000000000000000000000),
            ),
            ("1e-28", dec!(0.0000000000000000000000000001)),
            ("-2.5e1", dec!(-25)),
        ] {
            assert_eq!(parse_beancount_decimal(value), Ok(expected), "{value:?}");
        }
    }

    /// A value whose coefficient is past 96 bits only because of trailing
    /// zeros is held, by dropping them: bean-check and main accept these.
    #[test]
    fn test_exact_decimal_drops_trailing_zeros_past_96_bits() {
        use rust_decimal_macros::dec;
        for (value, expected) in [
            (
                "1000000000000000000000000000.00",
                dec!(1000000000000000000000000000),
            ),
            (
                "10000000000000000000000000000.0",
                dec!(10000000000000000000000000000),
            ),
            ("79228162514264337593543950335.0", Decimal::MAX),
            // 29 digits, so `must_pop` drops nothing: only the 96-bit loop
            // brings these under 2^96 - 1.
            (
                "8000000000000000000000000000.0",
                dec!(8000000000000000000000000000),
            ),
            (
                "9999999999999999999999999999.0",
                dec!(9999999999999999999999999999),
            ),
            (
                "7922816251426433759354395034.0",
                dec!(7922816251426433759354395034),
            ),
        ] {
            assert_eq!(parse_beancount_decimal(value), Ok(expected), "{value}");
            assert_eq!(
                parse_tolerance_map(&format!("USD:{value}")),
                Ok(("USD", expected)),
                "{value}"
            );
        }
        // The same 29-digit coefficient, reached through an exponent.
        assert_eq!(
            parse_beancount_decimal("80000000000000000000000000000e-1"),
            Ok(dec!(8000000000000000000000000000))
        );
        // Past 96 bits with no trailing zero to drop: not held.
        assert!(parse_beancount_decimal("79228162514264337593543950336").is_err());
    }

    /// `exact_decimal` is linear in the value's length: the value is untrusted
    /// ledger text, and the LSP reads it on every edit. A version that
    /// rescanned the leading zeros per trailing zero took 30 s here.
    #[test]
    fn test_exact_decimal_is_linear_on_long_input() {
        let zeros = "0".repeat(160_000);
        let value = format!("USD:{zeros}1{zeros}");
        let multiplier = format!("{zeros}1{zeros}");
        let start = std::time::Instant::now();
        assert!(parse_tolerance_map(&value).is_err());
        assert!(parse_beancount_decimal(&multiplier).is_err());
        let fraction = format!("USD:0.{zeros}");
        assert_eq!(
            parse_tolerance_map(&fraction).map(|(_, d)| d.scale()),
            Ok(28)
        );
        assert!(
            start.elapsed() < std::time::Duration::from_secs(2),
            "took {:?}",
            start.elapsed()
        );
    }

    /// A zero is 0 at any exponent Python's `Decimal` can build, and an error
    /// past that, as bean-check reports `0e99999999999999999999`.
    #[test]
    fn test_parse_beancount_decimal_zero_exponent_bounds() {
        for value in [
            "0e999999999999999999",
            "0e-1000000000000000000",
            "0.00e100",
            "0e-1999999999999999997",
        ] {
            assert_eq!(parse_beancount_decimal(value), Ok(Decimal::ZERO), "{value}");
        }
        for value in [
            "0e1000000000000000000",
            "0e99999999999999999999",
            "0e-1999999999999999998",
        ] {
            assert!(parse_beancount_decimal(value).is_err(), "{value}");
        }
    }

    /// Whitespace is Python's `str.isspace`, not only ASCII: `Decimal(str)`
    /// strips it, and a tolerance map ignores it after the number.
    #[test]
    fn test_parse_beancount_decimal_strips_python_whitespace() {
        use rust_decimal_macros::dec;
        for value in ["\u{c}0.5\u{a0}", "\u{1c}0.5\u{1f}", "\t0.5\n", "1 000"] {
            let expected = if value == "1 000" {
                dec!(1000)
            } else {
                dec!(0.5)
            };
            assert_eq!(parse_beancount_decimal(value), Ok(expected), "{value:?}");
        }
        for value in ["USD:0.5\u{a0}", "USD:0.5\u{1c}", "USD:0.5\u{3000}"] {
            assert_eq!(
                parse_tolerance_map(value),
                Ok(("USD", dec!(0.5))),
                "{value:?}"
            );
        }
        // Whitespace is stripped before `_` is dropped, as in CPython, so
        // whitespace next to an `_` stays inside and is invalid (bean-check
        // exit 1 on each).
        for value in ["_\t1", "1\t_", "1\u{3000}_"] {
            assert!(parse_beancount_decimal(value).is_err(), "{value:?}");
        }
        // `D()` drops the ASCII space first, so `"_ 1"` is `"_1"`, which is 1
        // (bean-check exit 0).
        assert_eq!(parse_beancount_decimal("_ 1"), Ok(dec!(1)));
    }

    /// An empty `tolerance_multiplier` is 0, as beancount's `D("")` is, with
    /// no diagnostic. It used to be an E7002 error.
    #[test]
    fn test_set_tolerance_multiplier_empty_is_zero() {
        let mut opts = Options::new();
        opts.set("tolerance_multiplier", "");
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
        assert_eq!(opts.inferred_tolerance_multiplier, Decimal::ZERO);

        opts.set("tolerance_multiplier", "1,5");
        assert_eq!(opts.inferred_tolerance_multiplier, Decimal::from(15));
    }

    /// Not fixable locally: Python's `Decimal` reads `NaN` and `Infinity`,
    /// which `rust_decimal` cannot hold, so rledger rejects them with E7002
    /// and keeps the earlier value.
    #[test]
    fn test_set_tolerance_multiplier_non_finite_is_rejected() {
        for value in ["NaN", "-Infinity", "inf", "sNaN"] {
            let mut opts = Options::new();
            opts.set("tolerance_multiplier", value);
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7002"], "{value}");
            assert_eq!(opts.inferred_tolerance_multiplier, Decimal::new(5, 1));
        }
    }

    #[test]
    fn test_inferred_tolerance_default() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_default", "USD:0.005");

        assert!(opts.warnings.is_empty());
        assert_eq!(
            opts.inferred_tolerance_default.get("USD"),
            Some(&rust_decimal_macros::dec!(0.005))
        );

        // Test wildcard
        let mut opts2 = Options::new();
        opts2.set("inferred_tolerance_default", "*:0.01");
        assert!(opts2.warnings.is_empty());
        assert_eq!(
            opts2.inferred_tolerance_default.get("*"),
            Some(&rust_decimal_macros::dec!(0.01))
        );

        // Test invalid format
        let mut opts3 = Options::new();
        opts3.set("inferred_tolerance_default", "INVALID");
        assert_eq!(opts3.warnings.len(), 1);
        assert_eq!(opts3.warnings[0].code, "E7002");
    }

    #[test]
    fn test_display_precision_basic() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:0.01");
        assert!(opts.warnings.is_empty(), "warnings: {:?}", opts.warnings);
        assert_eq!(opts.display_precision.get("USD"), Some(&2));
    }

    #[test]
    fn test_display_precision_high_precision() {
        let mut opts = Options::new();
        opts.set("display_precision", "BTC:0.00000001");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.display_precision.get("BTC"), Some(&8));
    }

    #[test]
    fn test_display_precision_zero_decimals() {
        // "JPY:1" → no fractional digits → precision 0.
        let mut opts = Options::new();
        opts.set("display_precision", "JPY:1");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.display_precision.get("JPY"), Some(&0));
    }

    #[test]
    fn test_display_precision_repeatable_per_currency() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:0.01");
        opts.set("display_precision", "EUR:0.001");
        assert!(opts.warnings.is_empty(), "warnings: {:?}", opts.warnings);
        assert_eq!(opts.display_precision.get("USD"), Some(&2));
        assert_eq!(opts.display_precision.get("EUR"), Some(&3));
    }

    #[test]
    fn test_display_precision_missing_colon_warns() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD0.01");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("CURRENCY:NUMBER"));
        assert!(opts.display_precision.is_empty());
    }

    #[test]
    fn test_name_option_invalid_root_warns_e7008() {
        // Digit-start root: no account under it could parse, so the option
        // site reports it and keeps the previous root (#2911).
        let mut opts = Options::new();
        opts.set("name_assets", "1Assets");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7008");
        assert!(opts.warnings[0].message.contains("1Assets"));
        // Rejected, as beancount rejects it: the root stays the default.
        assert_eq!(opts.name_assets, "Assets");

        // Colon inside a root can never match a root component.
        let mut opts = Options::new();
        opts.set("name_income", "In:Come");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7008");
        assert_eq!(opts.name_income, "Income");

        // A character outside `[\p{L}\p{Nd}-]` (#2906): bean-check reports
        // `Invalid root account name: 'A😀'`, although `A😀:X` lexes.
        let mut opts = Options::new();
        opts.set("name_equity", "A\u{1F600}");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7008");
        assert_eq!(opts.name_equity, "Equity");
    }

    #[test]
    fn test_name_option_valid_roots_no_warning() {
        let mut opts = Options::new();
        opts.set("name_income", "Revenue");
        opts.set("name_assets", "Activa");
        opts.set("name_expenses", "Ausgaben");
        opts.set("name_liabilities", "負債"); // caseless (\p{Lo}) root
        // Non-ASCII roots bean-check accepts (#2906).
        opts.set("name_equity", "\u{c9}quit\u{e9}"); // Équité
        assert!(
            opts.warnings.is_empty(),
            "lexable renames must not warn: {:?}",
            opts.warnings
        );
    }

    #[test]
    fn test_account_option_uses_canonical_rule() {
        // The old hand-written account check had no per-character rule:
        // 'Equity:Ro unding' style values with invalid chars slipped through
        // as long as first chars looked right. The canonical predicate
        // rejects what the lexer rejects.
        let mut opts = Options::new();
        opts.set("account_current_conversions", "Conv ersions");
        assert!(opts.warnings.iter().any(|w| w.code == "E7002"));

        let mut opts = Options::new();
        opts.set("account_current_conversions", "Conversions:Current");
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
    }

    #[test]
    fn test_display_precision_invalid_example_warns() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:abc");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("Invalid value"));
        assert!(opts.display_precision.is_empty());
    }

    /// The `name_*` options whose converter (beancount's
    /// `options_validate_root_account`) can reject a value.
    const NAME_OPTIONS: [&str; 5] = [
        "name_assets",
        "name_liabilities",
        "name_equity",
        "name_income",
        "name_expenses",
    ];

    /// The `account_*` options whose converter (beancount's
    /// `options_validate_leaf_account`) can reject a value.
    const ACCOUNT_OPTIONS: [&str; 7] = [
        "account_previous_balances",
        "account_previous_earnings",
        "account_previous_conversions",
        "account_current_earnings",
        "account_current_conversions",
        "account_unrealized_gains",
        "account_rounding",
    ];

    /// The value an option holds, for the families rejected by #2911.
    fn held(opts: &Options, key: &str) -> Option<String> {
        match key {
            "name_assets" => Some(opts.name_assets.clone()),
            "name_liabilities" => Some(opts.name_liabilities.clone()),
            "name_equity" => Some(opts.name_equity.clone()),
            "name_income" => Some(opts.name_income.clone()),
            "name_expenses" => Some(opts.name_expenses.clone()),
            "account_previous_balances" => Some(opts.account_previous_balances.clone()),
            "account_previous_earnings" => Some(opts.account_previous_earnings.clone()),
            "account_previous_conversions" => Some(opts.account_previous_conversions.clone()),
            "account_current_earnings" => Some(opts.account_current_earnings.clone()),
            "account_current_conversions" => opts.account_current_conversions.clone(),
            "account_unrealized_gains" => opts.account_unrealized_gains.clone(),
            "account_rounding" => opts.account_rounding.clone(),
            other => panic!("not an account-name option: {other}"),
        }
    }

    /// #2911: an invalid root is reported once and not applied, as beancount's
    /// `grammar.option` returns on the converter's error without assigning.
    /// The issue's example, then an empty string, a lowercase name and a
    /// colon, on every `name_*` option.
    #[test]
    fn test_set_invalid_name_option_keeps_default() {
        for key in NAME_OPTIONS {
            for bad in [
                "A\u{1F600}",
                "Cap ital",
                "",
                "revenue",
                "Exp:Sub",
                "1Assets",
            ] {
                let mut opts = Options::new();
                let before = held(&opts, key);
                opts.set(key, bad);
                let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
                assert_eq!(codes, ["E7008"], "{key}={bad:?}");
                assert_eq!(held(&opts, key), before, "{key}={bad:?} must not apply");
                assert!(
                    !opts.set_options.contains(key),
                    "{key}={bad:?}: a rejected value is not a setting"
                );
            }
        }
    }

    /// #2911: an earlier valid root survives a later invalid one, and an
    /// invalid one does not stop a later valid one from applying. Neither
    /// order is a duplicate setting: only one value was applied.
    #[test]
    fn test_set_invalid_name_option_keeps_earlier_valid_value() {
        for key in NAME_OPTIONS {
            let mut opts = Options::new();
            opts.set(key, "Capital");
            opts.set(key, "bad");
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7008"], "{key}");
            assert_eq!(held(&opts, key).as_deref(), Some("Capital"), "{key}");

            let mut opts = Options::new();
            opts.set(key, "bad");
            opts.set(key, "Capital");
            let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
            assert_eq!(codes, ["E7008"], "{key}");
            assert_eq!(held(&opts, key).as_deref(), Some("Capital"), "{key}");
        }
    }

    /// A root that collides with another root's name is a valid root, so it
    /// is applied, as in beancount (which then rejects accounts under the
    /// renamed type, not the option).
    #[test]
    fn test_set_name_option_colliding_root_is_applied() {
        let mut opts = Options::new();
        opts.set("name_income", "Assets");
        assert!(opts.warnings.is_empty(), "{:?}", opts.warnings);
        assert_eq!(opts.name_income, "Assets");
    }

    /// #2911: an invalid leaf on any `account_*` option is one E7002 and
    /// leaves the option as it was: the default, or unset where it has none.
    /// `account_rounding` raises no E7007 for a value it did not take.
    #[test]
    fn test_set_invalid_account_option_keeps_default() {
        for key in ACCOUNT_OPTIONS {
            for bad in ["bad:leaf", "", "x", "Conv ersions", "Anfang:"] {
                let mut opts = Options::new();
                let before = held(&opts, key);
                opts.set(key, bad);
                let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
                assert_eq!(codes, ["E7002"], "{key}={bad:?}");
                assert_eq!(held(&opts, key), before, "{key}={bad:?} must not apply");
                assert!(!opts.set_options.contains(key), "{key}={bad:?}");
                assert!(opts.rooted_leaf_warnings().is_empty(), "{key}={bad:?}");
            }
        }
    }

    /// #2911: an earlier valid leaf survives a later invalid one, and a later
    /// valid leaf applies after an invalid one.
    #[test]
    fn test_set_invalid_account_option_keeps_earlier_valid_value() {
        for key in ACCOUNT_OPTIONS {
            let mut opts = Options::new();
            opts.set(key, "Anfang");
            opts.set(key, "x");
            assert_eq!(held(&opts, key).as_deref(), Some("Anfang"), "{key}");
            assert!(
                !opts.warnings.iter().any(|w| w.code == "E7003"),
                "{key}: the rejected value did not win, so it is no duplicate"
            );

            let mut opts = Options::new();
            opts.set(key, "x");
            opts.set(key, "Anfang");
            assert_eq!(held(&opts, key).as_deref(), Some("Anfang"), "{key}");
            assert!(!opts.warnings.iter().any(|w| w.code == "E7003"), "{key}");
        }
        // The resolved account follows the kept leaf.
        let mut opts = Options::new();
        opts.set("account_previous_balances", "Anfang");
        opts.set("account_previous_balances", "x");
        assert_eq!(opts.previous_balances_account(), "Equity:Anfang");
    }

    /// Two ACCEPTED settings are still a duplicate, reported ahead of the
    /// second value's own diagnostics.
    #[test]
    fn test_set_two_valid_values_still_warn_duplicate() {
        let mut opts = Options::new();
        opts.set("account_rounding", "Rounding");
        opts.set("account_rounding", "Other");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7003"]);
        assert_eq!(opts.account_rounding.as_deref(), Some("Other"));
    }

    /// #2911: `booking_method`'s converter is beancount's `Booking[value]`, so
    /// an unknown or lowercase method is rejected and the earlier method kept.
    #[test]
    fn test_set_invalid_booking_method_keeps_earlier_value() {
        let mut opts = Options::new();
        opts.set("booking_method", "FIFO");
        opts.set("booking_method", "XYZ");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7002"]);
        assert_eq!(opts.booking_method, "FIFO");
        assert_eq!(
            opts.effective_booking_method(rustledger_core::BookingMethod::Strict),
            rustledger_core::BookingMethod::Fifo
        );

        let mut opts = Options::new();
        opts.set("booking_method", "fifo");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(
            codes,
            ["E7002"],
            "beancount's Booking[...] is case-sensitive"
        );
        assert_eq!(opts.booking_method, "STRICT");
        assert!(!opts.set_options.contains("booking_method"));
    }

    /// #2911: an invalid `plugin_processing_mode` keeps the earlier mode.
    #[test]
    fn test_set_invalid_plugin_processing_mode_keeps_earlier_value() {
        let mut opts = Options::new();
        opts.set("plugin_processing_mode", "raw");
        opts.set("plugin_processing_mode", "bogus");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7002"]);
        assert_eq!(opts.plugin_processing_mode, "raw");
    }

    /// #2911: the numeric options keep their earlier value on a bad one, and a
    /// map option keeps its entries. `long_string_maxlines` takes any value
    /// (#2925), so `ten` is only the duplicate E7003 and leaves the count.
    #[test]
    fn test_set_invalid_numeric_option_keeps_earlier_value() {
        let mut opts = Options::new();
        opts.set("tolerance_multiplier", "0.6");
        opts.set("tolerance_multiplier", "abc");
        opts.set("long_string_maxlines", "10");
        opts.set("long_string_maxlines", "ten");
        opts.set("inferred_tolerance_default", "USD:0.01");
        opts.set("inferred_tolerance_default", "USD:abc");
        opts.set("display_precision", "USD:0.01");
        opts.set("display_precision", "USD:abc");
        let codes: Vec<&str> = opts.warnings.iter().map(|w| w.code).collect();
        assert_eq!(codes, ["E7002", "E7003", "E7002", "E7002"]);
        assert_eq!(
            opts.inferred_tolerance_multiplier,
            rust_decimal_macros::dec!(0.6)
        );
        assert_eq!(opts.long_string_maxlines, 10);
        assert_eq!(
            opts.inferred_tolerance_default.get("USD"),
            Some(&rust_decimal_macros::dec!(0.01))
        );
        assert_eq!(opts.display_precision.get("USD"), Some(&2));
    }

    /// #2911: only a rejected `booking_method` refuses queries, only when
    /// the ledger is booked with a method other than the one its last value
    /// asks for, and the refusal names the option, its value and its line.
    #[test]
    fn test_query_refusal_only_when_booking_differs_from_the_request() {
        use rustledger_core::BookingMethod;
        let booked = |opts: &Options| opts.effective_booking_method(BookingMethod::Strict);
        let refuses = |values: &[&str]| {
            let mut opts = Options::new();
            for value in values {
                opts.set("booking_method", value);
            }
            opts.query_refusal(booked(&opts))
                .map(|r| (r.value.clone(), booked(&opts)))
        };

        // Refuses: the booking is not what the last value asks for.
        assert_eq!(
            refuses(&["fifo"]),
            Some(("fifo".to_string(), BookingMethod::Strict))
        );
        assert_eq!(
            refuses(&["bogus"]),
            Some(("bogus".to_string(), BookingMethod::Strict))
        );
        assert_eq!(
            refuses(&["FIFO", "bogus"]),
            Some(("bogus".to_string(), BookingMethod::Fifo))
        );
        // Answers: a later accepted value wins, and a rejected value that
        // reads as the method booked asks for what is booked.
        assert_eq!(refuses(&["fifo", "FIFO"]), None);
        // A later accepted value clears the rejection outright: `bogus`
        // names no method, so only the clearing lets this answer.
        assert_eq!(refuses(&["bogus", "FIFO"]), None);
        assert_eq!(refuses(&["FIFO", "fifo"]), None);
        assert_eq!(refuses(&["FIFO"]), None);

        // The message, at the option's line, names only the value as wrong.
        let mut opts = Options::new();
        opts.set_scoped_at(
            "booking_method",
            "fifo",
            true,
            Some(OptionSite {
                file: "main.beancount".to_string(),
                line: 3,
            }),
        );
        let message = opts
            .query_refusal(BookingMethod::Strict)
            .expect("refuses")
            .query_refusal_message("STRICT");
        assert_eq!(
            message,
            "option \"booking_method\" at main.beancount:3: \"fifo\" is not a booking \
             method (E7002); refusing to derive figures, which would be booked with STRICT"
        );

        let mut opts = Options::new();
        opts.set("account_rounding", "bad:leaf");
        opts.set("name_equity", "capital");
        opts.set("plugin_processing_mode", "bogus");
        assert!(
            opts.query_refusal(BookingMethod::Strict).is_none(),
            "other rejected options keep their default and answer"
        );

        // An ignored `booking_method` in an included file is not validated,
        // so it does not refuse either.
        let mut opts = Options::new();
        opts.set_scoped("booking_method", "fifo", false);
        assert!(opts.query_refusal(BookingMethod::Strict).is_none());
    }
}
