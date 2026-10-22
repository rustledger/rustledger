//! Built-in system-table builders — `#prices`, `#balances`, `#commodities`,
//! `#events`, `#notes`, `#documents`, `#accounts`, `#transactions`, `#entries`,
//! `#postings`. Extracted from the executor god-module; the `get_builtin_table`
//! dispatcher in `mod.rs` calls these. Most walk directives via
//! `Executor::resolved_directives` (so they honor the source-mapped
//! constructor); `#prices` is backed by `self.price_db` instead (itself built
//! from the directives at construction).

use super::types::{SourceLocation, Table, Value};
use super::{ColumnInfo, Executor, compute_posting_weight};
use rustc_hash::FxHashMap;
use rustledger_core::{Amount, Directive, Position};

/// A [`ColumnInfo`] in a `const` table definition.
const fn col(name: &'static str, type_name: &'static str, description: &'static str) -> ColumnInfo {
    ColumnInfo {
        name,
        type_name,
        description,
    }
}

// The columns of each system table, in order: the one definition its builder
// below creates the table from and the REPL's `.describe` prints (#2634), so
// the two cannot drift. Types use the names bean-query 0.2's `.describe` gives
// its own tables (`metadata` for a directive's `meta`, `frozenset` for a
// note's or document's tags, ...) where it has the column, and the type of the
// value rledger puts there where it does not, or where the two differ.
// `system_tables_describe_their_real_columns` checks every column against the
// values the builder produces.

/// The columns of `#prices`. bean-query's also has `meta`, which rledger's
/// price database does not keep.
pub(super) const PRICES_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Date of the price"),
    col("currency", "str", "Currency being priced"),
    col("amount", "amount", "Price, in the quote currency"),
];

/// The columns of `#balances`.
pub(super) const BALANCES_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Date of the assertion"),
    col("account", "str", "Account asserted"),
    col("amount", "amount", "Asserted balance"),
    col("tolerance", "decimal", "Explicit `~` tolerance, else NULL"),
    col(
        "discrepancy",
        "amount",
        "Computed minus asserted balance on a failing assertion, else NULL",
    ),
    col("meta", "metadata", "Directive metadata (not in `SELECT *`)"),
];

/// The columns of `#commodities`.
pub(super) const COMMODITIES_COLUMNS: &[ColumnInfo] = &[
    col("meta", "metadata", "Directive metadata"),
    col("date", "date", "Date of the declaration"),
    col("name", "str", "Commodity"),
];

/// The columns of `#events`.
pub(super) const EVENTS_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Date of the event"),
    col("type", "str", "Event type"),
    col("description", "str", "Event value"),
    col("meta", "metadata", "Directive metadata (not in `SELECT *`)"),
];

/// The columns of `#notes`.
pub(super) const NOTES_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Date of the note"),
    col("account", "str", "Account the note is attached to"),
    col("comment", "str", "Note text"),
    col("tags", "frozenset", "Note tags"),
    col("links", "frozenset", "Note links"),
    col("meta", "metadata", "Directive metadata (not in `SELECT *`)"),
];

/// The columns of `#documents`.
pub(super) const DOCUMENTS_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Date of the document"),
    col("account", "str", "Account the document is attached to"),
    col("filename", "str", "Path of the document"),
    col("tags", "frozenset", "Document tags"),
    col("links", "frozenset", "Document links"),
    col("meta", "metadata", "Directive metadata (not in `SELECT *`)"),
];

/// The columns of `#accounts`. `currencies` and `booking` are rledger's own.
pub(super) const ACCOUNTS_COLUMNS: &[ColumnInfo] = &[
    col("account", "str", "Account name"),
    col("open", "date", "Date the account was opened"),
    col("close", "date", "Date the account was closed, else NULL"),
    col("currencies", "set", "Currencies the account allows"),
    col("booking", "str", "Booking method, else NULL"),
];

/// The columns of `#transactions`.
pub(super) const TRANSACTIONS_COLUMNS: &[ColumnInfo] = &[
    col("date", "date", "Transaction date"),
    col("flag", "str", "Transaction flag"),
    col("payee", "str", "Payee, else NULL"),
    col("narration", "str", "Narration"),
    col("tags", "set", "Transaction tags"),
    col("links", "set", "Transaction links"),
    col(
        "accounts",
        "set[str]",
        "Accounts of the transaction's postings",
    ),
    col(
        "meta",
        "metadata",
        "Transaction metadata (not in `SELECT *`)",
    ),
];

/// The columns of the `#entries` table, in order: one row per directive,
/// whatever its type, as beanquery's `entries` table. `PRINT`'s FROM filter
/// reads an entry through them too. `id` is an `int` here, where
/// bean-query's is a `str` hash, as in [`POSTING_COLUMNS`](super::POSTING_COLUMNS).
pub(super) const ENTRIES_COLUMNS: &[ColumnInfo] = &[
    col("id", "int", "Directive index"),
    col("type", "str", "Directive type"),
    col("filename", "str", "Source file"),
    col("lineno", "int", "Source line"),
    col("date", "date", "Directive date"),
    col("year", "int", "Year of the date"),
    col("month", "int", "Month of the date"),
    col("day", "int", "Day of the date"),
    col("flag", "str", "Transaction flag, else NULL"),
    col("payee", "str", "Transaction payee, else NULL"),
    col("narration", "str", "Transaction narration, else NULL"),
    col("description", "str", "`payee | narration`, else NULL"),
    col("tags", "set", "Tags"),
    col("links", "set", "Links"),
    col("meta", "dict", "Metadata, with `filename` and `lineno`"),
    col("accounts", "set[str]", "Accounts the directive names"),
];

/// The columns of `#postings` a query names, in order. The table also
/// keeps hidden columns after them (`_entry_meta`, `_posting_meta` and the
/// NUL-named posting values), which back functions rather than queries.
///
/// The same columns as [`POSTING_COLUMNS`](super::POSTING_COLUMNS) minus
/// `units`, `cost` and `has_cost` (only a `SELECT` with no `FROM` has those),
/// in its order except the tail: this list ends `accounts, entry`, the
/// builder's order, where the default table's ends `entry, accounts`
/// (bean-query's `.describe postings` order).
/// `postings_column_lists_agree` pins the relationship.
pub(super) const POSTINGS_TABLE_COLUMNS: &[ColumnInfo] = &[
    col("type", "str", "Directive type (always `transaction`)"),
    col("id", "int", "Directive index"),
    col("date", "date", "Transaction date"),
    col("year", "int", "Year of the date"),
    col("month", "int", "Month of the date"),
    col("day", "int", "Day of the date"),
    col("filename", "str", "Source file"),
    col("lineno", "int", "Source line of the posting"),
    col("location", "str", "`filename:lineno`"),
    col("flag", "str", "Transaction flag"),
    col("payee", "str", "Payee, else NULL"),
    col("narration", "str", "Narration"),
    col("description", "str", "`payee | narration`"),
    col("tags", "set", "Transaction tags"),
    col("links", "set", "Transaction links"),
    col("posting_flag", "str", "Posting flag, else NULL"),
    col("account", "str", "Posting account"),
    col("other_accounts", "set", "The transaction's other accounts"),
    col("number", "decimal", "Units number"),
    col("currency", "str", "Units currency"),
    col("cost_number", "decimal", "Per-unit cost, else NULL"),
    col("cost_currency", "str", "Cost currency, else NULL"),
    col("cost_date", "date", "Lot date, else NULL"),
    col("cost_label", "str", "Lot label, else NULL"),
    col("position", "position", "Units with cost"),
    col("price", "amount", "Price, else NULL"),
    col("weight", "amount", "Balancing weight"),
    col("balance", "inventory", "Running balance"),
    col(
        "account_balance",
        "inventory",
        "Per-account running balance",
    ),
    col("meta", "dict", "Posting metadata"),
    col(
        "accounts",
        "set[str]",
        "Accounts of all the transaction's postings",
    ),
    col("entry", "transaction", "Parent transaction"),
];

/// The columns of the system table `name` (any case, `#` optional).
///
/// What `.describe` prints, and the columns the table is built with. `None`
/// when `name` is not a system table. It knows the same names as the
/// executor's table lookup, which a test checks.
#[must_use]
pub fn system_table_columns(name: &str) -> Option<&'static [ColumnInfo]> {
    let upper = name.to_uppercase();
    Some(match upper.strip_prefix('#').unwrap_or(&upper) {
        "PRICES" => PRICES_COLUMNS,
        "BALANCES" => BALANCES_COLUMNS,
        "COMMODITIES" => COMMODITIES_COLUMNS,
        "EVENTS" => EVENTS_COLUMNS,
        "NOTES" => NOTES_COLUMNS,
        "DOCUMENTS" => DOCUMENTS_COLUMNS,
        "ACCOUNTS" => ACCOUNTS_COLUMNS,
        "TRANSACTIONS" => TRANSACTIONS_COLUMNS,
        "ENTRIES" => ENTRIES_COLUMNS,
        "POSTINGS" => POSTINGS_TABLE_COLUMNS,
        _ => return None,
    })
}

/// The column names of a table definition, to build the table from.
fn column_names(columns: &[ColumnInfo]) -> Vec<String> {
    columns.iter().map(|c| c.name.to_string()).collect()
}

impl Executor<'_> {
    /// Build the #prices table from price directives.
    ///
    /// The table has columns: date, currency, amount
    /// - date: The date of the price directive
    /// - currency: The base currency being priced
    /// - amount: The price as an Amount (number + quote currency)
    ///
    /// Only **explicit** Price directives surface here — those that
    /// came from a `price` directive in the source or were emitted by
    /// a declared plugin (e.g. `implicit_prices`). Transaction-derived
    /// implicit prices that the executor's pass-2 walk added for
    /// internal `VALUE()` lookups are intentionally excluded so the
    /// `#prices` table matches `bean-query`'s output (issue #1048).
    pub(super) fn build_prices_table(&self) -> Table {
        let columns = column_names(PRICES_COLUMNS);
        let mut table = Table::new(columns);

        // Collect explicit price entries only — transaction-derived
        // implicit prices are kept in the database for internal
        // lookups but hidden from the `#prices` table for bean-query
        // compat.
        let mut entries: Vec<_> = self.price_db.iter_explicit_entries().collect();
        // Sort by (date, base_currency). NOT source order, unlike the other
        // system tables: these rows come from `price_db`, whose outer map is
        // an `FxHashMap` keyed by base currency, so iteration is grouped by
        // currency in arbitrary order and no source position survives. The
        // secondary key is what makes this table deterministic at all
        // — dropping it to chase bean-query's source order would trade a wrong
        // but stable order for an unstable one (#2163).
        entries.sort_by(|(currency_a, date_a, _, _), (currency_b, date_b, _, _)| {
            date_a.cmp(date_b).then_with(|| currency_a.cmp(currency_b))
        });

        for (base_currency, date, price_number, quote_currency) in entries {
            let row = vec![
                Value::Date(date),
                Value::String(base_currency.to_string()),
                Value::Amount(Amount::new(price_number, quote_currency)),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #balances table from balance assertion directives.
    ///
    /// The table has columns: date, account, amount, tolerance, discrepancy, meta
    /// - date: The date of the balance assertion
    /// - account: The account being balanced
    /// - amount: The expected balance amount
    /// - tolerance: The explicit `~` tolerance, or NULL if none was given
    /// - discrepancy: `computed − asserted` for a FAILING assertion, else NULL
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    ///
    /// `discrepancy` is not a field of the directive — the balance checker
    /// computes it — so it comes from the host via
    /// [`Executor::set_balance_discrepancies`](super::Executor::set_balance_discrepancies)
    /// rather than being re-derived here (#2180). A host that did not validate
    /// supplies nothing and every row reports NULL, which keeps the SCHEMA
    /// matching bean-query's even where the values are unavailable.
    ///
    /// NULL on a passing assertion, matching beancount: its checker sets
    /// `diff_amount` only on a failing entry, so an assertion that is off by
    /// less than its tolerance reports nothing rather than a small number.
    pub(super) fn build_balances_table(&self) -> Table {
        let columns = column_names(BALANCES_COLUMNS);
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect balance directives from either spanned or unspanned directives
        let mut balances: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Balance(b) = d {
                    Some((
                        b.date,
                        b.account.as_ref(),
                        b.amount.clone(),
                        b.tolerance,
                        &b.meta,
                    ))
                } else {
                    None
                }
            })
            .collect();

        // Sort by date ONLY, and stably. The loader already hands over
        // directives in beancount's (date, SORT_ORDER, lineno) order -- which
        // is why `#entries`, which never sorts, still comes back ordered -- so
        // on that path this is a no-op that must not disturb what it receives.
        // It does real work only when an `Executor` is built directly from a
        // caller-supplied slice, where nothing has ordered anything.
        //
        // The bug was therefore not a missing sort but an extra one: a
        // secondary key on account/type/name re-ordered rows that already
        // shared a date, away from the order bean-query returns (#2163).
        //
        // This matches beancount's `(date, lineno)` within a single file. It
        // deliberately does NOT match across an `include`. beancount compares
        // the raw line number with no record of which file it came from, so
        // adding two comment lines to an included file reorders query results;
        // measured, not assumed (#2166). We keep each file's directives
        // together, which is stable under that edit. Divergence by choice.
        balances.sort_by_key(|(date, ..)| *date);

        for (date, account, amount, tolerance, meta) in balances {
            let discrepancy = self
                .balance_discrepancies
                .get(&(
                    date,
                    account.to_string(),
                    amount.currency.to_string(),
                    amount.number,
                ))
                .cloned()
                .map_or(Value::Null, Value::Amount);
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::Amount(amount),
                tolerance.map_or(Value::Null, Value::Number),
                discrepancy,
                Self::metadata_to_value(meta),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #commodities table from commodity directives.
    ///
    /// The table has columns: meta, date, name
    /// - meta: The directive's metadata
    /// - date: The date of the commodity declaration
    /// - name: The currency/commodity code
    ///
    /// `meta` leads, and is the one system table where bean-query's
    /// `SELECT *` includes it — beanquery derives this table's columns from
    /// the `Commodity` namedtuple, whose first field is `meta`. Verified
    /// against bean-query rather than inferred (#2154).
    pub(super) fn build_commodities_table(&self) -> Table {
        let columns = column_names(COMMODITIES_COLUMNS);
        let mut table = Table::new(columns);

        // Collect commodity directives from either spanned or unspanned directives
        let mut commodities: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Commodity(c) = d {
                    Some((c.date, c.currency.as_ref(), &c.meta))
                } else {
                    None
                }
            })
            .collect();

        // Sort by date ONLY, and stably. The loader already hands over
        // directives in beancount's (date, SORT_ORDER, lineno) order -- which
        // is why `#entries`, which never sorts, still comes back ordered -- so
        // on that path this is a no-op that must not disturb what it receives.
        // It does real work only when an `Executor` is built directly from a
        // caller-supplied slice, where nothing has ordered anything.
        //
        // The bug was therefore not a missing sort but an extra one: a
        // secondary key on account/type/name re-ordered rows that already
        // shared a date, away from the order bean-query returns (#2163).
        //
        // This matches beancount's `(date, lineno)` within a single file. It
        // deliberately does NOT match across an `include`. beancount compares
        // the raw line number with no record of which file it came from, so
        // adding two comment lines to an included file reorders query results;
        // measured, not assumed (#2166). We keep each file's directives
        // together, which is stable under that edit. Divergence by choice.
        commodities.sort_by_key(|(date, ..)| *date);

        for (date, name, meta) in commodities {
            let row = vec![
                Self::metadata_to_value(meta),
                Value::Date(date),
                Value::String(name.to_string()),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #events table from event directives.
    ///
    /// The table has columns: date, type, description, meta
    /// - date: The date of the event
    /// - type: The event type
    /// - description: The event value/description
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    pub(super) fn build_events_table(&self) -> Table {
        let columns = column_names(EVENTS_COLUMNS);
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect event directives
        let mut events: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Event(e) = d {
                    Some((e.date, e.event_type.as_str(), e.value.as_str(), &e.meta))
                } else {
                    None
                }
            })
            .collect();

        // Sort by date ONLY, and stably. The loader already hands over
        // directives in beancount's (date, SORT_ORDER, lineno) order -- which
        // is why `#entries`, which never sorts, still comes back ordered -- so
        // on that path this is a no-op that must not disturb what it receives.
        // It does real work only when an `Executor` is built directly from a
        // caller-supplied slice, where nothing has ordered anything.
        //
        // The bug was therefore not a missing sort but an extra one: a
        // secondary key on account/type/name re-ordered rows that already
        // shared a date, away from the order bean-query returns (#2163).
        //
        // This matches beancount's `(date, lineno)` within a single file. It
        // deliberately does NOT match across an `include`. beancount compares
        // the raw line number with no record of which file it came from, so
        // adding two comment lines to an included file reorders query results;
        // measured, not assumed (#2166). We keep each file's directives
        // together, which is stable under that edit. Divergence by choice.
        events.sort_by_key(|(date, ..)| *date);

        for (date, event_type, description, meta) in events {
            let row = vec![
                Value::Date(date),
                Value::String(event_type.to_string()),
                Value::String(description.to_string()),
                Self::metadata_to_value(meta),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #notes table from note directives.
    ///
    /// The table has columns: date, account, comment, tags, links, meta
    /// - date: The date of the note
    /// - account: The account the note is attached to
    /// - comment: The note text
    /// - tags: The note's tags (as a set)
    /// - links: The note's links (as a set)
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    ///
    /// `tags` and `links` are VISIBLE, matching bean-query's wildcard here.
    /// They could not be surfaced at all until #2160, because `Note` had no
    /// fields to hold them and the parser discarded them -- a column census
    /// could not see that, since the columns were simply absent.
    pub(super) fn build_notes_table(&self) -> Table {
        let columns = column_names(NOTES_COLUMNS);
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect note directives
        let mut notes: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Note(n) = d {
                    Some((
                        n.date,
                        n.account.as_ref(),
                        n.comment.as_str(),
                        &n.tags,
                        &n.links,
                        &n.meta,
                    ))
                } else {
                    None
                }
            })
            .collect();

        // Sort by date ONLY, and stably. The loader already hands over
        // directives in beancount's (date, SORT_ORDER, lineno) order -- which
        // is why `#entries`, which never sorts, still comes back ordered -- so
        // on that path this is a no-op that must not disturb what it receives.
        // It does real work only when an `Executor` is built directly from a
        // caller-supplied slice, where nothing has ordered anything.
        //
        // The bug was therefore not a missing sort but an extra one: a
        // secondary key on account/type/name re-ordered rows that already
        // shared a date, away from the order bean-query returns (#2163).
        //
        // This matches beancount's `(date, lineno)` within a single file. It
        // deliberately does NOT match across an `include`. beancount compares
        // the raw line number with no record of which file it came from, so
        // adding two comment lines to an included file reorders query results;
        // measured, not assumed (#2166). We keep each file's directives
        // together, which is stable under that edit. Divergence by choice.
        notes.sort_by_key(|(date, ..)| *date);

        for (date, account, comment, tags, links, meta) in notes {
            let tags_vec: Vec<String> = tags.iter().map(ToString::to_string).collect();
            let links_vec: Vec<String> = links.iter().map(ToString::to_string).collect();
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::String(comment.to_string()),
                Value::StringSet(tags_vec),
                Value::StringSet(links_vec),
                Self::metadata_to_value(meta),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #documents table from document directives.
    ///
    /// The table has columns: date, account, filename, tags, links, meta
    /// - date: The date of the document
    /// - account: The account the document is attached to
    /// - filename: The file path to the document
    /// - tags: The document tags (as a set)
    /// - links: The document links (as a set)
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    pub(super) fn build_documents_table(&self) -> Table {
        let columns = column_names(DOCUMENTS_COLUMNS);
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect document directives
        let mut documents: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Document(doc) = d {
                    Some((
                        doc.date,
                        doc.account.as_ref(),
                        doc.path.as_str(),
                        &doc.tags,
                        &doc.links,
                        &doc.meta,
                    ))
                } else {
                    None
                }
            })
            .collect();

        // Sort by date ONLY, and stably. The loader already hands over
        // directives in beancount's (date, SORT_ORDER, lineno) order -- which
        // is why `#entries`, which never sorts, still comes back ordered -- so
        // on that path this is a no-op that must not disturb what it receives.
        // It does real work only when an `Executor` is built directly from a
        // caller-supplied slice, where nothing has ordered anything.
        //
        // The bug was therefore not a missing sort but an extra one: a
        // secondary key on account/type/name re-ordered rows that already
        // shared a date, away from the order bean-query returns (#2163).
        //
        // This matches beancount's `(date, lineno)` within a single file. It
        // deliberately does NOT match across an `include`. beancount compares
        // the raw line number with no record of which file it came from, so
        // adding two comment lines to an included file reorders query results;
        // measured, not assumed (#2166). We keep each file's directives
        // together, which is stable under that edit. Divergence by choice.
        documents.sort_by_key(|(date, ..)| *date);

        for (date, account, filename, tags, links, meta) in documents {
            let tags_vec: Vec<String> = tags.iter().map(ToString::to_string).collect();
            let links_vec: Vec<String> = links.iter().map(ToString::to_string).collect();
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::String(filename.to_string()),
                Value::StringSet(tags_vec),
                Value::StringSet(links_vec),
                Self::metadata_to_value(meta),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #accounts table from Open/Close directives.
    ///
    /// The table has columns: account, open, close, currencies, booking
    /// - account: The account name
    /// - open: The date the account was opened
    /// - close: The date the account was closed (NULL if still open)
    /// - currencies: Allowed currencies for the account
    /// - booking: Booking method (NULL if not specified)
    pub(super) fn build_accounts_table(&self) -> Table {
        let columns = column_names(ACCOUNTS_COLUMNS);
        let mut table = Table::new(columns);

        // Build a map of account name -> (open_date, close_date, currencies, booking)
        let mut accounts: FxHashMap<
            &str,
            (
                Option<rustledger_core::NaiveDate>,
                Option<rustledger_core::NaiveDate>,
                Vec<String>,
                Option<&str>,
            ),
        > = FxHashMap::default();

        // Process directives
        for directive in self.resolved_directives() {
            match directive {
                Directive::Open(open) => {
                    let entry = accounts.entry(open.account.as_ref()).or_insert((
                        None,
                        None,
                        Vec::new(),
                        None,
                    ));
                    entry.0 = Some(open.date);
                    entry.2 = open.currencies.iter().map(ToString::to_string).collect();
                    entry.3 = open.booking.as_deref();
                }
                Directive::Close(close) => {
                    let entry = accounts.entry(close.account.as_ref()).or_insert((
                        None,
                        None,
                        Vec::new(),
                        None,
                    ));
                    entry.1 = Some(close.date);
                }
                _ => {}
            }
        }

        // Sort accounts by name for consistent output
        let mut account_list: Vec<_> = accounts.into_iter().collect();
        account_list.sort_by_key(|(a, _)| *a);

        for (account, (open_date, close_date, currencies, booking)) in account_list {
            let row = vec![
                Value::String(account.to_string()),
                open_date.map_or(Value::Null, Value::Date),
                close_date.map_or(Value::Null, Value::Date),
                Value::StringSet(currencies),
                booking.map_or(Value::Null, |b| Value::String(b.to_string())),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #transactions table from transaction directives.
    ///
    /// The table has columns: date, flag, payee, narration, tags, links,
    /// accounts, meta
    /// - date: The transaction date
    /// - flag: The transaction flag (e.g., '*' or '!')
    /// - payee: The payee (NULL if not specified)
    /// - narration: The transaction description
    /// - tags: Transaction tags (as a set)
    /// - links: Transaction links (as a set)
    /// - accounts: Set of accounts involved in the transaction
    /// - meta: The transaction's metadata (hidden from `SELECT *`)
    pub(super) fn build_transactions_table(&self) -> Table {
        let columns = column_names(TRANSACTIONS_COLUMNS);
        // `meta` is hidden from `SELECT *`, which bean-query keeps at seven
        // columns here, but selectable by name -- the last of #2154's
        // eleven, and the same split #2161 established for the other five
        // per-table `meta` columns.
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect transaction directives
        let mut transactions: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Transaction(txn) = d {
                    Some(txn)
                } else {
                    None
                }
            })
            .collect();

        // Sort by date for consistent output
        transactions.sort_by_key(|t| t.date);

        for txn in transactions {
            let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
            let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();
            let accounts = TxnAccounts::of(txn).accounts();

            let row = vec![
                Value::Date(txn.date),
                Value::String(txn.flag.to_string()),
                txn.payee
                    .as_ref()
                    .map_or(Value::Null, |p| Value::String(p.to_string())),
                Value::String(txn.narration.to_string()),
                Value::StringSet(tags),
                Value::StringSet(links),
                Value::StringSet(accounts),
                // User metadata only. bean-query's per-table `meta` columns
                // exclude `filename` / `lineno`; only `#entries` carries them
                // (#2162), so this must NOT use `augmented_meta`.
                //
                // Built unconditionally, like the other five per-table `meta`
                // columns. Measured before leaving it that way: on a ledger
                // with five metadata keys on every one of 20k transactions --
                // a deliberately extreme shape -- a query that does not select
                // `meta` costs ~30ms more, 371ms to 400ms. On a ledger without
                // transaction metadata it is below the noise floor. That is
                // far from the 40% that justified gating `#postings` in
                // #2169, so the projection machinery is not worth the review
                // surface here.
                Self::metadata_to_value(&txn.meta),
            ];
            table.add_row(row);
        }

        table
    }

    /// `"payee | narration"`, or the narration alone when there is no payee.
    ///
    /// ONE implementation for the `description` column, which both `#entries`
    /// and `#postings` expose. It was written out twice, and a divergence in
    /// the separator or the no-payee case would have shown up as two tables
    /// describing the same transaction differently.
    fn transaction_description(txn: &rustledger_core::Transaction) -> String {
        match &txn.payee {
            Some(payee) => format!("{payee} | {}", txn.narration),
            None => txn.narration.to_string(),
        }
    }

    /// Build the #entries table from all directives.
    ///
    /// Column order matches bean-query's `SELECT * FROM #entries` exactly, so
    /// the wildcard yields the same 16 columns in the same positions.
    ///
    /// Metadata lives in ONE column here, the visible `meta` bean-query
    /// exposes. This table briefly carried a `_entry_meta` copy of the same
    /// map as well, which cost a deep clone per entry on every query that
    /// touched it; `eval_meta_on_table_row` now falls back to `meta` when the
    /// underscore column is absent, so `ENTRY_META` still resolves.
    ///
    /// `#postings` keeps its `_entry_meta`, and must: there `meta` is the
    /// POSTING's metadata and `_entry_meta` the TRANSACTION's, two different
    /// maps on one row (#2154).
    pub(super) fn build_entries_table(&self) -> Table {
        let columns = column_names(ENTRIES_COLUMNS);
        let mut table = Table::new(columns);

        // Process directives with optional source locations. `get_source_location`
        // returns `None` when there's no source map (the unspanned case), so this
        // single loop covers both.
        for (idx, directive) in self.resolved_directives().enumerate() {
            let source_loc = self.get_source_location(idx);
            let row = self.directive_to_entry_row(Some(idx), directive, source_loc);
            table.add_row(row);
        }

        table
    }

    /// Convert a directive to a row for the #entries table, whose columns are
    /// [`ENTRIES_COLUMNS`]. `idx` is its directive index, the `id`; an
    /// entry a query synthesized has none.
    pub(super) fn directive_to_entry_row(
        &self,
        idx: Option<usize>,
        directive: &Directive,
        source_loc: Option<&SourceLocation>,
    ) -> Vec<Value> {
        let type_name = match directive {
            Directive::Transaction(_) => "transaction",
            Directive::Balance(_) => "balance",
            Directive::Open(_) => "open",
            Directive::Close(_) => "close",
            Directive::Commodity(_) => "commodity",
            Directive::Pad(_) => "pad",
            Directive::Event(_) => "event",
            Directive::Query(_) => "query",
            Directive::Note(_) => "note",
            Directive::Document(_) => "document",
            Directive::Price(_) => "price",
            Directive::Custom(_) => "custom",
        };

        let date = match directive {
            Directive::Transaction(t) => Value::Date(t.date),
            Directive::Balance(b) => Value::Date(b.date),
            Directive::Open(o) => Value::Date(o.date),
            Directive::Close(c) => Value::Date(c.date),
            Directive::Commodity(c) => Value::Date(c.date),
            Directive::Pad(p) => Value::Date(p.date),
            Directive::Event(e) => Value::Date(e.date),
            Directive::Query(q) => Value::Date(q.date),
            Directive::Note(n) => Value::Date(n.date),
            Directive::Document(d) => Value::Date(d.date),
            Directive::Price(p) => Value::Date(p.date),
            Directive::Custom(c) => Value::Date(c.date),
        };

        let (flag, payee, narration, description, tags, links, accounts) =
            if let Directive::Transaction(txn) = directive {
                let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
                let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();
                let accounts = TxnAccounts::of(txn).accounts();
                let description = Self::transaction_description(txn);
                (
                    Value::String(txn.flag.to_string()),
                    txn.payee
                        .as_ref()
                        .map_or(Value::Null, |p| Value::String(p.to_string())),
                    Value::String(txn.narration.to_string()),
                    Value::String(description),
                    Value::StringSet(tags),
                    Value::StringSet(links),
                    Value::StringSet(accounts),
                )
            } else {
                // bean-query leaves description Null on a non-transaction, the
                // same as payee and narration.
                //
                // Tags and links are NOT in that group. `note` and `document`
                // both carry them in beancount v3, and both now survive into
                // our model -- a document's always did, a note's since #2160.
                // Emptying them here made `#entries` disagree with `#documents`
                // about the same directive (#2154). A column-presence census
                // cannot see this: `tags` IS registered on `#entries`, it was
                // just wrong for every directive except transactions.
                let (tags, links, accounts) = match directive {
                    Directive::Open(open) => {
                        (Vec::new(), Vec::new(), vec![open.account.to_string()])
                    }
                    Directive::Close(close) => {
                        (Vec::new(), Vec::new(), vec![close.account.to_string()])
                    }
                    Directive::Balance(bal) => {
                        (Vec::new(), Vec::new(), vec![bal.account.to_string()])
                    }
                    Directive::Document(doc) => (
                        doc.tags.iter().map(ToString::to_string).collect(),
                        doc.links.iter().map(ToString::to_string).collect(),
                        vec![doc.account.to_string()],
                    ),
                    // `note` carries them too, since #2160 gave `Note` the
                    // fields. This arm was Document-only because a note's
                    // tags did not survive parsing; the comment above said so.
                    Directive::Note(note) => (
                        note.tags.iter().map(ToString::to_string).collect(),
                        note.links.iter().map(ToString::to_string).collect(),
                        vec![note.account.to_string()],
                    ),
                    // A set, as beancount's `get_entry_accounts` returns: sorted
                    // like the transaction arm, and one entry when a pad's source
                    // is its own account.
                    Directive::Pad(pad) => {
                        let mut accounts =
                            vec![pad.account.to_string(), pad.source_account.to_string()];
                        accounts.sort();
                        accounts.dedup();
                        (Vec::new(), Vec::new(), accounts)
                    }
                    _ => (Vec::new(), Vec::new(), Vec::new()),
                };
                (
                    Value::Null,
                    Value::Null,
                    Value::Null,
                    Value::Null,
                    Value::StringSet(tags),
                    Value::StringSet(links),
                    Value::StringSet(accounts),
                )
            };

        let filename = Self::source_filename_value(source_loc);
        let lineno = Self::source_lineno_value(source_loc);

        // Date parts come from the entry's own date, so they are populated for
        // every directive type and not just transactions -- bean-query reports
        // `year` on an `open` too.
        let (year, month, day) = match &date {
            Value::Date(d) => (
                Value::Integer(i64::from(d.year())),
                Value::Integer(i64::from(d.month())),
                Value::Integer(i64::from(d.day())),
            ),
            _ => (Value::Null, Value::Null, Value::Null),
        };

        vec![
            idx.map_or(Value::Null, |idx| Value::Integer(idx as i64)), // id
            Value::String(type_name.to_string()),
            filename,
            lineno,
            date,
            year,
            month,
            day,
            flag,
            payee,
            narration,
            description,
            tags,
            links,
            // bean-query's `#entries.meta` carries `filename` and `lineno`
            // alongside the user's keys; its per-table `meta` columns
            // (#notes, #balances, ...) do NOT, so this augmentation belongs
            // here and must not move into `metadata_to_value` (#2162).
            Self::metadata_to_value(&Self::augmented_meta(directive.meta(), source_loc)),
            accounts,
        ]
    }

    /// Build the #postings table from transaction postings.
    ///
    /// Column schema matches Python beancount's `postings` table for compatibility.
    ///
    /// # Errors
    ///
    /// When the `account_balance` replay refuses a transaction (see below).
    pub(super) fn build_postings_table(
        &self,
        query: &crate::ast::SelectQuery,
    ) -> Result<Table, crate::QueryError> {
        let mut columns = column_names(POSTINGS_TABLE_COLUMNS);
        columns.extend([
            // Hidden metadata columns for META/ENTRY_META functions
            "_entry_meta".to_string(),
            "_posting_meta".to_string(),
        ]);
        // Each row keeps its posting, which `weight(position)`,
        // `cost(position)` (#2429) and `sum(position)` (#2430) answer from
        // when a query reads them (#2442, `RowOrigin`).
        let position_column: std::sync::Arc<[usize]> = std::sync::Arc::from(vec![
            columns
                .iter()
                .position(|c| c == "position")
                .expect("#postings has a position column"),
        ]);
        let mut table = Table::new(columns);

        // Single posting-source scan, shared with the default `SELECT` path
        // ([`Self::collect_postings`]): every posting in directive order, with no
        // FROM/WHERE filter and both running balances tracked. With no filter
        // there are no predicates to evaluate, but the scan is still fallible:
        // `account_balance` replays each transaction through a booking engine,
        // which refuses one it cannot read. This used to be an `expect` that
        // called that impossible, and a global `option "booking_method"
        // "NONE"` ledger, replayed with the wrong default, crashed the process
        // (exit 101) instead of reporting a query error (#2386).
        let contexts = self
            .scan_postings(
                None,
                None,
                // Gate the running-balance snapshots on whether the query
                // reads them. These were hardcoded true, so
                // `SELECT count(account) FROM #postings` paid for the
                // cumulative `Inventory` clones per posting -- the #1080
                // runaway -- on every system-table query (#2169).
                //
                // Worth 34% of the wall clock and 55% of peak RSS on a
                // 40k-posting ledger (517MB -> 233MB), since the snapshots are
                // retained `Inventory` copies. Both before and after scale
                // linearly, so this is a constant factor, not a complexity
                // fix -- the #1080 quadratic itself was already dealt with.
                //
                // The flags do NOT mean what they mean in `collect_postings`,
                // and reusing that computation verbatim was wrong twice over:
                //
                //   * This scan gets `where_clause: None`. The table is built
                //     first and filtered afterwards, so nothing is read "at
                //     WHERE time" and both `where_reads_*` are false.
                //   * The table materializes `account_balance` into every row
                //     regardless of the SELECT list, so the TABLE is the
                //     output. Gating on `output_references_column` released
                //     the snapshot before the row was built, and
                //     `WHERE account_balance != 0` then matched nothing.
                //
                // A wildcard reads every column, and unlike the default
                // source -- whose `WILDCARD_COLUMNS` excludes both -- this
                // table's `SELECT *` includes `balance` and
                // `account_balance`, so it must force both on.
                {
                    let wildcard = query
                        .targets
                        .iter()
                        .any(|t| matches!(t.expr, crate::ast::Expr::Wildcard));
                    let account_balance =
                        wildcard || super::query_references_column(query, "account_balance");
                    super::ScanNeeds {
                        balance: wildcard || super::query_references_column(query, "balance"),
                        account_balance,
                        where_reads_balance: false,
                        where_reads_account_balance: false,
                        output_reads_account_balance: account_balance,
                        // Every row has both columns: the scan builds each
                        // transaction's set once (#2504), shared with the
                        // default table's.
                        txn_accounts: true,
                    }
                },
                true,
            )?
            .postings;

        // Four columns hold ~40% of this table's build time and ~47% of its
        // peak RSS: the structured `entry` object and the three metadata maps
        // (`meta`, `_entry_meta`, `_posting_meta`). Skip them when the query
        // cannot observe them (#2169). Everything else is cheap enough that
        // gating it would cost more in review surface than it saves --
        // stubbing both `StringSet` columns moved 443ms to 437ms.
        //
        // Callgrind on `examples/profile_query.rs` puts the whole #2169 +
        // #2173 effect at 457.4M -> 244.2M instructions, which does not move
        // with machine load the way the wall clock does.
        //
        // A wildcard forces on only what it can actually SHOW. This table's
        // `SELECT *` emits `meta` but omits `entry` and the two `_`-prefixed
        // metadata helpers -- `Executor::wildcard_hidden` drops the structured
        // entry column to match beanquery, and underscore columns with it. So
        // a bare `SELECT *` never observes those three, and forcing them on
        // would be pure waste. Reaching them from a wildcard query still
        // works, because `ORDER BY entry.narration` or `meta('k')` names or
        // calls its way in and is picked up below.
        let wildcard = query
            .targets
            .iter()
            .any(|t| matches!(t.expr, crate::ast::Expr::Wildcard));
        // `entry` is reachable as a bare column and as `entry.narration`;
        // `expr_references_column` recurses into `Attribute`/`Subscript`
        // operands, so the bare name covers both.
        let needs_entry = super::query_references_column(query, "entry");
        let needs_meta = wildcard || super::query_references_column(query, "meta");
        // The hidden metadata columns are read by FUNCTION, not by name:
        // `eval_meta_on_table_row` is dispatched for exactly these four, and
        // reads `_posting_meta` / `_entry_meta` off the row. A query calling
        // `meta('key')` never mentions either column, so gating on column
        // references alone would break it silently.
        let needs_hidden_meta = super::query_references_column(query, "_entry_meta")
            || super::query_references_column(query, "_posting_meta")
            || super::query_calls_any_function(
                query,
                &["META", "ENTRY_META", "ANY_META", "POSTING_META"],
            );

        // Entry objects are per-TRANSACTION; postings of one transaction are
        // contiguous in the scan, so memoize the last built object instead of
        // rebuilding (strings, tags/links vectors, full meta conversion) for
        // every posting (#1800 review).
        let mut last_entry: Option<(usize, Value)> = None;

        for ctx in contexts {
            let source = Self::context_source(&ctx);
            let txn: &rustledger_core::Transaction = &ctx.transaction;
            let posting = &txn.postings[ctx.posting_index];
            // `scan_postings` always sets a real directive index on every context.
            let dir_idx = ctx
                .directive_index
                .expect("scan_postings always records the source directive index");

            // Transaction-level location — the per-posting fallback below.
            let source_loc = self.get_source_location(dir_idx);

            let entry_val = if needs_entry {
                match &last_entry {
                    Some((idx, value)) if *idx == dir_idx => value.clone(),
                    _ => {
                        let value = Self::entry_object(txn, source_loc);
                        last_entry = Some((dir_idx, value.clone()));
                        value
                    }
                }
            } else {
                Value::Null
            };

            let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
            let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();

            // Built once per transaction by the scan, not per posting:
            // rebuilding the set for every row made a transaction of n
            // postings cost O(n^2).
            let built;
            let txn_accounts = if let Some(set) = ctx.txn_accounts.as_deref() {
                set
            } else {
                built = TxnAccounts::of(txn).into_owned();
                &built
            };
            let all_accounts = txn_accounts.accounts();

            let description = Self::transaction_description(txn);

            let year = Value::Integer(i64::from(txn.date.year()));
            let month = Value::Integer(i64::from(txn.date.month()));
            let day = Value::Integer(i64::from(txn.date.day()));

            // Per-posting source location (the posting's own span), falling back
            // to the transaction's when the posting has no real span.
            let posting_loc = self
                .span_source_location(posting.file_id, posting.span.start)
                .or_else(|| source_loc.cloned());
            let loc = posting_loc.as_ref();
            let (filename, lineno, location) = (
                Self::source_filename_value(loc),
                Self::source_lineno_value(loc),
                Self::source_location_value(loc),
            );

            let (number, currency) = posting.amount().map_or((Value::Null, Value::Null), |a| {
                (
                    Value::Number(a.number),
                    Value::String(a.currency.to_string()),
                )
            });

            let (cost_number, cost_currency, cost_date, cost_label) =
                if let Some(cost_spec) = &posting.cost {
                    let units = posting.amount();
                    if let Some(cost) = units.and_then(|u| cost_spec.resolve(u.number, txn.date)) {
                        (
                            Value::Number(cost.number),
                            Value::String(cost.currency.to_string()),
                            cost.date.map_or(Value::Null, Value::Date),
                            cost.label
                                .as_ref()
                                .map_or(Value::Null, |l| Value::String(l.clone())),
                        )
                    } else {
                        (Value::Null, Value::Null, Value::Null, Value::Null)
                    }
                } else {
                    (Value::Null, Value::Null, Value::Null, Value::Null)
                };

            let position_val = if let Some(units) = posting.amount() {
                Value::Position(Box::new(Position::from_posting(
                    units,
                    posting.cost.as_deref(),
                    txn.date,
                )))
            } else {
                Value::Null
            };

            let price_val = posting
                .price
                .as_ref()
                .and_then(|p| p.amount())
                .map_or(Value::Null, |a| Value::Amount(a.clone()));

            // Weight delegates to `compute_posting_weight` so the `#postings`
            // table and the default-FROM `weight` accessor stay in lockstep
            // (issue #1052).
            let weight_val = compute_posting_weight(posting);

            // The running balances come straight from the shared scan
            // (`needs_balance`/`needs_account_balance` both `true` above), so they
            // are identical to the old inline accumulators — proven by the
            // #postings parity test.
            let balance_val = ctx.balance.map_or(Value::Null, |inv| {
                Value::Inventory(std::sync::Arc::new(inv))
            });
            let account_balance_val = ctx.account_balance.map_or(Value::Null, Value::Inventory);

            // Other accounts: every posting's account except THIS posting's,
            // by index, so a second posting to the same account still counts.
            let other_accounts = txn_accounts.others(posting.account.as_ref());

            let posting_flag = posting
                .flag
                .map_or(Value::Null, |f| Value::String(f.to_string()));

            let row = vec![
                // Entry-level
                Value::String("transaction".to_string()),
                Value::Integer(dir_idx as i64),
                Value::Date(txn.date),
                year,
                month,
                day,
                filename,
                lineno,
                location,
                // Transaction-level
                Value::String(txn.flag.to_string()),
                txn.payee
                    .as_ref()
                    .map_or(Value::Null, |p| Value::String(p.to_string())),
                Value::String(txn.narration.to_string()),
                Value::String(description),
                Value::StringSet(tags),
                Value::StringSet(links),
                // Posting-level
                posting_flag,
                Value::String(posting.account.to_string()),
                Value::StringSet(other_accounts),
                number,
                currency,
                cost_number,
                cost_currency,
                cost_date,
                cost_label,
                position_val,
                price_val,
                weight_val,
                balance_val,
                account_balance_val,
                // Metadata and collection
                if needs_meta {
                    Value::Metadata(Box::new(Self::augmented_meta(
                        &posting.meta,
                        posting_loc.as_ref(),
                    )))
                } else {
                    Value::Null
                },
                Value::StringSet(all_accounts),
                entry_val,
                // Hidden metadata columns
                if needs_hidden_meta {
                    Self::metadata_to_value(&txn.meta)
                } else {
                    Value::Null
                },
                if needs_hidden_meta {
                    Self::metadata_to_value(&posting.meta)
                } else {
                    Value::Null
                },
            ];
            table.add_row_with_origin(
                row,
                Some(super::types::RowOrigin {
                    posting: source,
                    columns: std::sync::Arc::clone(&position_column),
                }),
            );
        }

        Ok(table)
    }
}

/// A transaction's `accounts` set, and what each posting's `other_accounts`
/// is derived from.
///
/// ONE implementation for every `accounts` / `other_accounts` column: the
/// default postings table, `#postings`, `#entries` and `#transactions`.
/// bean-query builds these as Python sets (`{p.account for p in
/// entry.postings}`, and for `other_accounts` `if p is not
/// context.posting`), so a transaction posting twice to one account lists it
/// once, and `other_accounts` drops only the CURRENT posting, never a
/// different posting that shares its account (#2483).
///
/// Generic over how the names are held: [`TxnAccounts::of`] borrows them
/// from the transaction (one set per row, no copies until output), and
/// [`TxnAccounts::into_owned`] keeps a set across rows (`#postings` builds
/// one per transaction).
#[derive(Debug)]
pub(super) struct TxnAccounts<S> {
    /// Every posting's account, sorted and deduped.
    all: Vec<S>,
    /// The accounts, sorted, that at least two postings use. Excluding ONE
    /// posting to such an account leaves the account in `other_accounts`.
    repeated: Vec<S>,
}

#[cfg(test)]
thread_local! {
    /// How many account sets this thread has built: the tests count them to
    /// pin that a scan builds one per transaction, not one per posting.
    pub(super) static TXN_ACCOUNTS_BUILT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    /// How many `accounts` / `other_accounts` values this thread has
    /// materialized: the tests count them to pin that `x IN other_accounts`
    /// builds none (#2597).
    pub(super) static TXN_ACCOUNT_SETS_MATERIALIZED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl<'t> TxnAccounts<&'t str> {
    /// Sort `txn`'s posting accounts once, then read off the distinct ones
    /// and the repeated ones.
    pub(super) fn of(txn: &'t rustledger_core::Transaction) -> Self {
        #[cfg(test)]
        TXN_ACCOUNTS_BUILT.with(|n| n.set(n.get() + 1));
        let mut all: Vec<&str> = txn.postings.iter().map(|p| p.account.as_ref()).collect();
        all.sort_unstable();
        // Usually empty, so usually no allocation.
        let repeated: Vec<&str> = all
            .chunk_by(|a, b| a == b)
            .filter(|run| run.len() > 1)
            .map(|run| run[0])
            .collect();
        all.dedup();
        Self { all, repeated }
    }

    /// The same set, holding its own copies of the names.
    pub(super) fn into_owned(self) -> TxnAccounts<String> {
        TxnAccounts {
            all: self.all.into_iter().map(str::to_string).collect(),
            repeated: self.repeated.into_iter().map(str::to_string).collect(),
        }
    }
}

impl<S: AsRef<str>> TxnAccounts<S> {
    /// The `accounts` column: every posting's account, sorted and deduped.
    pub(super) fn accounts(&self) -> Vec<String> {
        #[cfg(test)]
        TXN_ACCOUNT_SETS_MATERIALIZED.with(|n| n.set(n.get() + 1));
        self.all.iter().map(|a| a.as_ref().to_string()).collect()
    }

    /// Whether `name` is in the `accounts` column, answered without building
    /// it (#2597).
    pub(super) fn contains(&self, name: &str) -> bool {
        self.all.binary_search_by(|a| a.as_ref().cmp(name)).is_ok()
    }

    /// Whether `name` is in what [`Self::others`] gives for `account`,
    /// answered without building it (#2597): `x IN other_accounts` built
    /// every row's set, n names per posting, which made it quadratic in a
    /// transaction's size. The same rule as `others`: `account` itself counts
    /// only when another posting also uses it.
    pub(super) fn others_contain(&self, account: &str, name: &str) -> bool {
        if name == account {
            self.repeated
                .binary_search_by(|a| a.as_ref().cmp(name))
                .is_ok()
        } else {
            self.contains(name)
        }
    }

    /// `other_accounts` for a posting to `account` in this transaction: every
    /// OTHER posting's account. `account` drops out unless another posting
    /// also uses it.
    pub(super) fn others(&self, account: &str) -> Vec<String> {
        #[cfg(test)]
        TXN_ACCOUNT_SETS_MATERIALIZED.with(|n| n.set(n.get() + 1));
        let shared = self
            .repeated
            .binary_search_by(|a| a.as_ref().cmp(account))
            .is_ok();
        self.all
            .iter()
            .map(AsRef::as_ref)
            .filter(|a| shared || *a != account)
            .map(str::to_string)
            .collect()
    }
}
