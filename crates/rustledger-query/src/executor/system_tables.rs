//! Built-in system-table builders — `#prices`, `#balances`, `#commodities`,
//! `#events`, `#notes`, `#documents`, `#accounts`, `#transactions`, `#entries`,
//! `#postings`. Extracted from the executor god-module; the `get_builtin_table`
//! dispatcher in `mod.rs` calls these. Most walk directives via
//! `Executor::resolved_directives` (so they honor the source-mapped
//! constructor); `#prices` is backed by `self.price_db` instead (itself built
//! from the directives at construction).

use super::types::{SourceLocation, Table, Value};
use super::{Executor, compute_posting_weight};
use rustc_hash::FxHashMap;
use rustledger_core::{Amount, Directive, Position};

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
        let columns = vec![
            "date".to_string(),
            "currency".to_string(),
            "amount".to_string(),
        ];
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
    /// The table has columns: date, account, amount, tolerance, meta
    /// - date: The date of the balance assertion
    /// - account: The account being balanced
    /// - amount: The expected balance amount
    /// - tolerance: The explicit `~` tolerance, or NULL if none was given
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    ///
    /// bean-query also exposes `discrepancy` here. It is not a field of the
    /// directive — the balance checker computes it — so it is tracked
    /// separately rather than faked from the data we have (#2154).
    pub(super) fn build_balances_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "amount".to_string(),
            "tolerance".to_string(),
            "meta".to_string(),
        ];
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
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::Amount(amount),
                tolerance.map_or(Value::Null, Value::Number),
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
        let columns = vec!["meta".to_string(), "date".to_string(), "name".to_string()];
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
        let columns = vec![
            "date".to_string(),
            "type".to_string(),
            "description".to_string(),
            "meta".to_string(),
        ];
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
    /// The table has columns: date, account, comment, meta
    /// - date: The date of the note
    /// - account: The account the note is attached to
    /// - comment: The note text
    /// - meta: The directive's metadata (hidden from `SELECT *`)
    ///
    /// bean-query also exposes `tags` and `links` here. Our `Note` model
    /// drops them at parse time, so they cannot be surfaced until #2160
    /// lands — a column census cannot see that, since the columns are
    /// simply absent.
    pub(super) fn build_notes_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "comment".to_string(),
            "meta".to_string(),
        ];
        let mut table = Table::new(columns).with_hidden(&["meta"]);

        // Collect note directives
        let mut notes: Vec<_> = self
            .resolved_directives()
            .filter_map(|d| {
                if let Directive::Note(n) = d {
                    Some((n.date, n.account.as_ref(), n.comment.as_str(), &n.meta))
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

        for (date, account, comment, meta) in notes {
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::String(comment.to_string()),
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
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "filename".to_string(),
            "tags".to_string(),
            "links".to_string(),
            "meta".to_string(),
        ];
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
        let columns = vec![
            "account".to_string(),
            "open".to_string(),
            "close".to_string(),
            "currencies".to_string(),
            "booking".to_string(),
        ];
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
    /// The table has columns: date, flag, payee, narration, tags, links, accounts
    /// - date: The transaction date
    /// - flag: The transaction flag (e.g., '*' or '!')
    /// - payee: The payee (NULL if not specified)
    /// - narration: The transaction description
    /// - tags: Transaction tags (as a set)
    /// - links: Transaction links (as a set)
    /// - accounts: Set of accounts involved in the transaction
    pub(super) fn build_transactions_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "tags".to_string(),
            "links".to_string(),
            "accounts".to_string(),
        ];
        let mut table = Table::new(columns);

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
            let mut accounts: Vec<String> = txn
                .postings
                .iter()
                .map(|p| p.account.to_string())
                .collect::<std::collections::HashSet<_>>()
                .into_iter()
                .collect();
            accounts.sort(); // Ensure deterministic ordering

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
        let columns = vec![
            "id".to_string(),
            "type".to_string(),
            "filename".to_string(),
            "lineno".to_string(),
            "date".to_string(),
            "year".to_string(),
            "month".to_string(),
            "day".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "description".to_string(),
            "tags".to_string(),
            "links".to_string(),
            "meta".to_string(),
            "accounts".to_string(),
        ];
        let mut table = Table::new(columns);

        // Process directives with optional source locations. `get_source_location`
        // returns `None` when there's no source map (the unspanned case), so this
        // single loop covers both.
        for (idx, directive) in self.resolved_directives().enumerate() {
            let source_loc = self.get_source_location(idx);
            let row = self.directive_to_entry_row(idx, directive, source_loc);
            table.add_row(row);
        }

        table
    }

    /// Convert a directive to a row for the #entries table.
    fn directive_to_entry_row(
        &self,
        idx: usize,
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
                let mut accounts: Vec<String> = txn
                    .postings
                    .iter()
                    .map(|p| p.account.to_string())
                    .collect::<std::collections::HashSet<_>>()
                    .into_iter()
                    .collect();
                accounts.sort(); // Ensure deterministic ordering
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
                // carry them in beancount v3, and a document's already survive
                // into our model -- `SELECT tags FROM #documents` returns them.
                // Emptying them here made `#entries` disagree with `#documents`
                // about the same directive (#2154). A column-presence census
                // cannot see this: `tags` IS registered on `#entries`, it was
                // just wrong for every directive except transactions.
                let (tags, links) = match directive {
                    Directive::Document(doc) => (
                        doc.tags.iter().map(ToString::to_string).collect(),
                        doc.links.iter().map(ToString::to_string).collect(),
                    ),
                    _ => (Vec::new(), Vec::new()),
                };
                (
                    Value::Null,
                    Value::Null,
                    Value::Null,
                    Value::Null,
                    Value::StringSet(tags),
                    Value::StringSet(links),
                    Value::StringSet(vec![]),
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
            Value::Integer(idx as i64), // id
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
    pub(super) fn build_postings_table(&self, query: &crate::ast::SelectQuery) -> Table {
        let columns = vec![
            // Entry-level columns
            "type".to_string(),
            "id".to_string(),
            "date".to_string(),
            "year".to_string(),
            "month".to_string(),
            "day".to_string(),
            "filename".to_string(),
            "lineno".to_string(),
            "location".to_string(),
            // Transaction-level columns
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "description".to_string(),
            "tags".to_string(),
            "links".to_string(),
            // Posting-level columns
            "posting_flag".to_string(),
            "account".to_string(),
            "other_accounts".to_string(),
            "number".to_string(),
            "currency".to_string(),
            "cost_number".to_string(),
            "cost_currency".to_string(),
            "cost_date".to_string(),
            "cost_label".to_string(),
            "position".to_string(),
            "price".to_string(),
            "weight".to_string(),
            "balance".to_string(),
            "account_balance".to_string(),
            // Metadata and collection columns
            "meta".to_string(),
            "accounts".to_string(),
            // Parent transaction as a structured object (entry.meta etc.,
            // #1796) — same canonical builder as the default-path column.
            "entry".to_string(),
            // Hidden metadata columns for META/ENTRY_META functions
            "_entry_meta".to_string(),
            "_posting_meta".to_string(),
        ];
        let mut table = Table::new(columns);

        // Single posting-source scan, shared with the default `SELECT` path
        // ([`Self::collect_postings`]): every posting in directive order, with no
        // FROM/WHERE filter and both running balances tracked. With no filter
        // there are no predicates to evaluate, so the scan is infallible here —
        // assert that invariant rather than silently emitting an empty table.
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
                    }
                },
                true,
            )
            .expect("scan_postings(None, None, ..) evaluates no predicates, so it cannot fail")
            .postings;

        // Entry objects are per-TRANSACTION; postings of one transaction are
        // contiguous in the scan, so memoize the last built object instead of
        // rebuilding (strings, tags/links vectors, full meta conversion) for
        // every posting (#1800 review).
        let mut last_entry: Option<(usize, Value)> = None;

        for ctx in contexts {
            let txn = ctx.transaction;
            let posting = &txn.postings[ctx.posting_index];
            // `scan_postings` always sets a real directive index on every context.
            let dir_idx = ctx
                .directive_index
                .expect("scan_postings always records the source directive index");

            // Transaction-level location — the per-posting fallback below.
            let source_loc = self.get_source_location(dir_idx);

            let entry_val = match &last_entry {
                Some((idx, value)) if *idx == dir_idx => value.clone(),
                _ => {
                    let value = Self::entry_object(txn, source_loc);
                    last_entry = Some((dir_idx, value.clone()));
                    value
                }
            };

            let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
            let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();

            let mut all_accounts: Vec<String> = txn
                .postings
                .iter()
                .map(|p| p.account.to_string())
                .collect::<std::collections::HashSet<_>>()
                .into_iter()
                .collect();
            all_accounts.sort();

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

            // Other accounts: all accounts in the transaction except this posting's.
            let other_accounts: Vec<String> = all_accounts
                .iter()
                .filter(|a| a.as_str() != posting.account.as_ref())
                .cloned()
                .collect();

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
                Value::Metadata(Box::new(Self::augmented_meta(
                    &posting.meta,
                    posting_loc.as_ref(),
                ))),
                Value::StringSet(all_accounts),
                entry_val,
                // Hidden metadata columns
                Self::metadata_to_value(&txn.meta),
                Self::metadata_to_value(&posting.meta),
            ];
            table.add_row(row);
        }

        table
    }
}
