//! Binary serialization for WASM ledger caching.
//!
//! Provides rkyv-based serialization of parsed ledgers, enabling storage in
//! browser OPFS or `IndexedDB` and fast cache restores.
//!
//! Restoring a [`super::parsed_ledger::Ledger`] from cache avoids all
//! re-parsing, booking, and validation. Restoring a
//! [`super::parsed_ledger::ParsedLedger`] re-parses source text to rebuild
//! editor spans, but skips the expensive booking and validation phases by
//! reusing cached directives, options, and errors.
//!
//! # Cache format
//!
//! Each cache blob starts with a 12-byte header (8-byte magic + 4-byte version)
//! followed by an rkyv-serialized payload. The payload is therefore not at
//! its archive's alignment in the blob, and the blob a caller hands back need
//! not be aligned at all, so decoding copies the payload into an aligned
//! buffer first (#2934).
//!
//! # Cache invalidation
//!
//! Use [`hash_sources`] to compute a SHA-256 fingerprint of the source files.
//! Store the fingerprint alongside the cache bytes and compare on load; if the
//! fingerprint changed, discard the cache and re-parse.

use rustledger_core::Directive;

use crate::types::{Error, LedgerOptions};

/// Current cache format version. Increment when the serialized format changes.
///
/// v2 (#1597): `Error` gained `code`/`phase`/`hint`/`file`/`end_line`/
/// `end_column`, changing its rkyv archived layout — a v1 blob must be rejected
/// and re-parsed rather than misread under the new layout.
/// v4 (#1939): arithmetic in a COST SPEC is evaluated rather than truncated to
/// its first operand, and a leading `-` is now part of the number. The archived
/// LAYOUT is unchanged, so a v3 blob would be accepted and its `Vec<Directive>`
/// deserialized happily — serving a truncated or sign-flipped cost basis on a
/// build that has the fix. This cache archives the same parsed directives as
/// the loader cache, so it needs the same bump for the same reason.
/// v5 (#1944): arithmetic is evaluated in METADATA values and BALANCE
/// TOLERANCES too. Same reasoning as v4 and the loader's v19 — the archived
/// layout does not move, so a v4 blob would be accepted and its directives
/// deserialized with the truncated tolerance still in them. Any parser change
/// that alters a VALUE has to bump both caches, not just the loader's; missing
/// this one on the previous PR is what prompted the rule.
/// v6 (#1930): account names accept any non-ASCII character inside a
/// component, so a ledger that previously failed to parse now yields
/// directives. Layout again unchanged, so a v5 blob would be accepted and the
/// cached PARSE FAILURE served on a build that can read the file.
/// v7 (#1949): trailing tags/links on most directives are now parse
/// errors, so a previously-clean file can carry errors. Same reasoning as the
/// loader's v21; both caches move when a parser change alters output.
/// v8 (#1955): metadata keys need two or more characters, so a
/// previously-clean file can carry errors. Same reasoning as the loader's
/// v22; both caches move when a parser change alters output.
/// v9 (#1954): link-valued metadata is now a parse error, so a
/// previously-clean file can carry errors. Same reasoning as the loader's v23.
/// v10 (#1958): tags/links in custom and pushmeta values are now parse
/// errors. Same reasoning as the loader's v24.
/// v11 (#2008): transaction headers beancount rejects are now parse errors.
/// Same reasoning as the loader's v25.
/// v12 (#2008): malformed cost-spec component lists likewise. Loader v26.
/// v13 (#2008): numberless cost specs archive `None`, not an invented zero.
/// Loader v27 — and unlike v11/v12 this one changes archived VALUES, so a
/// stale blob would serve the invented number rather than merely miss an error.
/// v14: a literal `-0.00` parses to an UNSIGNED zero. Loader v28 — archived
/// VALUES again, so a stale blob would serve `-0.00` where the build no longer
/// produces one.
/// v15: `Posting::cost` and `Posting::price` are boxed. Loader v29 — the first
/// entry here that changes neither the parser's output nor anything
/// loader-internal: the archived VALUES are identical, but `ArchivedPosting`
/// changed SHAPE, and a v14 blob read by this build would interpret an inline
/// `CostSpec` as a relative pointer.
/// v16: `Note` gained `tags` and `links` (#2160), then a blank line before a
/// `note`/`document` stopped eating them (#2160 review). Loader v31 and v32 --
/// this one bump answers both, and it is overdue: #2160 moved the loader
/// version and the pin below but left this constant at 15, the exact miss the
/// pin exists to catch. That leaves v15 AMBIGUOUS -- a blob written before
/// #2160 holds the two-field-shorter `ArchivedNote`, one written by a dev
/// build after it holds the new shape, and both claim v15. Rejecting every
/// v15 blob is the only reading that is safe for either.
/// v17: `Pad` and `Balance` swap `DirectivePriority`, so a same-date pad and
/// balance come out of the pipeline in the other order (#2179). Loader v32,
/// unchanged -- and this is the first entry here that moves neither the
/// parser's output nor an archived layout. Every directive archives to the
/// same bytes; the LIST this cache holds is a different list. `LedgerPayload`
/// stores the output of `process()`, which sorts by `canonical_sort_key`, and
/// that key reads `DirectivePriority`.
///
/// What a stale blob costs is narrower than it first looks, and worth stating
/// exactly: `process_pads` re-sorts its input by `booking_sort_key`, which is
/// the same `(date, priority)`, so pad AMOUNTS computed from a v16 blob would
/// still come out right. What differs is the order of the directives this
/// cache hands back, which is what every order-sensitive consumer reads --
/// journal output, `SELECT` row order, the FFI directive stream. A cache that
/// returns a different sequence than a fresh run is stale by definition.
/// v18: `~` ends a balance's amount expression and a `price` refuses one
/// outright (#2191). Loader v33. Parser OUTPUT in both directions: a v17 blob
/// holds a parse error where this build produces a balance, and a truncated
/// 1.10 where this build produces an error.
/// v19: a `query` carrying a tag or link is diagnosed (#2194). Loader v34.
/// The archived DIRECTIVE is identical -- `reject_tags_and_links` records an
/// error and conversion still emits the `Query` -- so what a stale blob costs
/// is the diagnostic, not the data: such a file used to parse clean and was
/// therefore cacheable, and replaying its blob skips the parse that now
/// complains. Verified against a pre-#2194 binary's cache: 0 errors without
/// this bump, 2 with it.
/// v20: a balance tolerance in a currency the amount does not use, or
/// carrying a second juxtaposed number, is diagnosed rather than partly read
/// and partly discarded (#2193). Loader v35. Same shape as v19: the archived
/// directive is identical and the diagnostic is what a stale blob would hide.
/// v21: an invalid option is diagnosed on the single-source entry points
/// (#2299). Loader v35, unchanged -- this one is ours alone. Same shape as v19
/// and v20 again: the archived directives are identical, and what a stale blob
/// hides is the diagnostic. `from_cache` restores `parse_errors` verbatim and
/// re-parses the source only for editor spans, so it never re-derives them.
/// Measured on a pre-fix blob at v20, which this build accepted: `isValid()`
/// came back true with no codes where a fresh parse of the same source returns
/// false with E7001 -- the fix silently did not apply to any cached ledger.
///
/// v21 carries a debt that is not its own, which is the more useful half of
/// this entry. #2291/#2292 (option-warning SEVERITY), #2297/#2298 (its code
/// and phase, and the `[E7009] ` prefix dropped from the message text) each
/// changed the CONTENT of a cached error list and none of them touched this
/// file. `Ledger::is_valid` is `!has_fatal(&self.errors)` over exactly that
/// restored list, so a blob written before them decides validity by the rules
/// those PRs replaced. Measured on the same input, a duplicated option:
///
///   this build     E7003 Warning  code Some("E7003")  isValid=true
///   pre-#2291 blob E7003 Error    code None           isValid=false
///
/// which is the #2291 bug served back out of the cache -- a ledger `rledger
/// check` exits 0 on, reported invalid. Those three bumps are owed and this
/// one pays them, so the range v20 -> v21 covers more than #2299 alone.
/// v22: a missing `include` is reported at the directive that names it
/// (#2322). Loader v35, unchanged -- the loader's own cache archives parsed
/// directives, and those did not move. What moved is `Ledger`'s error list.
/// `Ledger.fromFiles` still builds a ledger when an include is missing,
/// `Error::from(LedgerError)` now copies the include site into `file`, `line`
/// and `column`, and `fromCache` restores `LedgerPayload.errors` verbatim. A v21
/// blob would hand back that error with no location, so the fix would silently
/// not apply to any cached ledger. Same shape as v19-v21: the archived
/// directives are identical, and what a stale blob hides is part of a
/// diagnostic. #2322 shipped without this bump; it was missed in review, which
/// concluded from truncated search output that `LedgerPayload` had no caller
/// outside tests.
/// v23: booking resolves a `{{T}}` reduction against the lot its total names
/// (#2306, #2325). Loader v35, unchanged -- the loader archives parsed
/// directives, and those did not move. The processed ones did: a dated
/// `{{T, D}}` sale now books with the matched lot's per-unit cost instead of a
/// `PerUnitFromTotal` rebuilt from the spec, an undated one books where it used
/// to fail with "No matching lot", and a wrong total fails where it used to
/// book. `ParsedLedger` and `Ledger` both archive booked directives and their
/// errors, so a v22 blob would serve the old answer for all three.
/// v24: loader v36, the trailing `*` merge marker (#2329), which changes
/// parsed directives. The same bump also covers booking changes merged since
/// v23 without one, each of which changes the BOOKED directives and errors
/// this cache archives: same-transaction shorts (#2368, #2379), zero-netted
/// lots and undated pools (#2378, #2385), a cost naming only its own side
/// (#2384, #2391), AVERAGE pooling one side (#2393, #2395), and cost-less
/// units no longer matched by a cost spec (#2396, #2397). A v23 blob can
/// serve the pre-fix answer for any of them.
/// v25: `LedgerPayload` gained `booking_method` (#2386), an archived LAYOUT
/// change. Loader v36, unchanged: the loader already archives `set_options`,
/// which is what its `Ledger::booking_method` is derived from.
/// v26: `LedgerPayload` gained `summary_account_names` (#2401), another
/// archived LAYOUT change. Loader v36, unchanged: the loader already archives
/// the `account_previous_*` options they come from.
/// v27: `summary_account_names` grew from three names to six (the current
/// earnings and conversions accounts and the conversion currency, #2406). The
/// layout did not move, but a v26 blob's three names fail the new arity and
/// would silently fall back to beancount's defaults, so it must not be read.
/// v28: loader v37, the account-name options read as leaves under a root
/// (#2408). `LedgerPayload::summary_account_names` archives the RESOLVED names,
/// and a set value resolves differently now (`Equity:Anfang` names
/// `Equity:Equity:Anfang`, as in beancount), so a v27 blob would serve the old
/// names.
/// v29: a `{*}` merge spec's cost, currency, date or label is checked against
/// the merged pool instead of dropped (#2398). The layout did not move, but a
/// restored `Ledger` skips booking and serves its cached errors, so a v28 blob
/// of a ledger stating a wrong pool cost would go on reporting none.
/// v30: a `{*}` that runs no merge (on a buy, a sale from an empty account,
/// or any sale on a NONE account) is refused instead of booked with the `*`
/// dropped (#2418). A v29 blob restores such a ledger's errors as none.
/// v31: a sale of a whole AVERAGE or `{*}` pool books its exact total as
/// `PerUnitFromTotal` instead of the rounded average as `PerUnit` (#2417). A
/// v30 blob would serve the old booked cost and its 1E-26 imbalance.
/// v32: a lot keeps its exact total, so a sale that empties a `{{T}}` lot
/// books that total, and a partial sale of such a lot or of a pool books a
/// basis fitted to it (#2425). A v31 blob serves the old booked costs.
/// v33: a units number written without its currency (`Assets:Foo  42.50`)
/// takes its currency by beancount's rule, including from the account's
/// running balance (#2465). Loader v37, unchanged -- the loader archives
/// parsed directives, and those did not move. The booked ones did, in both
/// directions: a ledger that failed with "cannot infer currency" now books,
/// and one whose currency was read off the residual now fails. `ParsedLedger`
/// and `Ledger` archive booked directives and their errors, so a v32 blob
/// would keep serving the old answer.
/// v34: a reduction whose take, lot or running total needs more digits than
/// `Decimal` holds is an overflow error instead of a rounded booking (#2554):
/// selling `MAX` from lots of `0.48` and `MAX` drained both, and now fails;
/// STRICT's total match is decided exactly, so a sale that only rounded to the
/// lots' total is now ambiguous. Loader v37, unchanged -- parsed directives
/// did not move. A v33 blob would serve the old booked lots with no error.
/// v35: an entry with no source location (one a plugin inserted) sorts first
/// among same-date, same-type entries instead of last (#2553). Loader v37,
/// unchanged -- the loader archives parsed directives, which have no such
/// entries. `Ledger` archives the processed, sorted directives, so a v34 blob
/// would keep serving the old order.
/// v36: loader v38, tags and links are a sorted, deduplicated set (#2545) and
/// `pushtag` reaches `document` and `note` entries (#2544). Parsed directives
/// changed, so a v35 blob would serve tags in written order with duplicates.
/// v37: a cost spec written without a currency (`{}`) takes the one
/// beancount's rule gives it before any lot is matched, and a reduction priced
/// in another currency than its cost is refused (#2571). Loader v38,
/// unchanged -- parsed directives did not move. A sale that sold a EUR lot
/// for USD cash now fails, so a v36 blob would serve its old booked lots and
/// no error.
/// v38: a tolerance needing more digits than a `Decimal` holds is rounded down
/// for the balance check, and interpolation keeps a quantized amount only
/// within it, booking the exact amount otherwise (#2582). Loader v38,
/// unchanged -- parsed directives did not move. `Ledger` archives booked
/// directives and their errors, so a v37 blob would serve the old amount, or
/// no E3001 where one is now reported.
/// v39: a cost written on an AVERAGE sale is checked against the pool's
/// average (#2603). Loader v38, unchanged -- parsed directives did not move.
/// A sale stating a cost its pool is not now fails, so a v38 blob would serve
/// its old booked lots and no error.
/// v40: a total price (`@@`) on a sale booked across several lots gives each
/// split posting the whole sale's per-unit price, `total / units sold`,
/// instead of keeping the total for `normalize_prices` to divide by the
/// split's own units (#2569). Loader v38, unchanged -- parsed directives did
/// not move. `Ledger` archives booked directives, so a v39 blob would serve
/// the old, multiplied price.
/// v41: a date or label written on an AVERAGE sale's cost spec is refused
/// instead of dropped (#2627). Loader v38, unchanged -- parsed directives did
/// not move. A restored `Ledger` skips booking and serves its cached errors,
/// so a v40 blob of such a ledger would go on reporting none.
/// v42: `noduplicates` compares every directive type but `price`, not only
/// transactions (#2599). Loader v38, unchanged -- parsed directives did not
/// move. `Ledger` runs the regular plugins and archives their errors, so a
/// v41 blob of a ledger with a repeated `note` (or `open`, `balance`, ...)
/// would serve no error where `noduplicates` now reports one.
/// v43: loader v39, a `#tag` / `^link` line after a transaction's first
/// posting is a parse error and its tags are dropped (#2575). Parsed
/// directives changed, so a v42 blob would serve the late tags and no error.
/// v44: `event` and `custom` share the transaction `DirectivePriority`, so a
/// same-date `event` or `custom` keeps its file position among transactions
/// (#2576). Loader v39, unchanged -- parsed directives did not move. `Ledger`
/// archives the processed, sorted directives, so a v43 blob would serve the
/// old order (a same-date `custom` after the date's transactions and `close`).
/// v45: a sale written with its units elided is booked as the same sale
/// with its units written: its lots are matched and its disposal recorded,
/// and an AVERAGE one carries the pool's exact cost (#2647). Loader v39,
/// unchanged -- parsed directives did not move. `Ledger` archives booked
/// directives, so a v44 blob would serve the old, unmatched posting.
/// v46: loader v40, a header-line comment stays off the first posting after
/// a blank line or comment (#2628), and `\b` / `\f` in strings decode to
/// U+0008 / U+000C (#2672). Parsed directives changed, so a v45 blob would
/// serve the misplaced comment and the old strings.
/// v47: a per-unit number booking derives from a total (`{{T}}`,
/// `{per # total}`, `@@`, an interpolated `{}` cost) is divided as Python's
/// `decimal` divides it (#2652): `{{10 USD}}` over 4 units is `2.5`, not
/// `2.50`, and over 3 is `3.333333333333333333333333333` (28 significant
/// digits), not `3.3333333333333333333333333333`. Loader v40, unchanged --
/// parsed directives did not move. `Ledger` archives booked directives, so a
/// v46 blob would serve the old per-unit costs and prices.
/// v48: loader v41, a file's includes resolve next to the path it was opened
/// by, symlinks kept (#2635); `HostFs` no longer resolves them next to the
/// `realpath`. A v47 blob of a ledger reached through a symlink would serve
/// the directives of the files next to the link's target.
/// v49: `commodity`, `note`, `query` and `price` share the transaction
/// `DirectivePriority`, so a same-date one keeps its file position among
/// transactions (#2629). Loader v40, unchanged -- parsed directives did not
/// move. `Ledger` archives the processed, sorted directives, so a v48 blob
/// would serve the old order (a same-date `price` after the date's
/// transactions, a `commodity` before its balances).
/// v50: a lot-matching booking failure carries its E4xxx code instead of
/// `BOOK` (#2631). Loader v41, unchanged -- parsed directives did not move.
/// `LedgerPayload.errors` is restored verbatim, so a v49 blob would serve
/// `BOOK` where a fresh load gives E4001-E4004.
/// v51: `inferred_tolerance_default "*"` is the tolerance of a currency left
/// with none, not a floor on every currency (#2685). Loader v41, unchanged --
/// parsed directives did not move. Booking quantizes interpolated amounts
/// with that tolerance and validation checks the balance against it, so a
/// v50 blob of a ledger setting `*` would serve the old interpolated amounts
/// and miss the imbalance errors a fresh load reports.
/// v52: a `{{total}}` cost over so many units that its per-unit needs more
/// than 28 decimal places books, with its exact total, instead of failing as
/// out of range (#2689). Loader v41, unchanged -- parsed directives did not
/// move. `Ledger` archives booked directives and errors, so a v51 blob would
/// serve the refusal and the posting left unbooked.
/// v55: a sale past the end of a lot its own transaction emptied is dated
/// with the transaction's date, as beancount dates it (#2390). Loader v41,
/// unchanged -- parsed directives did not move. `Ledger` archives booked
/// directives, so a v52 blob would serve the short's cost left undated. The
/// recorded `Posting::booking` decisions are NOT archived (they are skipped
/// by serde and rkyv), so a restored `Ledger` re-derives each one as before
/// #2390; this bump is for the dated short. v53 landed with `fix/tolerance-cost-cap`
/// (#2717) and v54 with `fix/plugin-placeholder-locations` (#2713); the
/// bumps kept DISTINCT numbers, so a blob written between the merges is
/// regenerated.
/// v57: `Posting`/`Transaction` keep their `meta` map and comment lists
/// boxed-while-nonempty (`MetaMap`/`CommentList`). Loader v42, MOVED --
/// both caches archive the same directives and the fields' archived
/// shape went from a bare map/`Vec` to `Option<Box<..>>`, so a v55 blob
/// reads the new structs at the wrong offsets. The number skips v56:
/// `fix/option-assignment-fee-window-guard` (handed over `569cf8099b`)
/// claimed v56 first for its plugin-error archive change, and parallel
/// bumps keep DISTINCT numbers (see v55's note).
/// v58: every variant's `meta` map is a `MetaMap` and `SortedSet` holds
/// its elements in an `Option<Box<Vec<T>>>`, mirroring loader v43. The
/// archived fields moved the same way v57's did, so a v57 blob reads the
/// new structs at the wrong offsets.
/// v59: loader v44, PARSER OUTPUT changed (#2769). A CRLF `#` comment no
/// longer claims its line ending's `\r`, so spans around it move by a byte
/// and files that failed with P0012 now parse clean; a v58 blob would keep
/// serving the old spans and the archived `parse_errors`.
/// v60: loader v45, PARSER OUTPUT changed (#2775). A `"` in a column-0 `#`
/// comment no longer swallows the directives after it; those files parsed
/// with no errors, so a v59 blob would keep serving them without the
/// swallowed directives.
/// v61: loader v46, PARSER OUTPUT changed (#2778). A `"` in an org-mode `*`
/// heading no longer swallows the directives after it; those files parsed
/// with no errors, so a v60 blob would keep serving them without the
/// swallowed directives.
/// v62: loader v47, PARSER OUTPUT changed (#2783). An indented top-level `*`
/// line is now an error instead of a silenced heading; such a file parsed
/// clean, so a v61 blob would keep serving it without the error.
/// v63: loader v48, PARSER OUTPUT changed (#2784). The directives after an
/// unterminated `"` are kept; a v62 blob (which archives the parse errors
/// and directives) would keep serving the file without them.
/// v64: loader v49, PARSER OUTPUT changed (#2774). A stray `\r` before a
/// line ending is trivia instead of an error; a v63 blob (which archives the
/// parse errors) would keep serving such a file with them.
/// v65: loader v50, PARSER OUTPUT changed (#2802). A stray token on a
/// non-transaction header line is a parse error, and `/6J` is one currency;
/// a v64 blob would keep serving such a file without the error or the
/// currency.
/// v66: loader v51, PARSER OUTPUT changed (#2802, stage 2). A stray token on a
/// metadata line is a parse error; a v65 blob would keep serving such a file
/// without the error.
/// v67: loader v52, PARSER OUTPUT changed (#2806, #2812). `custom` values
/// evaluate arithmetic and `pushmeta` values read like metadata values; a v66
/// blob would keep serving the old split values.
/// v68: loader v53, PARSER OUTPUT changed (#2802, stage 3). A stray token in a
/// transaction or posting line is a parse error, and `!Assets:A` and `--1 USD`
/// parse; a v67 blob would keep serving such a file without the error, or
/// with one.
/// v69: loader v54, PARSER OUTPUT changed. A posting whose cost and price
/// currencies are both written and differ is a parse error, a purchase too; a
/// v68 blob would keep serving such a purchase without the error.
/// v70: loader v55, PARSER OUTPUT changed (#2811). A value date that is not a
/// real calendar date, and a year-0 date, are parse errors; a v69 blob would
/// keep serving such a file without the error.
/// v71: loader v56, PARSER OUTPUT changed (#2812). Pushed metadata reaches
/// transactions only, and a transaction's own key wins over a pushed one; a v70
/// blob would keep serving the old attachment.
/// v72: the `ParsedLedger` payload gained `directive_spans` and `placeholders`
/// (the source map's placeholder locations), so a restored ledger's queries
/// resolve the `filename` / `lineno` / `location` columns and still name the
/// plugin that created a directive (`<auto_accounts>`, 0) (#2825). Loader
/// output is unchanged; a v71 blob has neither and would not deserialize as
/// this layout.
/// v73: loader v57, PARSER OUTPUT changed (#2808, #2856). A date with extra
/// digits is one date, as in beancount, and every invalid date is reported; a
/// v72 blob would keep serving such a file with its old errors.
/// v74: loader v58, PARSER OUTPUT changed (#2779). A column-0 `!`, `&`, `?` or
/// `:` line is ignored and a bare `#`, `%` or `*` line is an error, as in
/// beancount; a v73 blob would keep serving such a file with its old errors.
/// v75: the `Ledger` payload gained `query_refused`, whether an error that
/// blocks queries (`LedgerError::blocks_queries`) stops them (#2861); the
/// restored `errors` no longer carry that flag. Loader output is unchanged; a
/// v74 blob has no such field and would not deserialize as this layout.
/// v76: loader v59, PARSER OUTPUT changed (#2787). A line's overlapping
/// errors are reported once, as in beancount; a v75 blob would keep serving
/// such a file with its old errors.
/// v77: loader v60, PARSER OUTPUT changed (#2813). `True`/`true` are not
/// booleans, and indented lines after `option`-like directives and posting
/// `filename:`/`lineno:` are errors, as in beancount; a v76 blob would keep
/// serving such a file with its old values and no error.
/// v78: the `ParsedLedger` payload gained `query_refused`, whether an error
/// that blocks queries (`LedgerError::blocks_queries`) stops them (#2882); a
/// restored ledger refused on any load error. Loader output is unchanged; a
/// v77 blob has no such field and would not deserialize as this layout.
/// v79: loader v60, unchanged. What moved is `Ledger`'s error list: an
/// invalid account name among a `custom` directive's values is `E1005`, and a
/// `pad` reports an unopened or invalid source behind an unopened target
/// (#2809). `fromCache` restores the errors verbatim, so a v78 blob would keep
/// serving such a ledger without them.
/// v80: loader v61, ARCHIVED LAYOUT moved (#2835). `Metadata` is a vector of
/// entries with interned keys, in source order, where it was a hash map; a v79
/// blob would be read at the wrong offsets.
/// v81: loader v61, unchanged. `Ledger`'s error list moves: a `pad` after its
/// account's close is `E1003`, and a pad with an unopened account still pads,
/// so it no longer adds an `E2001` balance failure or loses its `Unused Pad
/// entry`. A v80 blob would keep serving the old errors.
/// v82: loader v62, PARSER OUTPUT changed (#2893). A metadata key repeated on
/// a transaction or a posting keeps its first value and is a parse error, as
/// in beancount; a v81 blob would keep serving the last value.
/// v84: loader v63, PARSER OUTPUT changed (#2872). An invalid token runs to the
/// next blank, as in beancount, and each one on a line is reported; an older
/// blob would keep serving such a file with its old errors and values.
/// v85: loader v63, unchanged. `Ledger`'s error list moves (#2896): a balance
/// on an unopened account is compared (`E2001`), a pad whose balance already
/// held or that a later pad superseded is an `Unused Pad entry` and pads
/// nothing later, `E2004` is no longer reported, a balance on a pad's source
/// sees the padding from the pad's date, and an account referenced before its
/// later `open` is inactive. A v84 blob would keep serving the old errors.
/// (v83 was never released: #2896 held it before #2872 took v84.)
/// v86: loader v65, PARSER OUTPUT changed (#2905). A transaction with no flag
/// after its date is a parse error, as in beancount; an older blob would keep
/// serving such a file with no error.
/// v87: loader v66, PARSER OUTPUT changed (#2906). Any non-ASCII character
/// starts an account component, as in beancount, so `Assets:٣Foo` is one
/// account; an older blob would keep serving such a file with its old errors.
/// v89: loader v67, PARSER OUTPUT changed (#2910). A BOM inside a string
/// literal or a comment, or glued into an account, is content, as in
/// beancount; an older blob would keep serving such a file with a
/// `BomInDirectiveBody` error.
/// v90: loader v68, LOADER OUTPUT changed (#2911). An option value its
/// converter rejects is no longer applied, so the archived account-type names
/// keep the default root and `Ledger`'s error list loses the errors the
/// rejected rename caused (`E1005` on `open Equity:A` under
/// `option "name_equity" "capital"`), and a ledger whose `booking_method` was
/// rejected now has `query_refused` set; an older blob would keep serving the
/// old names, errors and answers.
/// v92: loader v69, LOADER OUTPUT changed (#2925). Option values are read as
/// beancount reads them, so the archived error list moves: a valid
/// `account_rounding` no longer raises `E7007`, an unrecognized boolean word
/// is the `E7011` warning instead of an `E7002` error, `option "plugin"` is
/// `E7005` instead of `E7004`, the two dead tolerance options are `E7001`, and
/// the tolerance maps accept `A:B:0.01` and reject `USD:-0.01`. An older blob
/// would keep serving the old errors. (v91 is held by #2920.)
/// v94: loader v69, unchanged. ARCHIVED LAYOUT moved: the `Ledger` payload
/// gained `tolerance_multiplier`, which the padding a query inserts measures a
/// balance's tolerance with, and `directive_lines` and `directive_file_ranks`,
/// each directive's line and its file's place in the load, for the pad
/// expansion's entry order (#2901); an older blob has none of them. And both
/// payloads' error lists move: a pad pads for a balance on a sub-account and
/// counts only its own padding, a difference within the balance's tolerance
/// is not padded (an `Unused Pad entry`), and padding a currency held at cost
/// is `E2005`; a `ParsedLedger`'s validation errors also carry their own
/// lines, columns and spans, as it validates with its spans, and it validates
/// with the ledger's options (`tolerance_multiplier` among them), as
/// `rledger check` does. The `open`s `auto_accounts` and `currency_accounts`
/// make are at new lines (their place in the plugin's sorted list, as in
/// beancount), so the archived lines and error locations for them move.
/// (v88 and v91 were never released: #2920 held v88 before #2926 took v89,
/// and held v91 before #2930 took v92. v93 was never released.)
/// v97: loader v69, unchanged. Both payloads' error lists move (#2937): an
/// account closed with a balance is no longer reported (E1004 is
/// advisory-only, as in `rledger check`), and a `ParsedLedger` validates
/// after a booking error, setting the refused transaction aside, so it
/// reports the `Balance failed` that follows one. An older blob would keep
/// serving the old errors. (v95 was held by #2931 and never released; v96
/// was never released.)
/// v99: loader v71 (#2925). Both payloads' option diagnostics move: each
/// carries its option's line, and a `Ledger`'s its file too, and an invalid
/// option in an included file is its converter's error (`E7002`, `E7008`,
/// ...) instead of the `E7009` warning, which is left for a value the
/// converter accepts. The loader also ignores a `documents` option in an
/// included file (`E7009`), so it no longer scans that root. An older blob would keep serving them with
/// no location and the old codes, and a `Ledger` with such an option as
/// valid. (v98 was never released.)
/// v102: loader v73, PARSER OUTPUT changed (#2932). An invalid token after a
/// lone header string moves it to no other field, so `* "p" <bad>` keeps
/// payee `p` where `p` was the narration; an older blob would keep serving
/// the shifted fields. (v100 was held by #2931 and never released.)
/// v103: loader v73, unchanged. Both payloads move (#2949): a source with a
/// parse error is booked and validated over the entries that did parse, as
/// `rledger check` validates it, so a `ParsedLedger` archives those
/// directives and their validation errors where it archived none, and a
/// `Ledger` archives each parse error with its code and line where it
/// archived one line-less `parse errors in <path>`. An older blob would keep
/// serving the old errors: a `ParsedLedger` with no directives and no
/// validation errors for a source with a parse error, and a `Ledger` with one
/// line-less parse error per file. (v101 was never released; v104 was held by
/// #2931 and never released.)
/// v105: loader v73, unchanged. ARCHIVED LAYOUT moved (#2946): the
/// `ParsedLedger` payload gained `query_option_errors` and the `Ledger` payload
/// `query_errors`, what a query lists, in which a rejected `booking_method`'s
/// E7002 is the refusal that says why the query does not answer
/// (`Ledger::query_option_errors`, as the FFI lists it). A v103 blob holds
/// neither, so it is read at the wrong offsets. The `ParsedLedger` payload
/// also carries its parse and validation errors at character columns now,
/// where a byte column read high after a BOM or a multi-byte character.
/// (v104 was held by #2931 and never released.)
/// v107: loader v73, unchanged. A `Ledger`'s error list moves (#2959): an
/// include cycle's `LOAD` error carries the file and line of the `include`
/// that closed it, where it had no location. An older blob would keep
/// serving it with none. (v106 was held by #2931 and never released.)
/// v110: loader v73, unchanged; PARSER OUTPUT changed (#2931, for #2928). A
/// BOM in the middle of a line starts an invalid token that runs to the next
/// blank, as in beancount, so a quote after it opens no string. Every input
/// that changes has a parse error, so the loader's cache, saved only for an
/// error-free load, holds none of them; both payloads here archive a source
/// with parse errors, and an older blob would keep serving such a file with
/// its old errors and values. (v104 and v106 were held by #2931 and never
/// released; v108 is held by #2970 and v109 by #2971.)
pub const CACHE_VERSION: u32 = 110;

/// The `rustledger-loader` cache version this one was last reconciled with.
///
/// Both caches archive the same parsed `Vec<Directive>`. A parser change that
/// alters PARSER OUTPUT therefore invalidates both, and bumping only one leaves
/// the other serving stale directives on a build that has the fix.
///
/// That is not hypothetical: on #1942 (cost-spec arithmetic) only the loader
/// version moved, and a stale WASM blob would have kept serving a truncated
/// cost basis. It was caught in review, by a person, not by anything here.
///
/// So this pins the pair. If the assertion below fails, ask which kind of
/// change moved the loader version:
///
///   parser OUTPUT changed  -> bump `CACHE_VERSION` above too, then update
///                             this pin to match
///   archived LAYOUT changed -> bump `CACHE_VERSION` above too. Same answer as
///                             an output change and for a sharper reason: the
///                             values agree, so nothing downstream would look
///                             wrong, while the bytes are read at the wrong
///                             offsets (v15 / loader v29, boxing
///                             `Posting::cost`)
///   loader-internal only   -> only update this pin (layout of a loader-side
///                             struct moved; our archived directives did not)
///
/// The question is the point; the pin exists to force it to be asked.
/// Test-only: the pin exists to be asserted, and gating it keeps a non-test
/// build free of a constant nothing reads. The doc above stays here rather
/// than in the test module so a reader of this file meets the contract next
/// to `CACHE_VERSION`, which is the thing they came to change.
#[cfg(test)]
const LOADER_CACHE_VERSION_PIN: u32 = 73;

/// Magic bytes for [`ParsedLedgerPayload`] cache blobs.
pub const MAGIC_PARSED: &[u8; 8] = b"WLPARSED";

/// Magic bytes for [`LedgerPayload`] cache blobs.
pub const MAGIC_LEDGER: &[u8; 8] = b"WLLEDGER";

/// Header size: 8 (magic) + 4 (version).
const HEADER_SIZE: usize = 12;

// =============================================================================
// Payload types
// =============================================================================

/// Cache payload for a [`super::parsed_ledger::ParsedLedger`].
#[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct ParsedLedgerPayload {
    pub directives: Vec<Directive>,
    /// Each directive's span and file id, so a restored ledger's queries
    /// still resolve the source columns (#2825).
    pub directive_spans: Vec<(rustledger_core::Span, u16)>,
    /// The source map's placeholder locations (name, line), in id order, so
    /// the restored map gives each the id `directive_spans` holds (#2825).
    pub placeholders: Vec<(String, u32)>,
    pub options: LedgerOptions,
    pub parse_errors: Vec<Error>,
    /// Option diagnostics, archived apart from `parse_errors` because the
    /// restored ledger gates its operations on that list and must not refuse
    /// a query over an invalid option.
    pub option_errors: Vec<Error>,
    /// The option diagnostics a query lists (`Ledger::query_option_errors`):
    /// a rejected `booking_method`'s E7002 is the refusal (#2929).
    pub query_option_errors: Vec<Error>,
    pub validation_errors: Vec<Error>,
    /// Whether a query over the ledger refuses (`LedgerError::blocks_queries`,
    /// #2882: a parse error or a booking failure). The archived
    /// `parse_errors` do not carry the flag, so it is archived beside them.
    pub query_refused: bool,
}

/// Cache payload for a [`super::parsed_ledger::Ledger`].
#[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct LedgerPayload {
    pub directives: Vec<Directive>,
    pub options: LedgerOptions,
    /// Configured account-type roots as `[assets, liabilities, equity,
    /// income, expenses]` — `name_*` renames must survive the cache or
    /// `fromCache` ledgers silently misclassify in BQL (the L5 class).
    /// Plain strings rather than `rustledger_core::AccountTypes` so the
    /// rkyv derive stays local to this crate.
    pub account_type_names: Vec<String>,
    /// The effective booking method (`BookingMethod`'s `Display` form), the
    /// default BQL realizes with. Without it a `fromCache` ledger booked
    /// under `option "booking_method" "NONE"` would replay as STRICT and
    /// refuse `BALANCES` (#2386). A string for the same reason as above.
    pub booking_method: String,
    /// The `tolerance_multiplier` option (`Decimal`'s `Display` form), which
    /// the padding a query inserts measures a balance's tolerance with
    /// (#2901). A string for the same reason as above.
    pub tolerance_multiplier: String,
    /// Each directive's line as beancount numbers it, parallel to
    /// `directives`, for the pad expansion's entry order (#2901): a restored
    /// ledger has no spans to read them from.
    pub directive_lines: Vec<u32>,
    /// Each directive's file's place in the load, parallel to `directives`
    /// (`rustledger_booking::SourcePosition::file_rank`), which breaks a tie
    /// on the line in that order.
    pub directive_file_ranks: Vec<u32>,
    /// `[previous_balances, previous_earnings, previous_conversions,
    /// current_earnings, current_conversions, conversion_currency]`, what
    /// `FROM ... OPEN ON / CLOSE / CLEAR` summarize into (#2401, #2406). Plain
    /// strings for the same reason as `account_type_names`.
    pub summary_account_names: Vec<String>,
    pub errors: Vec<Error>,
    /// What a query lists: `errors` with the option diagnostics as a query
    /// lists them (`Ledger::query_option_errors`, #2929).
    pub query_errors: Vec<Error>,
    /// Whether a query over the ledger refuses (`LedgerError::blocks_queries`,
    /// #2861: a parse error, a file that could not be read or decrypted, a
    /// booking failure). Archived because
    /// `errors` lost the flag in conversion.
    pub query_refused: bool,
}

// =============================================================================
// Encode / decode
// =============================================================================

/// Validate and strip the cache header, checking the expected magic bytes.
fn strip_header(bytes: &[u8], expected_magic: [u8; 8]) -> Result<&[u8], String> {
    if bytes.len() < HEADER_SIZE {
        return Err("Invalid cache: data too short".to_string());
    }
    let (header, data) = bytes.split_at(HEADER_SIZE);
    if header[..8] != expected_magic {
        return Err("Invalid cache: wrong payload type or unrecognized magic bytes".to_string());
    }
    // `header` is exactly `HEADER_SIZE` (12) bytes — the length was checked
    // above — so bytes 8..12 are always present (no panic, no unwrap).
    let version = u32::from_le_bytes([header[8], header[9], header[10], header[11]]);
    if version != CACHE_VERSION {
        return Err(format!(
            "Cache version mismatch: expected {CACHE_VERSION}, got {version}. Re-parse the ledger."
        ));
    }
    Ok(data)
}

/// Prepend the cache header to rkyv-serialized data.
fn prepend_header(magic: [u8; 8], data: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(HEADER_SIZE + data.len());
    result.extend_from_slice(&magic);
    result.extend_from_slice(&CACHE_VERSION.to_le_bytes());
    result.extend_from_slice(data);
    result
}

/// Copy an archive into a buffer aligned for every archived type before
/// rkyv reads it in place (#2934).
///
/// `rkyv::from_bytes` validates and reads the archive where it lies, so each
/// archived value must sit at its own alignment in memory. `ArchivedMetaValue`
/// needs 8 (its `Int(i64)` variant), and every `custom` directive and metadata
/// entry archives one. The archive starts [`HEADER_SIZE`] (12) bytes into the
/// blob, so even in a 16-aligned blob those values sat 4 bytes off and every
/// such ledger failed with `unaligned pointer`. Nor is the blob itself aligned:
/// wasm-bindgen copies a JS `Uint8Array` into wasm memory with alignment 1,
/// and a native caller may hand in any slice. So rather than pad the header,
/// which would still depend on where the caller's bytes happen to lie, the
/// payload is copied into an [`rkyv::util::AlignedVec`], aligned to 16, the
/// alignment `rkyv::to_bytes` writes the archive for. The copy is one
/// `memcpy` of the blob, small beside the deserialization that follows, and
/// leaves the cache format unchanged.
///
/// Memory: while it lives, the copy holds a second blob-sized buffer beside
/// the caller's bytes (which wasm-bindgen has already copied in) and the
/// directives being built. Under wasm32 that peak sets the instance's linear
/// memory high-water mark, and linear memory never shrinks, so restoring a
/// cache grows the instance by about one more blob size than it did before.
fn aligned_payload(data: &[u8]) -> rkyv::util::AlignedVec {
    let mut aligned = rkyv::util::AlignedVec::with_capacity(data.len());
    aligned.extend_from_slice(data);
    aligned
}

/// Serialize a [`ParsedLedgerPayload`] to bytes.
pub fn serialize_parsed(payload: &ParsedLedgerPayload) -> Result<Vec<u8>, String> {
    let data = rkyv::to_bytes::<rkyv::rancor::Error>(payload)
        .map_err(|e| format!("Serialization failed: {e}"))?;
    Ok(prepend_header(*MAGIC_PARSED, &data))
}

/// Deserialize a [`ParsedLedgerPayload`] from bytes.
pub fn deserialize_parsed(bytes: &[u8]) -> Result<ParsedLedgerPayload, String> {
    let data = aligned_payload(strip_header(bytes, *MAGIC_PARSED)?);
    rkyv::from_bytes::<ParsedLedgerPayload, rkyv::rancor::Error>(&data)
        .map_err(|e| format!("Deserialization failed: {e}"))
}

/// Serialize a [`LedgerPayload`] to bytes.
pub fn serialize_ledger(payload: &LedgerPayload) -> Result<Vec<u8>, String> {
    let data = rkyv::to_bytes::<rkyv::rancor::Error>(payload)
        .map_err(|e| format!("Serialization failed: {e}"))?;
    Ok(prepend_header(*MAGIC_LEDGER, &data))
}

/// Deserialize a [`LedgerPayload`] from bytes.
pub fn deserialize_ledger(bytes: &[u8]) -> Result<LedgerPayload, String> {
    let data = aligned_payload(strip_header(bytes, *MAGIC_LEDGER)?);
    rkyv::from_bytes::<LedgerPayload, rkyv::rancor::Error>(&data)
        .map_err(|e| format!("Deserialization failed: {e}"))
}

// =============================================================================
// Source fingerprinting
// =============================================================================

/// Compute a SHA-256 fingerprint of one or more source strings.
///
/// Returns the hash as a lowercase hex string. Store this alongside cached
/// bytes and compare on the next load; if the fingerprint changed, discard
/// the cache.
///
/// Sources are separated by NUL bytes so `["ab", "c"]` differs from `["a", "bc"]`.
pub fn hash_sources(sources: &[&str]) -> String {
    use sha2::{Digest, Sha256};
    use std::fmt::Write as _;

    let mut hasher = Sha256::new();
    for source in sources {
        hasher.update(source.as_bytes());
        hasher.update(b"\x00");
    }
    let result = hasher.finalize();
    result.iter().fold(String::with_capacity(64), |mut acc, b| {
        let _ = write!(acc, "{b:02x}");
        acc
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {

    /// The two caches archive the same parsed directives, so they have to move
    /// together whenever PARSER OUTPUT changes.
    ///
    /// This is the guard for the failure that actually happened on #1942: the
    /// loader version was bumped, this one was not, and a stale WASM blob would
    /// have served a truncated cost basis on a fixed build. Review caught it;
    /// nothing in the test suite did.
    #[test]
    fn loader_cache_version_is_pinned() {
        assert_eq!(
            rustledger_loader::cache::CACHE_VERSION,
            LOADER_CACHE_VERSION_PIN,
            "the rustledger-loader cache version moved and this one did not. \
             If PARSER OUTPUT changed, bump CACHE_VERSION in this file too and \
             then update LOADER_CACHE_VERSION_PIN to match. If the loader \
             change was internal to the loader (its own struct layout) and our \
             archived directives are unaffected, update the pin alone. See \
             #1942, where only the loader moved and a stale blob would have \
             kept serving a truncated cost basis.",
        );
    }

    /// Pin the archived form of every `Directive` variant.
    ///
    /// The pin above only forces a QUESTION, and on #2160 the question got the
    /// wrong answer: `Note` gained `tags` and `links`, the loader version and
    /// the pin both moved, `CACHE_VERSION` did not, and every test still
    /// passed. A pin cannot tell a loader-internal change from one that moves
    /// our archived directives -- only a person can, and that person was me.
    ///
    /// This can tell. It parses one of every directive kind and hashes the
    /// archived bytes, so ANY change to how a directive is archived -- a new
    /// field (layout) or a different value in an existing one (output) --
    /// moves the digest and fails here. Both are exactly the cases that
    /// require `CACHE_VERSION` to move, which is what the message says to do.
    ///
    /// The blank lines before `note` and `document` are load-bearing: without
    /// them this test cannot see a directive's tags being dropped, because a
    /// directive that follows another one directly never hit that bug. Written
    /// without them, it passed while the defect was reintroduced.
    ///
    /// The transaction and its first posting carry metadata. Before #2835
    /// `Metadata` was an `FxHashMap`, and a hash over its archived bytes would
    /// have pinned an iteration order rather than a layout, so the fixture had
    /// none; it is an insertion-ordered vector now, so its layout is pinned
    /// here like every other field. Directives are archived one at a time, so
    /// nothing here depends on the encoding of the outer `Vec`.
    #[test]
    fn directive_archived_form_is_pinned() {
        // Moved for the `MetaMap`/`CommentList` boxing: `Posting` and
        // `Transaction` archive their meta map and comment lists as
        // `Option<Box<..>>` where they were a bare map/`Vec`. That is a
        // layout change, not an output one -- the fixture's values parse
        // the same, the bytes sit at different offsets.
        //
        // Moved again for the variant `MetaMap`/`SortedSet` boxing (loader
        // v43): same shape move on the other directives' meta maps and on
        // every tag/link set.
        //
        // Moved for #2835 (loader v61): `Metadata` is an ordered vector with
        // interned keys, and the fixture gained metadata to pin it.
        const DIRECTIVE_LAYOUT_HASH: u64 = 0x2e4f_9512_8c52_9246;

        // One of every `Directive` variant, in declaration order.
        let src = "\
2024-01-05 * \"payee\" \"narration\" #t ^l\n\
\x20\x20source: \"bank\"\n\
\x20\x20ref: 42\n\
\x20\x20Assets:Bank  10.00 USD {2.00 USD} @ 3.00 USD\n\
\x20\x20\x20\x20memo: \"in\"\n\
\x20\x20Equity:Opening-Balances\n\
2024-01-06 balance Assets:Bank  10.00 ~ 0.01 USD\n\
2024-01-01 open Assets:Bank USD,EUR \"STRICT\"\n\
2024-01-31 close Assets:Bank\n\
2024-01-01 commodity USD\n\
2024-01-04 pad Assets:Bank Equity:Opening-Balances\n\
2024-01-07 event \"location\" \"Paris\"\n\
2024-01-08 query \"q\" \"SELECT date\"\n\
\n\
2024-01-09 note Assets:Bank \"n\" #nt ^nl\n\
\n\
2024-01-10 document Assets:Bank \"/x.pdf\" #dt ^dl\n\
2024-01-11 price USD 1.10 EUR\n\
2024-01-12 custom \"budget\" Assets:Bank 10.00 USD\n";

        let parsed = rustledger_parser::parse(src);
        assert!(
            parsed.errors.is_empty(),
            "fixture must parse cleanly, else the digest pins an error path: {:?}",
            parsed.errors,
        );

        // Every variant, or the pin has a blind spot exactly where a new
        // variant would be added.
        // `Directive::type_name`, not `Debug` on `mem::Discriminant`: that
        // format is not a documented guarantee, and a std that printed every
        // discriminant identically would turn this coverage check into a
        // baffling failure. `type_name` also names the missing variant.
        let kinds: std::collections::BTreeSet<&str> = parsed
            .directives
            .iter()
            .map(|d| d.value.type_name())
            .collect();
        assert_eq!(
            kinds.len(),
            12,
            "fixture must cover all 12 Directive variants, got {kinds:?}"
        );

        // FNV-1a: a checked-in constant needs an algorithm that is stable
        // across toolchains, which `DefaultHasher` is not promised to be.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        let mut eat = |bytes: &[u8]| {
            for b in bytes {
                h ^= u64::from(*b);
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
        };
        for d in &parsed.directives {
            let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&d.value).unwrap();
            // Length-prefixed so a byte crossing a directive boundary cannot be
            // masked by a compensating change in its neighbor.
            eat(&(bytes.len() as u64).to_le_bytes());
            eat(&bytes);
        }

        assert_eq!(
            h, DIRECTIVE_LAYOUT_HASH,
            "the archived form of a directive changed -- a field was added or \
             removed (layout), or the parser now produces a different value \
             (output). Either way a cache written by an older binary is no \
             longer safe to read: bump CACHE_VERSION in this file, reconcile \
             LOADER_CACHE_VERSION_PIN, and set DIRECTIVE_LAYOUT_HASH to {h:#x}",
        );
    }

    /// Pin the archived form of a PROCESSED ledger.
    ///
    /// `directive_archived_form_is_pinned` covers what the parser produces,
    /// which is what `ParsedLedgerPayload` holds. `LedgerPayload` holds
    /// something else: the output of the shared `process()` pipeline, sorted
    /// by `canonical_sort_key` and booked. A change to `DirectivePriority`
    /// reorders that list without touching a single parsed directive, and a
    /// booking change rewrites the values in it -- both invalidate a cached
    /// blob, and neither moves the parse-side digest.
    ///
    /// The fixture puts a `pad` and a `balance` on the SAME DATE, because
    /// that pair is the one whose relative order the priorities decide. With
    /// them on different dates the date component of the sort key settles it
    /// and a priority swap changes nothing here. For the same reason it puts
    /// a `custom`, an `event` and a `note` on a transaction's date (#2576),
    /// and a `price` before it and a `commodity` after it (#2629).
    #[test]
    fn processed_ledger_archived_form_is_pinned() {
        // Moved once so far: swapping `Pad` and `Balance` in
        // `DirectivePriority` (#2179) reorders the same-date pair in the
        // fixture. That is the change this test was written to catch, and it
        // caught it on the rebase rather than in review.
        //
        // Moved again for #2576, which ranks `event` and `custom` with
        // transactions: the fixture gained a same-date `custom` written
        // before the transaction and an `event` and `note` after it, whose
        // order the ranks decide (custom, transaction, event, note now;
        // transaction, note, event, custom before).
        //
        // And for #2629, which ranks `commodity`, `note`, `query` and `price`
        // with transactions: the fixture gained a same-date `price` written
        // before the transaction and a `commodity` after it (price,
        // transaction, commodity now; commodity first and price last before).
        //
        // Moved once more for the `MetaMap`/`CommentList` boxing, which is a
        // layout change in the archived directives rather than a reordering
        // or a rebooking -- see `directive_archived_form_is_pinned`. And
        // once more for the variant `MetaMap`/`SortedSet` boxing (loader
        // v43), the same shape move on the remaining meta maps and the
        // tag/link sets. (Within v57 the hash had also moved when the load
        // pipeline stopped leaving an empty `Some(Box<Metadata>)` on every
        // posting and transaction it merely visited; v58 covers both.)
        const PROCESSED_LAYOUT_HASH: u64 = 0xf09b_417e_6cb6_e098;

        let src = "\
2024-01-01 open Assets:Bank USD\n\
2024-01-01 open Equity:Opening-Balances USD\n\
\n\
2024-01-04 pad Assets:Bank Equity:Opening-Balances\n\
2024-01-04 balance Assets:Bank  10.00 USD\n\
\n\
2024-01-05 custom \"fava-option\" \"locale\" \"en\"\n\
2024-01-05 price USD 0.90 EUR\n\
2024-01-05 * \"payee\" \"narration\"\n\
\x20\x20Assets:Bank  5.00 USD\n\
\x20\x20Equity:Opening-Balances\n\
2024-01-05 event \"location\" \"Paris\"\n\
2024-01-05 note Assets:Bank \"after the event\"\n\
2024-01-05 commodity USD\n\
\n\
2024-01-06 balance Assets:Bank  15.00 USD\n";

        let processed = crate::helpers::load_and_book(src);
        for d in &processed.directives {
            eprintln!("PROBE {} {:?}", d.type_name(), d.date());
        }
        assert!(
            processed.directives.len() >= 6,
            "fixture must survive the pipeline, else the digest pins an early \
             return: {} directives",
            processed.directives.len(),
        );

        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        let mut eat = |bytes: &[u8]| {
            for b in bytes {
                h ^= u64::from(*b);
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
        };
        // Hashed in pipeline order, so a reordering moves the digest even
        // when every directive is archived byte-identically.
        for d in &processed.directives {
            let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(d).unwrap();
            eat(&(bytes.len() as u64).to_le_bytes());
            eat(&bytes);
        }

        assert_eq!(
            h, PROCESSED_LAYOUT_HASH,
            "the processed ledger this cache archives changed -- directive \
             order (a `DirectivePriority` or sort-key change) or the booked \
             values themselves. A blob written by an older binary now \
             deserializes into a ledger this build would not produce: bump \
             CACHE_VERSION in this file and set PROCESSED_LAYOUT_HASH to {h:#x}",
        );
    }

    use super::*;

    #[test]
    fn test_roundtrip_ledger_payload() {
        let payload = LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions {
                operating_currencies: vec!["USD".to_string()],
                title: Some("Test".to_string()),
            },
            account_type_names: vec![
                "Assets".to_string(),
                "Liabilities".to_string(),
                "Equity".to_string(),
                "Revenue".to_string(),
                "Expenses".to_string(),
            ],
            booking_method: "NONE".to_string(),
            tolerance_multiplier: "0.25".to_string(),
            directive_lines: Vec::new(),
            directive_file_ranks: Vec::new(),
            summary_account_names: vec![
                "Eigenkapital:Anfang".to_string(),
                "Eigenkapital:Vorjahr".to_string(),
                "Eigenkapital:Umrechnung".to_string(),
                "Eigenkapital:Laufend".to_string(),
                "Eigenkapital:Umrechnung:Laufend".to_string(),
                "EUR".to_string(),
            ],
            errors: vec![Error::new("a warning")],
            query_errors: Vec::new(),
            query_refused: true,
        };
        let bytes = serialize_ledger(&payload).expect("serialize");
        assert!(bytes.starts_with(MAGIC_LEDGER));

        let restored = deserialize_ledger(&bytes).expect("deserialize");
        assert_eq!(restored.options.operating_currencies, ["USD"]);
        assert_eq!(restored.options.title.as_deref(), Some("Test"));
        assert_eq!(restored.booking_method, "NONE");
        assert_eq!(restored.tolerance_multiplier, "0.25");
        assert_eq!(
            restored.summary_account_names,
            [
                "Eigenkapital:Anfang",
                "Eigenkapital:Vorjahr",
                "Eigenkapital:Umrechnung",
                "Eigenkapital:Laufend",
                "Eigenkapital:Umrechnung:Laufend",
                "EUR"
            ]
        );
        assert_eq!(restored.errors.len(), 1);
        assert!(
            restored.query_refused,
            "the query gate survives the cache (#2861)"
        );
    }

    #[test]
    fn test_roundtrip_with_directives() {
        use crate::helpers::load_and_book;

        let source = r#"
option "title" "Test"
option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let processed = load_and_book(source);
        assert!(!processed.directives.is_empty());

        let payload = ParsedLedgerPayload {
            directives: processed.directives.clone(),
            directive_spans: processed.directive_spans.clone(),
            placeholders: Vec::new(),
            options: processed.options.clone(),
            parse_errors: Vec::new(),
            option_errors: Vec::new(),
            query_option_errors: Vec::new(),
            validation_errors: Vec::new(),
            query_refused: false,
        };

        let bytes = serialize_parsed(&payload).expect("serialize");
        let restored = deserialize_parsed(&bytes).expect("deserialize");
        assert_eq!(restored.directives.len(), processed.directives.len());
        assert_eq!(restored.options.title.as_deref(), Some("Test"));
    }

    /// A payload holding `MetaValue`s (8-byte aligned) decodes wherever the
    /// caller's bytes lie (#2934).
    ///
    /// The archive sits 12 bytes into the blob, and a `Uint8Array` reaches
    /// wasm memory with alignment 1, so the decoder may not assume either.
    /// Each shift below places the blob at a different offset from a 16-byte
    /// boundary; before the fix every one failed with `unaligned pointer`.
    #[cfg_attr(not(target_arch = "wasm32"), test)]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn test_deserialize_at_any_alignment() {
        use crate::helpers::load_and_book;

        let source = "2024-01-01 open Assets:Bank USD\n  note: \"meta\"\n\
2024-01-02 custom \"budget\" Assets:Bank \"monthly\" 2024-02-01 TRUE 42 2.5 1.00 USD\n";
        let processed = load_and_book(source);
        assert!(processed.errors.is_empty(), "{:?}", processed.errors);
        let parsed = serialize_parsed(&ParsedLedgerPayload {
            directives: processed.directives.clone(),
            directive_spans: processed.directive_spans.clone(),
            placeholders: Vec::new(),
            options: processed.options.clone(),
            parse_errors: Vec::new(),
            option_errors: Vec::new(),
            query_option_errors: Vec::new(),
            validation_errors: Vec::new(),
            query_refused: false,
        })
        .expect("serialize");
        let ledger = serialize_ledger(&LedgerPayload {
            directives: processed.directives.clone(),
            options: processed.options,
            account_type_names: Vec::new(),
            booking_method: "STRICT".to_string(),
            tolerance_multiplier: "0.5".to_string(),
            directive_lines: Vec::new(),
            directive_file_ranks: Vec::new(),
            summary_account_names: Vec::new(),
            errors: Vec::new(),
            query_errors: Vec::new(),
            query_refused: false,
        })
        .expect("serialize");

        for shift in 0..16 {
            let at = |blob: &[u8]| {
                let mut buf = rkyv::util::AlignedVec::<16>::with_capacity(shift + blob.len());
                buf.extend_from_slice(&vec![0; shift]);
                buf.extend_from_slice(blob);
                buf
            };
            let restored = deserialize_parsed(&at(&parsed)[shift..])
                .unwrap_or_else(|e| panic!("ParsedLedger at shift {shift}: {e}"));
            assert_eq!(restored.directives, processed.directives, "shift {shift}");
            let restored = deserialize_ledger(&at(&ledger)[shift..])
                .unwrap_or_else(|e| panic!("Ledger at shift {shift}: {e}"));
            assert_eq!(restored.directives, processed.directives, "shift {shift}");
        }
    }

    #[test]
    fn test_bad_magic_returns_error() {
        let mut bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            booking_method: "STRICT".to_string(),
            tolerance_multiplier: "0.5".to_string(),
            directive_lines: Vec::new(),
            directive_file_ranks: Vec::new(),
            summary_account_names: Vec::new(),
            errors: Vec::new(),
            query_errors: Vec::new(),
            query_refused: false,
        })
        .unwrap();
        bytes[0] = b'X';
        assert!(deserialize_ledger(&bytes).unwrap_err().contains("magic"));
    }

    #[test]
    fn test_too_short_returns_error() {
        assert!(
            deserialize_ledger(b"short")
                .unwrap_err()
                .contains("too short")
        );
    }

    #[test]
    fn test_version_mismatch_returns_error() {
        let mut bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            booking_method: "STRICT".to_string(),
            tolerance_multiplier: "0.5".to_string(),
            directive_lines: Vec::new(),
            directive_file_ranks: Vec::new(),
            summary_account_names: Vec::new(),
            errors: Vec::new(),
            query_errors: Vec::new(),
            query_refused: false,
        })
        .unwrap();
        bytes[8..12].copy_from_slice(&(CACHE_VERSION + 1).to_le_bytes());
        assert!(
            deserialize_ledger(&bytes)
                .unwrap_err()
                .contains("version mismatch")
        );
    }

    #[test]
    fn test_hash_sources_deterministic() {
        let h1 = hash_sources(&["hello", "world"]);
        let h2 = hash_sources(&["hello", "world"]);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }

    #[test]
    fn test_hash_sources_distinguishes_concat() {
        let h1 = hash_sources(&["ab", "c"]);
        let h2 = hash_sources(&["a", "bc"]);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_hash_sources_changes_with_content() {
        let h1 = hash_sources(&["source v1"]);
        let h2 = hash_sources(&["source v2"]);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_cross_type_rejection() {
        // Serialized Ledger bytes should not deserialize as ParsedLedger
        let bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            booking_method: "STRICT".to_string(),
            tolerance_multiplier: "0.5".to_string(),
            directive_lines: Vec::new(),
            directive_file_ranks: Vec::new(),
            summary_account_names: Vec::new(),
            errors: Vec::new(),
            query_errors: Vec::new(),
            query_refused: false,
        })
        .unwrap();
        assert!(
            deserialize_parsed(&bytes).is_err(),
            "Ledger bytes should not deserialize as ParsedLedger"
        );

        // Serialized ParsedLedger bytes should not deserialize as Ledger
        let bytes = serialize_parsed(&ParsedLedgerPayload {
            directives: Vec::new(),
            directive_spans: Vec::new(),
            placeholders: Vec::new(),
            options: LedgerOptions::default(),
            parse_errors: Vec::new(),
            option_errors: Vec::new(),
            query_option_errors: Vec::new(),
            validation_errors: Vec::new(),
            query_refused: false,
        })
        .unwrap();
        assert!(
            deserialize_ledger(&bytes).is_err(),
            "ParsedLedger bytes should not deserialize as Ledger"
        );
    }
}
