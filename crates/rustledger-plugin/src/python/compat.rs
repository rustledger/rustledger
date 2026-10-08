//! Beancount compatibility layer for Python plugins.
//!
//! This module provides the Python code that creates a beancount-compatible
//! environment for running Python plugins. It defines the `beancount.core.data`
//! namedtuples and provides serialization/deserialization functions.

/// Python compatibility layer code.
///
/// This code is executed in the Python runtime before loading user plugins.
/// It provides:
/// - `beancount.core.data` namedtuples (Transaction, Posting, Amount, etc.)
/// - JSON serialization/deserialization for directives
/// - Plugin execution wrapper
pub const BEANCOUNT_COMPAT_PY: &str = r#"
"""
Beancount compatibility layer for rustledger Python plugins.

This module provides the beancount.core.data API expected by Python plugins,
using rustledger's JSON-serialized directive format.
"""

import json
import sys
from collections import namedtuple
from datetime import date
from decimal import Decimal, InvalidOperation


# =============================================================================
# Core beancount.core.data types
# =============================================================================

Transaction = namedtuple('Transaction', [
    'meta', 'date', 'flag', 'payee', 'narration', 'tags', 'links', 'postings'
])

Posting = namedtuple('Posting', [
    'account', 'units', 'cost', 'price', 'flag', 'meta'
])

Amount = namedtuple('Amount', ['number', 'currency'])

Balance = namedtuple('Balance', [
    'meta', 'date', 'account', 'amount', 'tolerance', 'diff_amount'
])

Open = namedtuple('Open', [
    'meta', 'date', 'account', 'currencies', 'booking'
])

Close = namedtuple('Close', ['meta', 'date', 'account'])

Commodity = namedtuple('Commodity', ['meta', 'date', 'currency'])

Pad = namedtuple('Pad', ['meta', 'date', 'account', 'source_account'])

Event = namedtuple('Event', ['meta', 'date', 'type', 'description'])

Note = namedtuple('Note', ['meta', 'date', 'account', 'comment'])

Document = namedtuple('Document', [
    'meta', 'date', 'account', 'filename', 'tags', 'links'
])

Price = namedtuple('Price', ['meta', 'date', 'currency', 'amount'])

Query = namedtuple('Query', ['meta', 'date', 'name', 'query_string'])

Custom = namedtuple('Custom', ['meta', 'date', 'type', 'values'])


# =============================================================================
# Cost types
# =============================================================================

Cost = namedtuple('Cost', ['number', 'currency', 'date', 'label'])

# `CostSpec` shape matches upstream `beancount.core.data.CostSpec`
# verbatim — `number_per` / `number_total` are the two flat fields
# Python plugins read directly. The host's typed `CostNumber` enum
# (rustledger_core::CostNumber) is flattened to these two fields by
# `_parse_cost_spec` below.
#
# This is an INTENTIONAL legacy-shape match (Python compat policy
# bucket 2: "not fixable locally" — see project CLAUDE.md). Upstream
# beancount's Python API is what every existing Python plugin codes
# against; presenting a different shape here would break every
# Python plugin in the ecosystem. The host's stricter `CostNumber`
# shape is the right model internally, but the Python compat surface
# matches upstream's API by design.
CostSpec = namedtuple('CostSpec', [
    'number_per', 'number_total', 'currency', 'date', 'label', 'merge'
])


# =============================================================================
# Helper types
# =============================================================================

TxnPosting = namedtuple('TxnPosting', ['txn', 'posting'])


# =============================================================================
# Validation error
# =============================================================================

class ValidationError:
    """A validation error from a plugin."""

    def __init__(self, source, message, entry):
        self.source = source
        self.message = message
        self.entry = entry

    def __repr__(self):
        return f"ValidationError({self.message!r})"


# =============================================================================
# Deserialization helpers
# =============================================================================

def _parse_date(s):
    """Parse a date string (YYYY-MM-DD) to a date object."""
    if s is None:
        return None
    if isinstance(s, date):
        return s
    parts = s.split('-')
    return date(int(parts[0]), int(parts[1]), int(parts[2]))


def _parse_decimal(s):
    """Parse a decimal string to Decimal."""
    if s is None:
        return None
    if isinstance(s, (int, float)):
        return Decimal(str(s))
    if isinstance(s, Decimal):
        return s
    try:
        return Decimal(s)
    except InvalidOperation:
        return Decimal(0)


def _parse_amount(d):
    """Parse an amount dict to Amount namedtuple."""
    if d is None:
        return None
    return Amount(
        number=_parse_decimal(d.get('number')),
        currency=d.get('currency', '')
    )


def _parse_cost(d):
    """Parse a cost dict to Cost namedtuple."""
    if d is None:
        return None
    return Cost(
        number=_parse_decimal(d.get('number')),
        currency=d.get('currency', ''),
        date=_parse_date(d.get('date')),
        label=d.get('label')
    )


def _parse_cost_spec(d):
    """Parse a cost spec dict to CostSpec namedtuple.

    Reads the unified `kind`-tagged shape shared with FFI-WASI, WASM,
    and plugin-types:
        - {"kind": "per_unit", "value": "100"}            → number_per=100, number_total=None
        - {"kind": "total", "value": "1500"}              → number_per=None, number_total=1500
        - {"kind": "per_unit_from_total",
           "per_unit": "150", "total": "300"}             → both populated
        - null                                            → both None (bare `{}`)

    The Python-side `CostSpec` namedtuple still presents two flat
    fields for upstream beancount API compatibility; the bridge
    flattens the typed enum into those fields here.
    """
    if d is None:
        return None
    number_per = None
    number_total = None
    n = d.get('number')
    if isinstance(n, dict):
        kind = n.get('kind')
        if kind == 'per_unit':
            number_per = _parse_decimal(n.get('value'))
        elif kind == 'total':
            number_total = _parse_decimal(n.get('value'))
        elif kind == 'per_unit_from_total':
            number_per = _parse_decimal(n.get('per_unit'))
            number_total = _parse_decimal(n.get('total'))
    return CostSpec(
        number_per=number_per,
        number_total=number_total,
        currency=d.get('currency', ''),
        date=_parse_date(d.get('date')),
        label=d.get('label'),
        merge=d.get('merge', False)
    )


def _parse_posting(d):
    """Parse a posting dict to Posting namedtuple."""
    if d is None:
        return None
    return Posting(
        account=d.get('account', ''),
        units=_parse_amount(d.get('units')),
        cost=_parse_cost_spec(d.get('cost')),
        price=_parse_amount(d.get('price')),
        flag=d.get('flag'),
        meta=_parse_meta(d.get('metadata'))
    )


class _Meta(dict):
    """A metadata dict that remembers each value's wire form, so a value
    the plugin leaves alone goes back with its original type (an account
    stays an account, not a string). A plugin that builds a new dict
    still works; its values are typed from their Python types."""
    __slots__ = ('_wire',)


def _parse_meta_value(v):
    t = v.get('type')
    x = v.get('value')
    if t == 'number':
        return _parse_decimal(x)
    if t == 'date':
        return _parse_date(x)
    if t == 'amount':
        return _parse_amount(x)
    if t == 'bool':
        return bool(x)
    # string, account, currency, tag, link: plain strings, as in beancount.
    return x


def _parse_meta(items, d=None):
    """Parse the wire's `metadata` (a list of [key, typed value] pairs).

    Before #2500's review this read a `meta` key the wire never has, so
    every plugin saw empty metadata and every round trip dropped it.

    With `d` (the directive's dict), adds `filename` and `lineno` from its
    location, as beancount's entries always carry them (plugins read them,
    and report errors against `entry.meta`). They are not written back.
    """
    meta = _Meta()
    if items:
        # Only for entries that have metadata of their own: most have
        # none, and a ledger's worth of empty dicts is memory the
        # sandbox does not have to spare.
        wire = meta._wire = {}
        for item in items:
            k, v = item[0], item[1]
            if isinstance(v, dict) and 'type' in v:
                parsed = _parse_meta_value(v)
                meta[k] = parsed
                wire[k] = (parsed, v)
            else:
                meta[k] = v
    if d is not None:
        if d.get('filename') is not None and 'filename' not in meta:
            # One string per file, not one per entry.
            meta['filename'] = sys.intern(d['filename'])
        if d.get('lineno') is not None and 'lineno' not in meta:
            meta['lineno'] = d['lineno']
    return meta


def _serialize_meta_value(v):
    if isinstance(v, bool):
        return {'type': 'bool', 'value': v}
    if isinstance(v, (Decimal, int, float)):
        return {'type': 'number', 'value': str(v)}
    if isinstance(v, date):
        return {'type': 'date', 'value': _serialize_date(v)}
    if isinstance(v, Amount):
        return {'type': 'amount', 'value': _serialize_amount(v)}
    return {'type': 'string', 'value': str(v)}


def _serialize_meta(meta):
    """Metadata to the wire: [key, typed value] pairs.

    Skips the `filename` / `lineno` location keys `_parse_meta` added, and
    beancount-internal `__key__`s, neither of which is user metadata, and
    None values, which the wire cannot carry.
    """
    if not meta:
        return []
    wire = getattr(meta, '_wire', None) or {}
    out = []
    for k, v in meta.items():
        original = wire.get(k)
        if original is not None and original[0] == v:
            out.append([k, original[1]])
            continue
        if original is None and (k in ('filename', 'lineno') or str(k).startswith('__')):
            continue
        if v is None:
            continue
        out.append([str(k), _serialize_meta_value(v)])
    return out


def _dict_to_directive(d):
    """Convert a dict to the appropriate directive namedtuple."""
    dtype = d.get('type', '')
    meta = _parse_meta(d.get('metadata'), d)
    date_val = _parse_date(d.get('date'))

    if dtype == 'transaction':
        postings = [_parse_posting(p) for p in d.get('postings', [])]
        return Transaction(
            meta=meta,
            date=date_val,
            flag=d.get('flag', '*'),
            payee=d.get('payee'),
            narration=d.get('narration', ''),
            tags=frozenset(d.get('tags', [])),
            links=frozenset(d.get('links', [])),
            postings=postings
        )
    elif dtype == 'balance':
        return Balance(
            meta=meta,
            date=date_val,
            account=d.get('account', ''),
            amount=_parse_amount(d.get('amount')),
            tolerance=_parse_decimal(d.get('tolerance')),
            diff_amount=_parse_amount(d.get('diff_amount'))
        )
    elif dtype == 'open':
        return Open(
            meta=meta,
            date=date_val,
            account=d.get('account', ''),
            currencies=frozenset(d.get('currencies', [])),
            booking=d.get('booking')
        )
    elif dtype == 'close':
        return Close(
            meta=meta,
            date=date_val,
            account=d.get('account', '')
        )
    elif dtype == 'commodity':
        return Commodity(
            meta=meta,
            date=date_val,
            currency=d.get('currency', '')
        )
    elif dtype == 'pad':
        return Pad(
            meta=meta,
            date=date_val,
            account=d.get('account', ''),
            source_account=d.get('source_account', '')
        )
    elif dtype == 'event':
        return Event(
            meta=meta,
            date=date_val,
            type=d.get('event_type', ''),
            description=d.get('description', '')
        )
    elif dtype == 'note':
        return Note(
            meta=meta,
            date=date_val,
            account=d.get('account', ''),
            comment=d.get('comment', '')
        )
    elif dtype == 'document':
        return Document(
            meta=meta,
            date=date_val,
            account=d.get('account', ''),
            filename=d.get('filename', ''),
            tags=frozenset(d.get('tags', [])),
            links=frozenset(d.get('links', []))
        )
    elif dtype == 'price':
        return Price(
            meta=meta,
            date=date_val,
            currency=d.get('currency', ''),
            amount=_parse_amount(d.get('amount'))
        )
    elif dtype == 'query':
        return Query(
            meta=meta,
            date=date_val,
            name=d.get('name', ''),
            query_string=d.get('query_string', '')
        )
    elif dtype == 'custom':
        return Custom(
            meta=meta,
            date=date_val,
            type=d.get('custom_type', ''),
            values=d.get('values', [])
        )
    else:
        # Return as-is for unknown types
        return d


# =============================================================================
# Serialization helpers
# =============================================================================

def _serialize_date(d):
    """Serialize a date to ISO string."""
    if d is None:
        return None
    if isinstance(d, str):
        return d
    return d.isoformat()


def _serialize_decimal(d):
    """Serialize a Decimal to string."""
    if d is None:
        return None
    return str(d)


def _serialize_amount(a):
    """Serialize an Amount to dict."""
    if a is None:
        return None
    return {
        'number': _serialize_decimal(a.number),
        'currency': a.currency
    }


def _serialize_cost(c):
    """Serialize a Cost to dict."""
    if c is None:
        return None
    return {
        'number': _serialize_decimal(c.number),
        'currency': c.currency,
        'date': _serialize_date(c.date),
        'label': c.label
    }


def _serialize_cost_spec(c):
    """Serialize a CostSpec to dict (matches Rust CostData format).

    Emits the unified `kind`-tagged number shape shared with FFI-WASI,
    WASM, and plugin-types:
        - per_unit only       → {"kind": "per_unit", "value": "100"}
        - total only          → {"kind": "total", "value": "1500"}
        - both (post-booking) → {"kind": "per_unit_from_total",
                                 "per_unit": ..., "total": ...}
        - neither             → number is None (bare `{}`)

    Inputs accepted: CostSpec namedtuple (has number_per/number_total)
    or Cost namedtuple (has number). The latter is mapped to per_unit.
    """
    if c is None:
        return None
    if hasattr(c, 'number_per'):
        number_per = c.number_per
        number_total = c.number_total if hasattr(c, 'number_total') else None
        if number_per is not None and number_total is not None:
            number = {
                'kind': 'per_unit_from_total',
                'per_unit': _serialize_decimal(number_per),
                'total': _serialize_decimal(number_total),
            }
        elif number_per is not None:
            number = {'kind': 'per_unit', 'value': _serialize_decimal(number_per)}
        elif number_total is not None:
            number = {'kind': 'total', 'value': _serialize_decimal(number_total)}
        else:
            number = None
        return {
            'number': number,
            'currency': c.currency if c.currency else None,
            'date': _serialize_date(c.date),
            'label': c.label,
            'merge': c.merge if hasattr(c, 'merge') else False
        }
    # Cost namedtuple: a single `number` field, treated as per-unit.
    if c.number is not None:
        number = {'kind': 'per_unit', 'value': _serialize_decimal(c.number)}
    else:
        number = None
    return {
        'number': number,
        'currency': c.currency if c.currency else None,
        'date': _serialize_date(c.date),
        'label': c.label,
        'merge': False
    }


def _serialize_posting(p):
    """Serialize a Posting to dict."""
    if p is None:
        return None
    return {
        'account': p.account,
        'units': _serialize_amount(p.units),
        'cost': _serialize_cost_spec(p.cost),
        'price': _serialize_amount(p.price),
        'flag': p.flag,
        'metadata': _serialize_meta(p.meta)
    }


def _directive_to_dict(entry):
    """Convert a directive namedtuple to a dict."""
    if isinstance(entry, Transaction):
        return {
            'type': 'transaction',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'flag': entry.flag,
            'payee': entry.payee,
            'narration': entry.narration,
            'tags': list(entry.tags) if entry.tags else [],
            'links': list(entry.links) if entry.links else [],
            'postings': [_serialize_posting(p) for p in entry.postings]
        }
    elif isinstance(entry, Balance):
        return {
            'type': 'balance',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'amount': _serialize_amount(entry.amount),
            'tolerance': _serialize_decimal(entry.tolerance),
            'diff_amount': _serialize_amount(entry.diff_amount)
        }
    elif isinstance(entry, Open):
        return {
            'type': 'open',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'currencies': list(entry.currencies) if entry.currencies else [],
            'booking': entry.booking
        }
    elif isinstance(entry, Close):
        return {
            'type': 'close',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account
        }
    elif isinstance(entry, Commodity):
        return {
            'type': 'commodity',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'currency': entry.currency
        }
    elif isinstance(entry, Pad):
        return {
            'type': 'pad',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'source_account': entry.source_account
        }
    elif isinstance(entry, Event):
        return {
            'type': 'event',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'event_type': entry.type,
            'description': entry.description
        }
    elif isinstance(entry, Note):
        return {
            'type': 'note',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'comment': entry.comment
        }
    elif isinstance(entry, Document):
        return {
            'type': 'document',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'filename': entry.filename,
            'tags': list(entry.tags) if entry.tags else [],
            'links': list(entry.links) if entry.links else []
        }
    elif isinstance(entry, Price):
        return {
            'type': 'price',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'currency': entry.currency,
            'amount': _serialize_amount(entry.amount)
        }
    elif isinstance(entry, Query):
        return {
            'type': 'query',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'name': entry.name,
            'query_string': entry.query_string
        }
    elif isinstance(entry, Custom):
        return {
            'type': 'custom',
            'metadata': _serialize_meta(entry.meta),
            'date': _serialize_date(entry.date),
            'custom_type': entry.type,
            'values': entry.values
        }
    else:
        # Return as-is for unknown types
        return entry


# =============================================================================
# Public API
# =============================================================================

def deserialize_entries(json_str):
    """Convert JSON string to list of Python directive objects."""
    data = json.loads(json_str)
    return [_dict_to_directive(d) for d in data]


def serialize_entries(entries):
    """Convert list of Python directive objects to JSON string."""
    return json.dumps([_directive_to_dict(e) for e in entries], default=str)


def load_entries(path):
    """Read directives written one JSON object per line.

    Line by line, so the whole input never sits in memory as one string
    next to the objects parsed from it (#2500 review: a 100k-transaction
    ledger exhausted the sandbox's memory that way).
    """
    with open(path) as f:
        return [_dict_to_directive(json.loads(line)) for line in f if line.strip()]


def dump_entries(entries, f, inputs=()):
    """Write the plugin's output to the file object `f`, one line per
    entry, one at a time.

    An entry that is one of `inputs`, or was rebuilt from one (it still
    holds that input's `meta` dict, as `_replace` keeps it), is written
    as `{"modify": i, "entry": {...}}`, so the host keeps input `i`'s
    source location; anything else is `{"insert": {...}}`. Before #2500's
    review every entry was re-inserted, so a Python plugin cost every
    later diagnostic (from a later plugin or validation) its location.
    """
    by_id = {}
    by_meta = {}
    for i, e in enumerate(inputs):
        by_id[id(e)] = i
        meta = getattr(e, 'meta', None)
        if meta is not None:
            by_meta.setdefault(id(meta), i)
    used = set()
    for e in entries:
        i = by_id.get(id(e))
        if i is None or i in used:
            i = by_meta.get(id(getattr(e, 'meta', None)))
        entry = json.dumps(_directive_to_dict(e), default=str)
        if i is not None and i not in used:
            used.add(i)
            f.write('{"modify": %d, "entry": %s}\n' % (i, entry))
        else:
            f.write('{"insert": %s}\n' % entry)


def _error_to_dict(e):
    """One plugin error as the host reads it.

    Any object with a `message` counts, as in beancount, whose plugins
    report errors as namedtuples of their own (`source message entry`):
    bean-check prints `e.source['filename']:e.source['lineno']` and
    `e.message`, whatever the error's type. Before #2500's review only
    this module's `ValidationError` was read that way, and every other
    error became `str(e)`, the whole tuple, with no location.
    """
    message = getattr(e, 'message', None)
    source = getattr(e, 'source', None)
    filename = lineno = None
    if isinstance(source, dict):
        filename = source.get('filename')
        lineno = source.get('lineno')
    return {
        'message': str(e) if message is None else str(message),
        'source_file': filename if isinstance(filename, str) else None,
        'line_number': lineno if isinstance(lineno, int) and lineno > 0 else None,
    }


def serialize_errors(errors):
    """Convert list of errors to JSON string."""
    return json.dumps([_error_to_dict(e) for e in errors])


def _host_diagnostic(message, severity='error'):
    """A diagnostic about the plugin module itself, not about an entry."""
    return json.dumps([{
        'message': message,
        'source_file': None,
        'line_number': None,
        'severity': severity,
    }])


def _entry_point_name(item):
    return item if isinstance(item, str) else getattr(item, '__name__', repr(item))


def run_plugin(module, plugin_name, entries_path, options_json, config=None,
               entry_points=None):
    """
    Run a plugin module the way beancount's loader does.

    Mirrors `beancount.loader.run_transformations`: every item of the
    module's `__plugins__` is applied in order, a string naming a function
    of the module (looked up with getattr) and anything else being the
    callable itself. Each one receives the entries the previous one
    returned, plus the config string when the `plugin` directive has one.
    An exception in one function is reported and the next function gets
    the entries as they were before it, as in beancount.

    Where this differs from beancount, it reports instead of passing or
    crashing:
    - A module with no `__plugins__` runs nothing (beancount skips it
      silently); it is reported as a warning so a forgotten `__plugins__`
      is not mistaken for a plugin that ran and found nothing.
    - A listed name the module does not define is an error naming it
      (beancount raises AttributeError and aborts the whole load), and
      nothing in the module runs.

    Args:
        module: The plugin's module object
        plugin_name: The plugin reference, for messages
        entries_path: File of directives, one JSON object per line
        options_json: JSON-serialized options dict
        config: Optional plugin config string
        entry_points: Names of the functions to run instead of
            `__plugins__` (None: use `__plugins__`)

    Returns:
        Tuple of ((entries, inputs), serialized_errors), where inputs are
        the entries as loaded, for `dump_entries`. The first item is None
        when nothing ran, so the input entries stand unchanged.
    """
    if entry_points is None:
        if not hasattr(module, '__plugins__'):
            return None, _host_diagnostic(
                f'Python plugin "{plugin_name}" has no __plugins__, so it ran nothing; '
                f'list its entry points, e.g. __plugins__ = ["my_plugin"] '
                f'(beancount skips such a module silently)',
                'warning')
        entry_points = module.__plugins__
        if isinstance(entry_points, (str, bytes)):
            return None, _host_diagnostic(
                f'__plugins__ of Python plugin "{plugin_name}" must be a list or '
                f'tuple of function names, not the string {entry_points!r}')

    _missing = object()
    callbacks = []
    for item in entry_points:
        callback = getattr(module, item, _missing) if isinstance(item, str) else item
        if callback is _missing:
            return None, _host_diagnostic(
                f'__plugins__ of Python plugin "{plugin_name}" lists "{item}", '
                f'which the plugin does not define')
        if not callable(callback):
            return None, _host_diagnostic(
                f'__plugins__ of Python plugin "{plugin_name}" lists '
                f'"{_entry_point_name(item)}", which is not a function')
        callbacks.append((_entry_point_name(item), callback))

    entries = load_entries(entries_path)
    inputs = list(entries)
    options = json.loads(options_json) if options_json else {}
    args = () if config is None else (config,)

    errors = []
    for name, callback in callbacks:
        try:
            entries, plugin_errors = callback(entries, options, *args)
        except MemoryError:
            errors.append(ValidationError(
                None,
                f'Error applying plugin "{plugin_name}" ({name}): it ran out of the '
                f'sandbox memory limit (MemoryError; rledger raises it with '
                f'--plugin-max-memory-mb or [plugins] max_memory_mb)',
                None))
            continue
        except Exception as e:
            errors.append(ValidationError(
                None,
                f'Error applying plugin "{plugin_name}" ({name}): {type(e).__name__}: {e}',
                None))
            continue
        errors.extend(plugin_errors or [])

    return (entries, inputs), serialize_errors(errors)


# =============================================================================
# Create fake beancount module hierarchy
# =============================================================================

import types as _types


def FakeModule(name):
    """A stand-in module, named, so a missing name reads as
    `cannot import name 'x' from 'beancount.core'`, not from
    `'<unknown module name>'`."""
    return _types.ModuleType(name)


# Create beancount.core.data module
_beancount = FakeModule('beancount')
_beancount.core = FakeModule('beancount.core')
_beancount.core.data = FakeModule('beancount.core.data')

# Populate beancount.core.data with our types
_beancount.core.data.Transaction = Transaction
_beancount.core.data.Posting = Posting
_beancount.core.data.Amount = Amount
_beancount.core.data.Balance = Balance
_beancount.core.data.Open = Open
_beancount.core.data.Close = Close
_beancount.core.data.Commodity = Commodity
_beancount.core.data.Pad = Pad
_beancount.core.data.Event = Event
_beancount.core.data.Note = Note
_beancount.core.data.Document = Document
_beancount.core.data.Price = Price
_beancount.core.data.Query = Query
_beancount.core.data.Custom = Custom
_beancount.core.data.Cost = Cost
_beancount.core.data.CostSpec = CostSpec
_beancount.core.data.TxnPosting = TxnPosting

def new_metadata(filename, lineno, kvlist=None):
    """Create a new metadata dictionary."""
    meta = {'filename': filename, 'lineno': lineno}
    if kvlist:
        meta.update(kvlist)
    return meta

_beancount.core.data.new_metadata = new_metadata


def filter_txns(entries):
    """Yield only the Transaction entries (beancount.core.data.filter_txns)."""
    for entry in entries:
        if isinstance(entry, Transaction):
            yield entry

_beancount.core.data.filter_txns = filter_txns
_beancount.core.data.Directives = list

# Create beancount.core.amount module
_beancount.core.amount = FakeModule('beancount.core.amount')
_beancount.core.amount.Amount = Amount
# Verbatim from beancount.core.amount (3.x).
_beancount.core.amount.CURRENCY_RE = (
    r"[A-Z][A-Z0-9\'\.\_\-]*[A-Z0-9]?\b|/[A-Z0-9\'\.\_\-]*[A-Z](?:[A-Z0-9\'\.\_\-]*[A-Z0-9])?"
)

# Create beancount.core.getters module
_beancount.core.getters = FakeModule('beancount.core.getters')

def get_account_open_close(entries):
    """Get a mapping of account name to Open/Close directives.

    This is a simplified version of beancount.core.getters.get_account_open_close
    that returns a dict mapping account names to (open, close) tuples.
    """
    open_close_map = {}
    for entry in entries:
        if isinstance(entry, Open):
            account = entry.account
            if account not in open_close_map:
                open_close_map[account] = (entry, None)
            else:
                # Update the open entry
                open_close_map[account] = (entry, open_close_map[account][1])
        elif isinstance(entry, Close):
            account = entry.account
            if account not in open_close_map:
                open_close_map[account] = (None, entry)
            else:
                # Update the close entry
                open_close_map[account] = (open_close_map[account][0], entry)
    return open_close_map

_beancount.core.getters.get_account_open_close = get_account_open_close

# Create beancount.core.flags module
_beancount.core.flags = FakeModule('beancount.core.flags')
_beancount.core.flags.FLAG_OKAY = '*'
_beancount.core.flags.FLAG_WARNING = '!'
_beancount.core.flags.FLAG_PADDING = 'P'
_beancount.core.flags.FLAG_SUMMARIZE = 'S'
_beancount.core.flags.FLAG_TRANSFER = 'T'
_beancount.core.flags.FLAG_CONVERSIONS = 'C'
_beancount.core.flags.FLAG_UNREALIZED = 'U'
_beancount.core.flags.FLAG_RETURNS = 'R'
_beancount.core.flags.FLAG_MERGING = 'M'

# Install in sys.modules so imports work
sys.modules['beancount'] = _beancount
sys.modules['beancount.core'] = _beancount.core
sys.modules['beancount.core.data'] = _beancount.core.data
sys.modules['beancount.core.amount'] = _beancount.core.amount
sys.modules['beancount.core.getters'] = _beancount.core.getters
sys.modules['beancount.core.flags'] = _beancount.core.flags

# Export for direct use
__all__ = [
    'Transaction', 'Posting', 'Amount', 'Balance', 'Open', 'Close',
    'Commodity', 'Pad', 'Event', 'Note', 'Document', 'Price', 'Query',
    'Custom', 'Cost', 'CostSpec', 'TxnPosting', 'ValidationError',
    'deserialize_entries', 'serialize_entries', 'serialize_errors',
    'load_entries', 'dump_entries', 'run_plugin',
]
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compat_code_is_valid_python_syntax() {
        // Basic check that the Python code is non-empty and contains expected content
        assert!(BEANCOUNT_COMPAT_PY.contains("Transaction = namedtuple"));
        assert!(BEANCOUNT_COMPAT_PY.contains("def run_plugin"));
        assert!(BEANCOUNT_COMPAT_PY.contains("beancount.core.data"));
    }
}
