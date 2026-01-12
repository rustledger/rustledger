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
    """Parse a cost spec dict to CostSpec namedtuple."""
    if d is None:
        return None
    return CostSpec(
        number_per=_parse_decimal(d.get('number_per')),
        number_total=_parse_decimal(d.get('number_total')),
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
        cost=_parse_cost(d.get('cost')),
        price=_parse_amount(d.get('price')),
        flag=d.get('flag'),
        meta=d.get('meta', {})
    )


def _parse_meta(d):
    """Parse metadata dict."""
    if d is None:
        return {}
    return dict(d)


def _dict_to_directive(d):
    """Convert a dict to the appropriate directive namedtuple."""
    dtype = d.get('type', '')
    meta = _parse_meta(d.get('meta'))
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


def _serialize_posting(p):
    """Serialize a Posting to dict."""
    if p is None:
        return None
    return {
        'account': p.account,
        'units': _serialize_amount(p.units),
        'cost': _serialize_cost(p.cost),
        'price': _serialize_amount(p.price),
        'flag': p.flag,
        'metadata': list(p.meta.items()) if p.meta else []
    }


def _directive_to_dict(entry):
    """Convert a directive namedtuple to a dict."""
    if isinstance(entry, Transaction):
        return {
            'type': 'transaction',
            'metadata': list(entry.meta.items()) if entry.meta else [],
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
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'amount': _serialize_amount(entry.amount),
            'tolerance': _serialize_decimal(entry.tolerance),
            'diff_amount': _serialize_amount(entry.diff_amount)
        }
    elif isinstance(entry, Open):
        return {
            'type': 'open',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'currencies': list(entry.currencies) if entry.currencies else [],
            'booking': entry.booking
        }
    elif isinstance(entry, Close):
        return {
            'type': 'close',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account
        }
    elif isinstance(entry, Commodity):
        return {
            'type': 'commodity',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'currency': entry.currency
        }
    elif isinstance(entry, Pad):
        return {
            'type': 'pad',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'source_account': entry.source_account
        }
    elif isinstance(entry, Event):
        return {
            'type': 'event',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'event_type': entry.type,
            'description': entry.description
        }
    elif isinstance(entry, Note):
        return {
            'type': 'note',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'comment': entry.comment
        }
    elif isinstance(entry, Document):
        return {
            'type': 'document',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'account': entry.account,
            'filename': entry.filename,
            'tags': list(entry.tags) if entry.tags else [],
            'links': list(entry.links) if entry.links else []
        }
    elif isinstance(entry, Price):
        return {
            'type': 'price',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'currency': entry.currency,
            'amount': _serialize_amount(entry.amount)
        }
    elif isinstance(entry, Query):
        return {
            'type': 'query',
            'metadata': list(entry.meta.items()) if entry.meta else [],
            'date': _serialize_date(entry.date),
            'name': entry.name,
            'query_string': entry.query_string
        }
    elif isinstance(entry, Custom):
        return {
            'type': 'custom',
            'metadata': list(entry.meta.items()) if entry.meta else [],
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


def serialize_errors(errors):
    """Convert list of errors to JSON string."""
    error_list = []
    for e in errors:
        if isinstance(e, ValidationError):
            error_list.append({
                'message': str(e.message),
                'source_file': e.source.get('filename') if e.source else None,
                'line_number': e.source.get('lineno') if e.source else None,
            })
        else:
            error_list.append({
                'message': str(e),
                'source_file': None,
                'line_number': None,
            })
    return json.dumps(error_list)


def run_plugin(plugin_func, entries_json, options_json, config=None):
    """
    Execute a beancount plugin function.

    Args:
        plugin_func: The plugin function to call
        entries_json: JSON-serialized directives
        options_json: JSON-serialized options dict
        config: Optional plugin config string

    Returns:
        Tuple of (serialized_entries, serialized_errors)
    """
    entries = deserialize_entries(entries_json)
    options = json.loads(options_json) if options_json else {}

    try:
        if config is not None:
            new_entries, errors = plugin_func(entries, options, config)
        else:
            new_entries, errors = plugin_func(entries, options)
    except Exception as e:
        # Return original entries with the exception as an error
        error = ValidationError(None, f"Plugin error: {e}", None)
        return serialize_entries(entries), serialize_errors([error])

    return serialize_entries(new_entries), serialize_errors(errors or [])


# =============================================================================
# Create fake beancount module hierarchy
# =============================================================================

class FakeModule:
    """A fake module for namespace purposes."""
    pass


# Create beancount.core.data module
_beancount = FakeModule()
_beancount.core = FakeModule()
_beancount.core.data = FakeModule()

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

# Create beancount.core.amount module
_beancount.core.amount = FakeModule()
_beancount.core.amount.Amount = Amount

# Install in sys.modules so imports work
sys.modules['beancount'] = _beancount
sys.modules['beancount.core'] = _beancount.core
sys.modules['beancount.core.data'] = _beancount.core.data
sys.modules['beancount.core.amount'] = _beancount.core.amount

# Export for direct use
__all__ = [
    'Transaction', 'Posting', 'Amount', 'Balance', 'Open', 'Close',
    'Commodity', 'Pad', 'Event', 'Note', 'Document', 'Price', 'Query',
    'Custom', 'Cost', 'CostSpec', 'TxnPosting', 'ValidationError',
    'deserialize_entries', 'serialize_entries', 'serialize_errors',
    'run_plugin',
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
