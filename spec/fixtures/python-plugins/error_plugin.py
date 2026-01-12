# Plugin that generates validation errors for testing
def plugin(entries, options_map, config=None):
    """Generate errors for transactions without payees."""
    errors = []
    for entry in entries:
        if type(entry).__name__ == 'Transaction':
            if not entry.payee:
                errors.append(ValidationError(
                    entry.meta,
                    f"Transaction on {entry.date} has no payee",
                    entry
                ))
    return entries, errors
