# Plugin that counts entries by type
def plugin(entries, options_map, config=None):
    """Count entries by type and print summary."""
    counts = {}
    for entry in entries:
        entry_type = type(entry).__name__
        counts[entry_type] = counts.get(entry_type, 0) + 1

    print(f"Entry counts: {counts}")
    return entries, []
