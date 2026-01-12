# Plugin that adds tags to transactions based on account patterns
def plugin(entries, options_map, config=None):
    """Add #food tag to transactions with Expenses:Food postings."""
    new_entries = []
    for entry in entries:
        if type(entry).__name__ == 'Transaction':
            has_food = any(
                p.account.startswith('Expenses:Food')
                for p in entry.postings
            )
            if has_food and 'food' not in entry.tags:
                # Create new transaction with added tag
                new_tags = frozenset(entry.tags | {'food'})
                entry = Transaction(
                    meta=entry.meta,
                    date=entry.date,
                    flag=entry.flag,
                    payee=entry.payee,
                    narration=entry.narration,
                    tags=new_tags,
                    links=entry.links,
                    postings=entry.postings
                )
        new_entries.append(entry)
    return new_entries, []
