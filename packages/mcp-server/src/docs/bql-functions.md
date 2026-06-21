# BQL Functions Reference

## Aggregate Functions

| Function | Description |
|----------|-------------|
| `sum(x)` | Sum of values |
| `count()` | Count of rows |
| `first(x)` | First value |
| `last(x)` | Last value |
| `min(x)` | Minimum value |
| `max(x)` | Maximum value |

## Date Functions

| Function | Description |
|----------|-------------|
| `year(date)` | Extract year (integer) |
| `month(date)` | Extract month (1-12) |
| `day(date)` | Extract day of month |
| `quarter(date)` | Extract quarter (1-4) |
| `weekday(date)` | Day-of-week name (`Mon`..`Sun`) |

## String Functions

| Function | Description |
|----------|-------------|
| `length(s)` | String length |
| `upper(s)` | Uppercase string |
| `lower(s)` | Lowercase string |

## Account Functions

| Function | Description |
|----------|-------------|
| `root(account, n)` | First n components |
| `leaf(account)` | Last component |
| `parent(account)` | Parent account |

## Conversion Functions

| Function | Description |
|----------|-------------|
| `cost(position)` | Convert to cost basis |
| `value(position)` | Market value (needs prices) |
| `units(position)` | Just the units |
