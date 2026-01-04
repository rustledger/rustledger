# Beancount Algorithms Specification

This document specifies the core algorithms for interpolation, balancing, and tolerance handling.

## 1. Transaction Balancing

### Weight Calculation

Each posting contributes a "weight" to the transaction balance. The weight is an Amount (number + currency).

```
weight(posting) =
    if posting.cost is Some:
        Amount(posting.units.number * posting.cost.number, posting.cost.currency)
    else if posting.price is Some:
        if posting.price.is_total:  // @@ syntax
            Amount(posting.price.number * sign(posting.units.number), posting.price.currency)
        else:  // @ syntax
            Amount(posting.units.number * posting.price.number, posting.price.currency)
    else:
        posting.units
```

### Balance Check

A transaction balances if, for each currency, the sum of weights equals zero within tolerance:

```
fn transaction_balances(txn: &Transaction, tolerances: &Tolerances) -> bool {
    let weights: HashMap<Currency, Decimal> = HashMap::new();

    for posting in &txn.postings {
        if let Some(units) = &posting.units {
            let w = weight(posting);
            *weights.entry(w.currency).or_default() += w.number;
        }
    }

    for (currency, total) in &weights {
        let tol = tolerances.get(currency);
        if total.abs() > tol {
            return false;
        }
    }
    true
}
```

## 2. Interpolation Algorithm

Interpolation fills in missing amounts so transactions balance.

### Rules

1. At most ONE posting per currency may have a missing amount
2. The missing amount is calculated from other postings
3. Cost and price affect the calculation

### Algorithm

```rust
fn interpolate(txn: &mut Transaction, tolerances: &Tolerances) -> Result<(), InterpolationError> {
    // Group postings by their weight currency
    let mut by_currency: HashMap<Currency, Vec<&mut Posting>> = HashMap::new();
    let mut missing: HashMap<Currency, Vec<&mut Posting>> = HashMap::new();

    for posting in &mut txn.postings {
        let currency = infer_weight_currency(posting);

        if posting.units.is_none() {
            missing.entry(currency).or_default().push(posting);
        } else {
            by_currency.entry(currency).or_default().push(posting);
        }
    }

    // Check: at most one missing per currency
    for (currency, postings) in &missing {
        if postings.len() > 1 {
            return Err(InterpolationError::MultipleMissing(currency.clone()));
        }
    }

    // Calculate missing amounts
    for (currency, mut missing_postings) in missing {
        let posting = &mut missing_postings[0];

        // Sum existing weights for this currency
        let total: Decimal = by_currency
            .get(&currency)
            .map(|ps| ps.iter().map(|p| weight(p).number).sum())
            .unwrap_or(Decimal::ZERO);

        // Missing amount is the negation
        let missing_number = -total;

        // Infer the units from weight
        posting.units = Some(infer_units_from_weight(
            posting,
            Amount { number: missing_number, currency: currency.clone() }
        ));
    }

    Ok(())
}

fn infer_weight_currency(posting: &Posting) -> Currency {
    if let Some(cost) = &posting.cost {
        cost.currency.clone()
    } else if let Some(price) = &posting.price {
        price.currency.clone()
    } else if let Some(units) = &posting.units {
        units.currency.clone()
    } else {
        // Must infer from account or context - error if ambiguous
        Currency::UNKNOWN
    }
}

fn infer_units_from_weight(posting: &Posting, weight: Amount) -> Amount {
    if let Some(cost) = &posting.cost {
        // units.number * cost.number = weight.number
        // units.number = weight.number / cost.number
        Amount {
            number: weight.number / cost.number,
            currency: infer_units_currency(posting),
        }
    } else if let Some(price) = &posting.price {
        if price.is_total {
            // Already the total, just need sign
            Amount {
                number: weight.number.signum() * /* need units from somewhere */,
                currency: infer_units_currency(posting),
            }
        } else {
            Amount {
                number: weight.number / price.number,
                currency: infer_units_currency(posting),
            }
        }
    } else {
        weight
    }
}
```

### Edge Cases

1. **Total price (@@ syntax)**: The price is the total, not per-unit
2. **Cost with missing units**: Must solve for units given cost
3. **Multiple currencies**: Each currency balances independently
4. **Tolerance**: Small residuals within tolerance are acceptable

## 3. Tolerance Calculation

### Inferred Tolerance

Tolerance is inferred from the precision of amounts in the transaction:

```rust
fn infer_tolerance(amounts: &[Amount], multiplier: Decimal) -> HashMap<Currency, Decimal> {
    let mut tolerances: HashMap<Currency, Decimal> = HashMap::new();

    for amount in amounts {
        let precision = decimal_places(amount.number);
        let tolerance = Decimal::new(5, precision + 1) * multiplier;
        // e.g., 2 decimal places -> 0.005 * multiplier

        tolerances
            .entry(amount.currency.clone())
            .and_modify(|t| *t = (*t).max(tolerance))
            .or_insert(tolerance);
    }

    tolerances
}

fn decimal_places(n: Decimal) -> u32 {
    // Count digits after decimal point
    n.scale()
}
```

### Default Tolerances

From options:
```rust
fn get_tolerance(currency: &str, options: &Options, inferred: &HashMap<Currency, Decimal>) -> Decimal {
    inferred.get(currency).copied()
        .or_else(|| options.inferred_tolerance_default.get(currency).copied())
        .unwrap_or(Decimal::new(5, 3))  // 0.005 default
}
```

### Tolerance from Cost

When `infer_tolerance_from_cost` is true, expand tolerance to include cost currency precision:

```rust
fn expand_tolerance_from_cost(
    tolerances: &mut HashMap<Currency, Decimal>,
    postings: &[Posting],
    multiplier: Decimal,
) {
    for posting in postings {
        if let Some(cost) = &posting.cost {
            let cost_precision = decimal_places(cost.number);
            let cost_tolerance = Decimal::new(5, cost_precision + 1) * multiplier;

            // The cost currency gets expanded tolerance
            tolerances
                .entry(cost.currency.clone())
                .and_modify(|t| *t = (*t).max(cost_tolerance))
                .or_insert(cost_tolerance);
        }
    }
}
```

## 4. Booking Algorithm

### Position Matching

```rust
fn match_positions<'a>(
    inventory: &'a [Position],
    units_currency: &Currency,
    cost_spec: &Option<CostSpec>,
) -> Vec<&'a Position> {
    inventory.iter()
        .filter(|pos| {
            // Must match units currency
            if &pos.units.currency != units_currency {
                return false;
            }

            // If no cost spec, match positions without cost
            let Some(spec) = cost_spec else {
                return pos.cost.is_none();
            };

            // If cost spec is empty {}, match any position with cost
            let Some(cost) = &pos.cost else {
                return false;
            };

            // Match each specified component
            if let Some(spec_number) = &spec.number {
                if &cost.number != spec_number {
                    return false;
                }
            }
            if let Some(spec_currency) = &spec.currency {
                if &cost.currency != spec_currency {
                    return false;
                }
            }
            if let Some(spec_date) = &spec.date {
                if cost.date.as_ref() != Some(spec_date) {
                    return false;
                }
            }
            if let Some(spec_label) = &spec.label {
                if cost.label.as_ref() != Some(spec_label) {
                    return false;
                }
            }

            true
        })
        .collect()
}
```

### Reduction Algorithm

```rust
fn reduce_inventory(
    inventory: &mut Vec<Position>,
    units: Amount,  // negative for reduction
    cost_spec: Option<CostSpec>,
    booking: BookingMethod,
) -> Result<Vec<MatchedLot>, BookingError> {
    let candidates = match_positions(inventory, &units.currency, &cost_spec);

    if candidates.is_empty() {
        return Err(BookingError::NoMatchingLots);
    }

    let total_available: Decimal = candidates.iter().map(|p| p.units.number).sum();
    let reduction = units.number.abs();

    if total_available < reduction {
        return Err(BookingError::InsufficientUnits {
            requested: reduction,
            available: total_available,
        });
    }

    // Total match: all candidates consumed exactly
    if total_available == reduction {
        return reduce_all(inventory, &candidates);
    }

    // Ambiguous match: need booking method
    match booking {
        BookingMethod::STRICT => {
            if candidates.len() > 1 {
                Err(BookingError::AmbiguousMatch)
            } else {
                reduce_single(inventory, candidates[0], reduction)
            }
        }
        BookingMethod::FIFO => {
            reduce_ordered(inventory, candidates, reduction, |a, b| a.date.cmp(&b.date))
        }
        BookingMethod::LIFO => {
            reduce_ordered(inventory, candidates, reduction, |a, b| b.date.cmp(&a.date))
        }
        BookingMethod::AVERAGE => {
            reduce_average(inventory, candidates, reduction)
        }
        BookingMethod::NONE => {
            // Just append negative position
            inventory.push(Position { units, cost: cost_spec.map(|s| s.into()) });
            Ok(vec![])
        }
    }
}

fn reduce_ordered<F>(
    inventory: &mut Vec<Position>,
    mut candidates: Vec<&Position>,
    mut remaining: Decimal,
    compare: F,
) -> Result<Vec<MatchedLot>, BookingError>
where
    F: Fn(&Cost, &Cost) -> Ordering,
{
    // Sort by date according to compare function
    candidates.sort_by(|a, b| {
        match (&a.cost, &b.cost) {
            (Some(ca), Some(cb)) => compare(ca, cb),
            _ => Ordering::Equal,
        }
    });

    let mut matched = vec![];

    for candidate in candidates {
        if remaining <= Decimal::ZERO {
            break;
        }

        let take = remaining.min(candidate.units.number);
        remaining -= take;

        matched.push(MatchedLot {
            units: take,
            cost: candidate.cost.clone(),
        });

        // Update inventory
        reduce_position_by(inventory, candidate, take);
    }

    Ok(matched)
}

fn reduce_average(
    inventory: &mut Vec<Position>,
    candidates: Vec<&Position>,
    reduction: Decimal,
) -> Result<Vec<MatchedLot>, BookingError> {
    // Calculate weighted average cost
    let total_units: Decimal = candidates.iter().map(|p| p.units.number).sum();
    let total_cost: Decimal = candidates.iter()
        .filter_map(|p| p.cost.as_ref().map(|c| p.units.number * c.number))
        .sum();

    let avg_cost = total_cost / total_units;

    // Remove all candidate positions
    for candidate in &candidates {
        remove_position(inventory, candidate);
    }

    // Add back consolidated position minus reduction
    let remaining_units = total_units - reduction;
    if remaining_units > Decimal::ZERO {
        inventory.push(Position {
            units: Amount {
                number: remaining_units,
                currency: candidates[0].units.currency.clone(),
            },
            cost: Some(Cost {
                number: avg_cost,
                currency: candidates[0].cost.as_ref().unwrap().currency.clone(),
                date: None,  // Average loses date specificity
                label: None,
            }),
        });
    }

    Ok(vec![MatchedLot {
        units: reduction,
        cost: Some(Cost {
            number: avg_cost,
            currency: candidates[0].cost.as_ref().unwrap().currency.clone(),
            date: None,
            label: None,
        }),
    }])
}
```

## 5. Pad Algorithm

Pad directives auto-generate balancing transactions:

```rust
fn process_pad(
    pad: &PadDirective,
    balance_assertion: &BalanceAssertion,
    inventory: &Inventory,
) -> Option<Transaction> {
    let current_balance = inventory
        .get_units(&pad.account, &balance_assertion.amount.currency);

    let difference = balance_assertion.amount.number - current_balance;

    if difference.abs() <= tolerance {
        return None;  // Already balanced
    }

    Some(Transaction {
        date: pad.date,
        flag: 'P',
        payee: None,
        narration: "(Padding inserted for balance assertion)".to_string(),
        postings: vec![
            Posting {
                account: pad.account.clone(),
                units: Some(Amount {
                    number: difference,
                    currency: balance_assertion.amount.currency.clone(),
                }),
                cost: None,
                price: None,
            },
            Posting {
                account: pad.source_account.clone(),
                units: Some(Amount {
                    number: -difference,
                    currency: balance_assertion.amount.currency.clone(),
                }),
                cost: None,
                price: None,
            },
        ],
        ..Default::default()
    })
}
```

## 6. Balance Assertion Algorithm

```rust
fn check_balance_assertion(
    assertion: &BalanceAssertion,
    inventories: &HashMap<Account, Inventory>,
    tolerances: &Tolerances,
) -> Result<(), BalanceError> {
    // Get inventory for account (or empty if not exists)
    let inventory = inventories
        .get(&assertion.account)
        .cloned()
        .unwrap_or_default();

    // Sum units of the asserted currency (ignoring cost lots)
    let actual: Decimal = inventory
        .positions
        .iter()
        .filter(|p| p.units.currency == assertion.amount.currency)
        .map(|p| p.units.number)
        .sum();

    let expected = assertion.amount.number;
    let tolerance = assertion.tolerance
        .unwrap_or_else(|| tolerances.get(&assertion.amount.currency));

    if (actual - expected).abs() > tolerance {
        Err(BalanceError {
            account: assertion.account.clone(),
            expected,
            actual,
            difference: actual - expected,
            currency: assertion.amount.currency.clone(),
        })
    } else {
        Ok(())
    }
}

// For parent account assertions, sum all children
fn check_balance_assertion_with_children(
    assertion: &BalanceAssertion,
    inventories: &HashMap<Account, Inventory>,
    tolerances: &Tolerances,
) -> Result<(), BalanceError> {
    let actual: Decimal = inventories
        .iter()
        .filter(|(account, _)| account.starts_with(&assertion.account))
        .flat_map(|(_, inv)| &inv.positions)
        .filter(|p| p.units.currency == assertion.amount.currency)
        .map(|p| p.units.number)
        .sum();

    // ... same comparison logic
}
```
