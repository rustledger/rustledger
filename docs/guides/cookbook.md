______________________________________________________________________

## title: Cookbook description: Practical examples for common financial scenarios

# Cookbook

Practical examples for recording common financial scenarios in beancount.

## Salary and Employment

### Recording a Paycheck

A typical paycheck with taxes and deductions:

```beancount
2024-01-15 * "Employer Inc" "January paycheck"
  Income:Salary:Gross        -5000.00 USD
  Expenses:Taxes:Federal       750.00 USD
  Expenses:Taxes:State         200.00 USD
  Expenses:Taxes:SocialSec     310.00 USD
  Expenses:Taxes:Medicare       72.50 USD
  Expenses:Health:Insurance    150.00 USD
  Assets:Retirement:401k       250.00 USD  ; Pre-tax contribution
  Assets:Bank:Checking        3267.50 USD  ; Net pay
```

### 401(k) with Employer Match

```beancount
2024-01-15 * "Employer Inc" "401k contribution + match"
  ; Your pre-tax contribution (from paycheck above)
  Assets:Retirement:401k:PreTax    250.00 USD
  ; Employer match (50% up to 6%)
  Assets:Retirement:401k:Match     125.00 USD
  Income:Salary:401kMatch         -125.00 USD
```

### Stock Vesting (RSUs)

When restricted stock units vest:

```beancount
2024-01-15 * "Employer Inc" "RSU vesting - 100 shares"
  ; Shares vest at current market price
  Assets:Brokerage:ACME    100 ACME {150.00 USD}
  Income:Salary:RSU     -15000.00 USD

  ; Taxes withheld (shares sold to cover)
  Expenses:Taxes:Federal   3000.00 USD
  Expenses:Taxes:State      750.00 USD
  Assets:Brokerage:ACME    -25 ACME {150.00 USD} @ 150.00 USD
```

### Vacation/PTO Tracking

Track accrued time off using a custom currency:

```beancount
2020-01-01 commodity PTOHR
  name: "PTO Hours"

2020-01-01 open Assets:PTO          PTOHR
2020-01-01 open Income:PTO:Accrued  PTOHR
2020-01-01 open Expenses:PTO:Used   PTOHR

; Accrue PTO each pay period
2024-01-15 * "PTO accrual"
  Assets:PTO           6.67 PTOHR
  Income:PTO:Accrued  -6.67 PTOHR

; Use PTO
2024-02-20 * "Vacation day"
  Expenses:PTO:Used    8 PTOHR
  Assets:PTO          -8 PTOHR
```

## Investments

### Buying Stock

```beancount
2024-01-15 * "Buy AAPL shares"
  Assets:Brokerage:AAPL    10 AAPL {185.00 USD}
  Expenses:Fees:Trading     4.95 USD
  Assets:Bank:Checking  -1854.95 USD
```

### Selling Stock (with Capital Gains)

```beancount
2024-06-15 * "Sell AAPL shares"
  ; Sell 10 shares bought at $185, now at $195
  Assets:Brokerage:AAPL   -10 AAPL {185.00 USD} @ 195.00 USD
  Assets:Bank:Checking   1945.05 USD
  Expenses:Fees:Trading     4.95 USD
  Income:CapitalGains:Short  ; Auto-calculated: -100.00 USD
```

### Dividends

Cash dividend:

```beancount
2024-03-15 * "AAPL dividend"
  Assets:Brokerage:Cash     24.00 USD
  Income:Dividends:AAPL    -24.00 USD
```

Reinvested dividend (DRIP):

```beancount
2024-03-15 * "VTI dividend reinvested"
  Assets:Brokerage:VTI    0.15 VTI {245.00 USD}
  Income:Dividends:VTI   -36.75 USD
```

### Stock Split

```beancount
2024-08-01 * "AAPL 4:1 stock split"
  ; Remove old shares
  Assets:Brokerage:AAPL   -10 AAPL {185.00 USD}
  ; Add new shares at adjusted cost basis
  Assets:Brokerage:AAPL    40 AAPL {46.25 USD}
```

### Index Fund Rebalancing

```beancount
2024-01-02 * "Annual rebalancing"
  ; Sell overweight position
  Assets:Brokerage:VTI   -5 VTI {240.00 USD} @ 255.00 USD
  ; Buy underweight position
  Assets:Brokerage:VXUS   8 VXUS {58.00 USD}
  ; Net cash movement
  Assets:Brokerage:Cash  811.00 USD
  Income:CapitalGains:Long  ; gain on VTI sale
```

## Banking

### Opening Balance

When starting to track an existing account:

```beancount
2024-01-01 pad Assets:Bank:Checking Equity:Opening-Balances
2024-01-01 balance Assets:Bank:Checking  5432.10 USD
```

### Bank Transfer

```beancount
2024-01-15 * "Transfer to savings"
  Assets:Bank:Checking  -1000.00 USD
  Assets:Bank:Savings    1000.00 USD
```

### ATM Withdrawal

```beancount
2024-01-15 * "ATM" "Cash withdrawal"
  Assets:Cash            200.00 USD
  Assets:Bank:Checking  -200.00 USD
```

### Bank Fees

```beancount
2024-01-31 * "Monthly account fee"
  Expenses:Fees:Bank    12.00 USD
  Assets:Bank:Checking
```

### Interest Earned

```beancount
2024-01-31 * "Savings interest"
  Assets:Bank:Savings     15.23 USD
  Income:Interest:Bank   -15.23 USD
```

## Credit Cards

### Credit Card Purchase

```beancount
2024-01-15 * "Amazon" "Office supplies"
  Expenses:Office        45.99 USD
  Liabilities:CreditCard:Chase
```

### Paying Credit Card Bill

```beancount
2024-02-01 * "Credit card payment"
  Liabilities:CreditCard:Chase  500.00 USD
  Assets:Bank:Checking         -500.00 USD

2024-02-01 balance Liabilities:CreditCard:Chase  -234.56 USD
```

### Credit Card Rewards

```beancount
2024-03-15 * "Cash back redemption"
  Assets:Bank:Checking      50.00 USD
  Income:Rewards:CashBack  -50.00 USD
```

## Loans and Mortgages

### Mortgage Payment

```beancount
2024-01-01 * "Mortgage payment"
  Expenses:Interest:Mortgage    850.00 USD  ; Interest portion
  Liabilities:Mortgage          650.00 USD  ; Principal paydown
  Expenses:Escrow:Taxes         200.00 USD
  Expenses:Escrow:Insurance     100.00 USD
  Assets:Bank:Checking        -1800.00 USD
```

### Car Loan Payment

```beancount
2024-01-15 * "Auto loan payment"
  Expenses:Interest:Auto     45.00 USD
  Liabilities:Loans:Auto    355.00 USD
  Assets:Bank:Checking     -400.00 USD
```

### Student Loan Payment

```beancount
2024-01-15 * "Student loan payment"
  Expenses:Interest:StudentLoan   125.00 USD
  Liabilities:Loans:Student       275.00 USD
  Assets:Bank:Checking           -400.00 USD
```

## Currency and International

### Currency Accounts

If you are starting a new ledger that will hold more than one currency, book conversions
through a trading account: each account then holds one currency, and every conversion is on
the books in both currencies. It is where Vnext is pointed (Martin Blais, "Currency Accounts
instead of a Single Conversion"), and rustledger has the semantics as the `currency_accounts`
plugin.

The source is the same either way. A conversion is written with a price:

```beancount
2024-01-15 * "Buy EUR"
  Assets:Bank:EUR    100 EUR @ 1.10 USD
  Assets:Bank:USD   -110 USD
```

Without the plugin that is the whole record: the price is the conversion. Enable it and the
same transaction is booked through the trading account on load. This is what
`rledger report journal` prints, with the price stripped, because a price beside an explicit
conversion leg would count the exchange twice:

```beancount
plugin "beancount.plugins.currency_accounts"

2024-01-15 * "Buy EUR"
  Assets:Bank:EUR              100 EUR
  Assets:Bank:USD             -110 USD
  Equity:CurrencyAccounts:EUR -100 EUR
  Equity:CurrencyAccounts:USD  110 USD
```

The transaction is marked `currency_accounts_processed: TRUE`, and the conversion shows up in
the balances instead of being left implied:

| Account | With the plugin | Without |
|---|---|---|
| `Assets:Bank:EUR` | 100 EUR | 100 EUR |
| `Assets:Bank:USD` | -110.00 USD | -110.00 USD |
| `Equity:CurrencyAccounts:EUR` | -100 EUR | — |
| `Equity:CurrencyAccounts:USD` | 110.00 USD | — |

The base account is `Equity:CurrencyAccounts`. Give the plugin a name to use your own:

```beancount
plugin "beancount.plugins.currency_accounts" "Equity:Trading"
```

Two divergences from beancount 3's plugin, both deliberate: a base account that is not a
valid account name falls back to `Equity:CurrencyAccounts` where beancount's plugin fails, and
the written posting order is kept. Full behavior in
[`currency_accounts`](../reference/plugins.md#currency_accounts).

The recipes below write conversions the common way, with the price doing the work. With
currency accounts enabled they book through the trading account instead.

### Currency Exchange

```beancount
2024-01-15 * "Currency exchange"
  Assets:Bank:EUR     500 EUR @@ 545 USD
  Assets:Bank:USD    -545 USD
```

### International Wire Transfer

```beancount
2024-01-15 * "Wire to Europe"
  Assets:Bank:EUR        1000 EUR @ 1.09 USD
  Expenses:Fees:Wire       35.00 USD
  Assets:Bank:USD       -1125.00 USD
```

### Foreign Expense

```beancount
2024-07-15 * "Hotel in Paris" #vacation
  Expenses:Travel:Lodging  150 EUR @ 1.10 USD
  Liabilities:CreditCard
```

## Shared Expenses

### Splitting a Bill

When you pay and someone owes you:

```beancount
2024-01-15 * "Dinner with friend"
  Expenses:Food:Restaurants   40.00 USD  ; Your half
  Assets:Receivables:John     40.00 USD  ; Friend owes you
  Assets:Bank:Checking       -80.00 USD  ; You paid total
```

When they pay you back:

```beancount
2024-01-20 * "John paid back"
  Assets:Bank:Checking       40.00 USD
  Assets:Receivables:John   -40.00 USD
```

### Roommate Expenses

```beancount
2024-01-01 * "January rent"
  Expenses:Housing:Rent      1000.00 USD  ; Your share
  Assets:Receivables:Roommate  1000.00 USD  ; Roommate's share
  Assets:Bank:Checking       -2000.00 USD  ; Total rent paid
```

### Expense Reimbursement

Work expense you'll be reimbursed for:

```beancount
2024-01-15 * "Business lunch with client"
  Assets:Receivables:Employer   85.00 USD
  Assets:Bank:Checking         -85.00 USD

2024-01-31 * "Expense reimbursement"
  Assets:Bank:Checking          85.00 USD
  Assets:Receivables:Employer  -85.00 USD
```

## Taxes

### Quarterly Estimated Tax Payment

```beancount
2024-04-15 * "Q1 estimated tax payment"
  Expenses:Taxes:Federal:Estimated  2500.00 USD
  Assets:Bank:Checking             -2500.00 USD
```

### Property Tax

```beancount
2024-03-01 * "Property tax payment"
  Expenses:Taxes:Property  3200.00 USD
  Assets:Bank:Checking    -3200.00 USD
```

### Tax Refund

```beancount
2024-04-20 * "Federal tax refund"
  Assets:Bank:Checking          1250.00 USD
  Expenses:Taxes:Federal:Refund -1250.00 USD
```

## Healthcare

### HSA Contribution

```beancount
2024-01-15 * "HSA contribution"
  Assets:HSA              200.00 USD
  Assets:Bank:Checking   -200.00 USD
```

### Medical Expense from HSA

```beancount
2024-02-10 * "Doctor visit copay"
  Expenses:Health:Medical   50.00 USD
  Assets:HSA               -50.00 USD
```

### Insurance Claim

Track pending reimbursement:

```beancount
2024-02-15 * "Medical procedure"
  Expenses:Health:Medical       500.00 USD
  Assets:Receivables:Insurance  400.00 USD  ; Expected reimbursement
  Assets:Bank:Checking         -100.00 USD  ; Copay

2024-03-01 * "Insurance reimbursement"
  Assets:Bank:Checking          400.00 USD
  Assets:Receivables:Insurance -400.00 USD
```

## Tips

### Use Tags for Analysis

```beancount
2024-07-15 * "Flight to Paris" #vacation #travel
  Expenses:Travel:Flights  450.00 USD
  Liabilities:CreditCard

2024-07-16 * "Museum tickets" #vacation
  Expenses:Entertainment   25.00 USD
  Assets:Cash
```

Query vacation expenses:

```sql
SELECT sum(cost(position))
WHERE "vacation" IN tags AND account ~ "Expenses"
```

### Use Links for Related Transactions

```beancount
2024-01-10 * "Book flight" ^trip-paris-2024
  Expenses:Travel:Flights  450.00 USD
  Liabilities:CreditCard

2024-01-12 * "Book hotel" ^trip-paris-2024
  Expenses:Travel:Lodging  800.00 USD
  Liabilities:CreditCard

2024-02-01 * "Trip reimbursement" ^trip-paris-2024
  Assets:Bank:Checking         1250.00 USD
  Assets:Receivables:Employer -1250.00 USD
```

Query all trip expenses:

```sql
SELECT * WHERE "trip-paris-2024" IN links
```

## See Also

- [Syntax Reference](../reference/syntax.md) - Complete syntax guide
- [Common Queries](common-queries.md) - Useful BQL queries
- [Accounting Concepts](accounting-concepts.md) - Understanding double-entry
