# Golden Test Vectors and Fixtures

This document catalogs all known test sources from the Python Beancount implementation and related projects.

## Primary Sources

### 1. beancount-parser-lima Test Cases (220 files)

**Location:** https://github.com/tesujimath/beancount-parser-lima/tree/main/test-cases

These are the most comprehensive parser test fixtures, extracted from the Python beancount test suite.

#### Arithmetic Tests (10 files)
```
Arithmetic.NumberExprAdd.beancount
Arithmetic.NumberExprDifferentPlaces.beancount
Arithmetic.NumberExprDifferentPlaces2.beancount
Arithmetic.NumberExprDivide.beancount
Arithmetic.NumberExprGroups.beancount
Arithmetic.NumberExprMultiply.beancount
Arithmetic.NumberExprNegative.beancount
Arithmetic.NumberExprPositive.beancount
Arithmetic.NumberExprPrecedence.beancount
Arithmetic.NumberExprSubtract.beancount
```

#### Balance Tests (2 files)
```
Balance.TotalCost.beancount
Balance.TotalPrice.beancount
```

#### Comment Tests (5 files)
```
Comment.CommentAfterPostings.beancount
Comment.CommentAfterTransaction.beancount
Comment.CommentAfterTransactionStart.beancount
Comment.CommentBeforeTransaction.beancount
Comment.CommentBetweenPostings.beancount
```

#### Currency Tests (2 files)
```
Currencies.DifferentCostAndPriceCurrency.beancount
Currencies.ParseCurrencies.beancount
```

#### Deprecated Options (2 files)
```
DeprecatedOptions.DeprecatedOption.beancount
DeprecatedOptions.DeprecatedPlugin.beancount
```

#### Display Context Options (4 files)
```
DisplayContextOptions.RenderCommasError.beancount
DisplayContextOptions.RenderCommasNo.beancount
DisplayContextOptions.RenderCommasYes.beancount
DisplayContextOptions.RenderCommasYes2.beancount
```

#### Document Tests (3 files)
```
Document.DocumentLinks.beancount
Document.DocumentNoTagsLinks.beancount
Document.DocumentTags.beancount
```

#### Expression Tests (2 files)
```
Expressions.ExplicitPrecision.beancount
Expressions.ExplicitPrecision2.beancount
```

#### Incomplete Inputs Tests (26 files)
```
IncompleteInputs.CostAverage.beancount
IncompleteInputs.CostAverageMissingBasis.beancount
IncompleteInputs.CostAverageWithOther.beancount
IncompleteInputs.CostEmpty.beancount
IncompleteInputs.CostEmptyWithOther.beancount
IncompleteInputs.CostFull.beancount
IncompleteInputs.CostMissingBasis.beancount
IncompleteInputs.CostMissingCurrency.beancount
IncompleteInputs.CostMissingNumberPer.beancount
IncompleteInputs.CostMissingNumberTotal.beancount
IncompleteInputs.CostMissingNumbers.beancount
IncompleteInputs.CostNoNumberTotal.beancount
IncompleteInputs.PriceMissing.beancount
IncompleteInputs.PriceMissingCurrency.beancount
IncompleteInputs.PriceMissingNumber.beancount
IncompleteInputs.PriceNone.beancount
IncompleteInputs.UnitsFull.beancount
IncompleteInputs.UnitsMissing.beancount
IncompleteInputs.UnitsMissingCurrency.beancount
IncompleteInputs.UnitsMissingCurrencyWithCost.beancount
IncompleteInputs.UnitsMissingCurrencyWithPrice.beancount
IncompleteInputs.UnitsMissingNumber.beancount
IncompleteInputs.UnitsMissingNumberWithCost.beancount
IncompleteInputs.UnitsMissingNumberWithPrice.beancount
IncompleteInputs.UnitsMissingWithCost.beancount
IncompleteInputs.UnitsMissingWithPrice.beancount
```

#### Lexer and Parser Error Tests (35 files)
```
LexerAndParserErrors.GrammarExceptionsAmount.beancount
LexerAndParserErrors.GrammarExceptionsBalance.beancount
LexerAndParserErrors.GrammarExceptionsClose.beancount
LexerAndParserErrors.GrammarExceptionsCommodity.beancount
LexerAndParserErrors.GrammarExceptionsCompoundAmount.beancount
LexerAndParserErrors.GrammarExceptionsDocument.beancount
LexerAndParserErrors.GrammarExceptionsEvent.beancount
LexerAndParserErrors.GrammarExceptionsInclude.beancount
LexerAndParserErrors.GrammarExceptionsKeyValue.beancount
LexerAndParserErrors.GrammarExceptionsLotCostDate.beancount
LexerAndParserErrors.GrammarExceptionsNote.beancount
LexerAndParserErrors.GrammarExceptionsOpen.beancount
LexerAndParserErrors.GrammarExceptionsOption.beancount
LexerAndParserErrors.GrammarExceptionsPad.beancount
LexerAndParserErrors.GrammarExceptionsPlugin.beancount
LexerAndParserErrors.GrammarExceptionsPoptag.beancount
LexerAndParserErrors.GrammarExceptionsPosting.beancount
LexerAndParserErrors.GrammarExceptionsPrice.beancount
LexerAndParserErrors.GrammarExceptionsPushtag.beancount
LexerAndParserErrors.GrammarExceptionsTagLinkLink.beancount
LexerAndParserErrors.GrammarExceptionsTagLinkNew.beancount
LexerAndParserErrors.GrammarExceptionsTagLinkPipe.beancount
LexerAndParserErrors.GrammarExceptionsTagLinkTag.beancount
LexerAndParserErrors.GrammarExceptionsTransaction.beancount
LexerAndParserErrors.GrammarSyntaxError.beancount
LexerAndParserErrors.GrammarSyntaxErrorMultiple.beancount
LexerAndParserErrors.GrammarSyntaxErrorRecovery.beancount
LexerAndParserErrors.GrammarSyntaxErrorRecovery2.beancount
LexerAndParserErrors.LexerErrorsInPostings.beancount
LexerAndParserErrors.LexerException.beancount
LexerAndParserErrors.LexerExceptionRecovery.beancount
LexerAndParserErrors.LexerInvalidToken.beancount
LexerAndParserErrors.LexerInvalidTokenRecovery.beancount
LexerAndParserErrors.ParsingErrorAtRoot.beancount
```

#### Metadata Tests (11 files)
```
MetaData.MetadataDataTypes.beancount
MetaData.MetadataEmpty.beancount
MetaData.MetadataKeySyntax.beancount
MetaData.MetadataOther.beancount
MetaData.MetadataTransactionBegin.beancount
MetaData.MetadataTransactionEnd.beancount
MetaData.MetadataTransactionIndented.beancount
MetaData.MetadataTransactionMany.beancount
MetaData.MetadataTransactionMiddle.beancount
MetaData.MetadataTransactionRepeated.beancount
MetaData.MetadataTransactionRepeated2.beancount
```

#### Miscellaneous Tests (5 files)
```
Misc.CommentInPostings.beancount
Misc.CommentInPostingsInvalid.beancount
MiscOptions.PluginProcessingModeDefault.beancount
MiscOptions.PluginProcessingModeInvalid.beancount
MiscOptions.PluginProcessingModeRaw.beancount
```

#### Multiline Tests (1 file)
```
MultipleLines.MultilineNarration.beancount
```

#### Parse Lots Tests (18 files)
```
ParseLots.CostAmount.beancount
ParseLots.CostBothCosts.beancount
ParseLots.CostDate.beancount
ParseLots.CostEmpty.beancount
ParseLots.CostEmptyComponents.beancount
ParseLots.CostLabel.beancount
ParseLots.CostMerge.beancount
ParseLots.CostNone.beancount
ParseLots.CostRepeated.beancount
ParseLots.CostRepeatedDate.beancount
ParseLots.CostRepeatedLabel.beancount
ParseLots.CostRepeatedMerge.beancount
ParseLots.CostThreeComponents.beancount
ParseLots.CostTotalCostOnly.beancount
ParseLots.CostTotalEmptyTotal.beancount
ParseLots.CostTotalJustCurrency.beancount
ParseLots.CostTwoComponents.beancount
ParseLots.CostWithSlashes.beancount
```

#### Parser Complete Tests (13 files)
```
Parser.BasicTesting.beancount
ParserComplete.Comment.beancount
ParserComplete.CommentEOF.beancount
ParserComplete.Empty1.beancount
ParserComplete.Empty2.beancount
ParserComplete.ExtraWhitespaceComment.beancount
ParserComplete.ExtraWhitespaceCommentIndented.beancount
ParserComplete.ExtraWhitespaceNote.beancount
ParserComplete.ExtraWhitespaceTransaction.beancount
ParserComplete.IndentEOF.beancount
ParserComplete.NoEmptyLines.beancount
ParserComplete.TransactionImbalanceFromSinglePosting.beancount
ParserComplete.TransactionSinglePostingAtZero.beancount
```

#### Parser Entry Types (20 files)
```
ParserEntryTypes.Balance.beancount
ParserEntryTypes.BalanceWithCost.beancount
ParserEntryTypes.Close.beancount
ParserEntryTypes.Commodity.beancount
ParserEntryTypes.Custom.beancount
ParserEntryTypes.Document.beancount
ParserEntryTypes.Event.beancount
ParserEntryTypes.Note.beancount
ParserEntryTypes.Open1.beancount
ParserEntryTypes.Open2.beancount
ParserEntryTypes.Open3.beancount
ParserEntryTypes.Open4.beancount
ParserEntryTypes.Open5.beancount
ParserEntryTypes.Pad.beancount
ParserEntryTypes.Price.beancount
ParserEntryTypes.Query.beancount
ParserEntryTypes.TransactionOneString.beancount
ParserEntryTypes.TransactionThreeStrings.beancount
ParserEntryTypes.TransactionTwoStrings.beancount
ParserEntryTypes.TransactionWithTxnKeyword.beancount
```

#### Parser Include Tests (5 files)
```
ParserInclude.IncludeAbsolute.beancount
ParserInclude.IncludeCycle.beancount
ParserInclude.IncludeDuplicate.beancount
ParserInclude.IncludeRelative.beancount
ParserInclude.IncludeRelativeFromString.beancount
```

#### Parser Links/Options/Plugin Tests (13 files)
```
ParserLinks.ParseLinks.beancount
ParserOptions.InvalidAccountNames.beancount
ParserOptions.InvalidOption.beancount
ParserOptions.LegacyTranslations.beancount
ParserOptions.OptionListValue.beancount
ParserOptions.OptionSingleValue.beancount
ParserOptions.ReadonlyOption.beancount
ParserOptions.ToleranceMapValue.beancount
ParserPlugin.Plugin.beancount
ParserPlugin.PluginAsOption.beancount
ParserPlugin.PluginWithConfig.beancount
```

#### Push/Pop Meta and Tag Tests (8 files)
```
PushPopMeta.PushmetaForgotten.beancount
PushPopMeta.PushmetaInvalidPop.beancount
PushPopMeta.PushmetaNormal.beancount
PushPopMeta.PushmetaOverride.beancount
PushPopMeta.PushmetaShadow.beancount
PushPopTag.Multiple.beancount
PushPopTag.PopInvalidTag.beancount
PushPopTag.TagLeftUnclosed.beancount
```

#### Syntax Error Tests (4 files)
```
SyntaxErrors.ErrorInPosting.beancount
SyntaxErrors.ErrorInTransactionLine.beancount
SyntaxErrors.NoFinalNewline.beancount
SyntaxErrors.SingleErrorTokenAtTopLevel.beancount
```

#### Totals and Signs Tests (12 files)
```
TotalsAndSigns.CostNegative.beancount
TotalsAndSigns.PriceNegative.beancount
TotalsAndSigns.TotalCost.beancount
TotalsAndSigns.TotalCostInvalid.beancount
TotalsAndSigns.TotalCostNegative.beancount
TotalsAndSigns.TotalPriceInverted.beancount
TotalsAndSigns.TotalPriceNegative.beancount
TotalsAndSigns.TotalPricePositive.beancount
TotalsAndSigns.TotalPriceWithMissing.beancount
TotalsAndSigns.TotalPriceWithMissing2.beancount
TotalsAndSigns.ZeroAmount.beancount
TotalsAndSigns.ZeroCost.beancount
```

#### Transaction Tests (18 files)
```
Transactions.BlankLineNotAllowed.beancount
Transactions.BlankLineWithSpacesNotAllowed.beancount
Transactions.EmptyNarration.beancount
Transactions.Imbalance.beancount
Transactions.LinkAndThenTag.beancount
Transactions.MultipleTagsLinksOnMetadataLine.beancount
Transactions.NoNarration.beancount
Transactions.NoPostings.beancount
Transactions.PayeeNoNarration.beancount
Transactions.Simple1.beancount
Transactions.Simple2.beancount
Transactions.TagThenLink.beancount
Transactions.TagsAfterFirstLine.beancount
Transactions.TagsAfterFirstPosting.beancount
Transactions.TooManyStrings.beancount
Transactions.ZeroCosts.beancount
Transactions.ZeroPrices.beancount
Transactions.ZeroUnits.beancount
```

#### Whitespace Tests (2 files)
```
Whitespace.IndentError0.beancount
Whitespace.IndentError1.beancount
```

### 2. Python Beancount Test Files

**Location:** https://github.com/beancount/beancount/tree/master/beancount/parser

| Test File | Coverage |
|-----------|----------|
| `grammar_test.py` | ~150 parser test methods |
| `lexer_test.py` | Lexer/tokenizer tests |
| `booking_test.py` | Basic booking validation |
| `booking_full_test.py` | Comprehensive booking (FIFO, LIFO, STRICT, NONE) |
| `booking_method_test.py` | Booking method-specific tests |
| `options_test.py` | Option parsing tests |
| `printer_test.py` | Pretty-printing tests |
| `context_test.py` | Context/include tests |

### 3. Booking Test Cases (from booking_full_test.py)

#### STRICT Booking Tests
```
test_augment__from_empty__no_cost__pos
test_augment__from_empty__no_cost__neg
test_augment__from_empty__at_cost__pos
test_augment__from_empty__at_cost__neg
test_augment__from_empty__incomplete_cost__empty
test_augment__from_empty__incomplete_cost__with_currency
test_reduce__no_cost
test_reduce__sign_change_simple
test_reduce__no_match
test_reduce__unambiguous
test_reduce__ambiguous__strict
test_reduce__other_currency
test_reduce__missing_units_number
test_reduce__multiple_reductions__competing__with_error
test_reduce__multiple_reductions__no_error_because_total
test_ambiguous__STRICT_1
test_ambiguous__STRICT_2
test_ambiguous__STRICT__mixed
```

#### FIFO Booking Tests
```
test_ambiguous__FIFO__no_match_against_any_lots
test_ambiguous__FIFO__test_match_against_partial_first_lot
test_ambiguous__FIFO__test_match_against_complete_first_lot
test_ambiguous__FIFO__test_partial_match_against_first_two_lots
test_ambiguous__FIFO__test_complete_match_against_first_two_lots
test_ambiguous__FIFO__test_partial_match_against_first_three_lots
test_ambiguous__FIFO__test_complete_match_against_first_three_lots
test_ambiguous__FIFO__test_matching_more_than_is_available
```

#### LIFO Booking Tests
```
test_ambiguous__LIFO__no_match_against_any_lots
test_ambiguous__LIFO__test_match_against_partial_first_lot
test_ambiguous__LIFO__test_match_against_complete_first_lot
test_ambiguous__LIFO__test_partial_match_against_first_two_lots
test_ambiguous__LIFO__test_complete_match_against_first_two_lots
test_ambiguous__LIFO__test_partial_match_against_first_three_lots
test_ambiguous__LIFO__test_complete_match_against_first_three_lots
test_ambiguous__LIFO__test_matching_more_than_is_available
```

#### NONE Booking Tests
```
test_reduce__ambiguous__none
test_reduce__ambiguous__none__from_mixed
test_ambiguous__NONE__notmatching_nonmixed1
test_ambiguous__NONE__notmatching_nonmixed2
test_ambiguous__NONE__notmatching_mixed1
test_ambiguous__NONE__notmatching_mixed2
test_ambiguous__NONE__matching_existing1
test_ambiguous__NONE__matching_existing2
```

### 4. Example Files (Integration Tests)

**Location:** https://github.com/beancount/beancount/tree/v2/examples

| File/Directory | Description |
|----------------|-------------|
| `example.beancount` | Main 3000+ line comprehensive example |
| `simple/` | Simple annotated examples |
| `tutorial/` | Tutorial output files |
| `sharing/` | Expense sharing example |
| `vesting/` | RSU vesting tracking example |
| `forecast/` | Forecasting plugin example |
| `ingest/` | Import configuration example |

## Obtaining Test Vectors

### Download beancount-parser-lima test cases

```bash
git clone https://github.com/tesujimath/beancount-parser-lima.git
cp -r beancount-parser-lima/test-cases spec/fixtures/lima-tests/
```

### Download Python beancount examples

```bash
git clone https://github.com/beancount/beancount.git --branch v2 --depth 1
cp -r beancount/examples spec/fixtures/examples/
```

### Extract embedded test cases from Python

```python
# Script to extract test cases from grammar_test.py
import ast
import re

with open('beancount/parser/grammar_test.py') as f:
    content = f.read()

# Find all docstrings containing beancount input
pattern = r'"""(.*?)"""'
matches = re.findall(pattern, content, re.DOTALL)

for i, match in enumerate(matches):
    if 'open Assets' in match or '* "' in match:
        with open(f'extracted_test_{i}.beancount', 'w') as f:
            f.write(match.strip())
```

## Test Categories Checklist

### Parser Tests
- [ ] All 12 directive types parse correctly
- [ ] Comments (line, inline, org-mode)
- [ ] Strings (simple, multiline, unicode, escapes)
- [ ] Numbers (integers, decimals, commas, expressions)
- [ ] Dates (YYYY-MM-DD, YYYY/MM/DD)
- [ ] Accounts (all 5 root types, deep nesting)
- [ ] Currencies (standard, tickers, special chars)
- [ ] Amounts (with cost, with price, both)
- [ ] Costs ({}, {{total}}, with date/label)
- [ ] Tags and links
- [ ] Metadata (all value types)
- [ ] Options
- [ ] Includes (relative, absolute, cycle detection)
- [ ] Push/pop tag and meta

### Error Recovery Tests
- [ ] Lexer errors
- [ ] Grammar errors
- [ ] Recovery continues after error
- [ ] Multiple errors in one file
- [ ] Error locations are accurate

### Booking Tests
- [ ] STRICT: exact match required
- [ ] STRICT: ambiguous match rejected
- [ ] STRICT: total match accepted
- [ ] FIFO: oldest lot first
- [ ] FIFO: partial lot reduction
- [ ] FIFO: multi-lot reduction
- [ ] LIFO: newest lot first
- [ ] LIFO: partial lot reduction
- [ ] LIFO: multi-lot reduction
- [ ] NONE: no matching, allows mixed
- [ ] AVERAGE: weighted average recalculation (if implementing)

### Validation Tests
- [ ] Account not opened
- [ ] Account already closed
- [ ] Balance assertion failed
- [ ] Transaction not balanced
- [ ] Currency constraint violation
- [ ] Duplicate metadata key

### Integration Tests
- [ ] example.beancount loads without errors
- [ ] Output matches Python beancount

## Compatibility Testing

### Running Comparison Tests

```bash
#!/bin/bash
# compare.sh - Compare rustledger against Python beancount

FILE=$1

# Run Python beancount
python -m beancount.scripts.check "$FILE" 2>&1 | sort > /tmp/python-output.txt

# Run Rust implementation
rustledger check "$FILE" 2>&1 | sort > /tmp/rust-output.txt

# Compare
diff /tmp/python-output.txt /tmp/rust-output.txt
```

### Known Differences to Track

Document any intentional deviations from Python behavior:

| Feature | Python Behavior | Rust Behavior | Reason |
|---------|-----------------|---------------|--------|
| (none yet) | | | |

## References

- [beancount-parser-lima](https://github.com/tesujimath/beancount-parser-lima) - Most complete Rust parser
- [Python beancount](https://github.com/beancount/beancount) - Reference implementation
- [Beancount docs](https://beancount.github.io/docs/) - Official documentation
