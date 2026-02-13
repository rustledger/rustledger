# Validation Errors Reference

rustledger validates ledgers and reports these error types:

## Account Errors
- **E0001**: Account not opened before use
- **E0002**: Account already opened
- **E0003**: Account closed but still has transactions
- **E0004**: Invalid account name format

## Balance Errors
- **E0101**: Balance assertion failed
- **E0102**: Negative balance not allowed

## Transaction Errors
- **E0201**: Transaction does not balance
- **E0202**: Missing posting amount (only one allowed)
- **E0203**: Currency mismatch in transaction

## Booking Errors
- **E0301**: Ambiguous lot matching
- **E0302**: Insufficient lots for reduction
- **E0303**: Cost basis mismatch

## Date Errors
- **E0401**: Future date not allowed
- **E0402**: Date out of order

## Document/Note Errors
- **E0501**: Document file not found
- **E0502**: Invalid document path

## Plugin Errors
- **E0601**: Plugin not found
- **E0602**: Plugin execution error

## Parse Errors
- **E0701**: Syntax error
- **E0702**: Invalid directive format
- **E0703**: Duplicate option
