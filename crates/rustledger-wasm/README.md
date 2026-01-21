# rustledger-wasm

WebAssembly bindings for rustledger, enabling Beancount functionality in JavaScript/TypeScript.

## Features

| Feature | Description |
|---------|-------------|
| `parse()` | Parse Beancount source to JSON |
| `validateSource()` | Validate ledger with error reporting |
| `query()` | Run BQL queries |
| `format()` | Format source with consistent alignment |
| `expandPads()` | Expand pad directives |
| `runPlugin()` | Run native plugins (with `plugins` feature) |
| `bqlCompletions()` | BQL query completions (with `completions` feature) |
| `ParsedLedger` | Stateful class with LSP-like editor features |

## Example

```javascript
import init, { parse, validateSource, query } from '@rustledger/wasm';

await init();

const source = `
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
`;

const result = parse(source);
if (result.errors.length === 0) {
    const validation = validateSource(source);
    console.log('Valid:', validation.valid);

    const balances = query(source, 'BALANCES');
    console.log('Balances:', balances.rows);
}
```

## Stateful API

For multiple operations on the same source, use `ParsedLedger` to avoid re-parsing:

```javascript
import { ParsedLedger } from '@rustledger/wasm';

const ledger = new ParsedLedger(source);

if (ledger.isValid()) {
    const balances = ledger.balances();
    const formatted = ledger.format();

    // Editor features
    const completions = ledger.getCompletions(5, 10);
    const hover = ledger.getHoverInfo(3, 5);
    const definition = ledger.getDefinition(4, 3);
}

ledger.free(); // Release WASM memory
```

## Cargo Features

- `plugins` (default) - Include native plugin support
- `completions` (default) - Include BQL query completions

## Building

```bash
wasm-pack build --target web crates/rustledger-wasm
```

## License

GPL-3.0
