# rustledger-plugin

Beancount plugin system with 30 native plugins and WASM support.

## Native Plugins

| Plugin | Description |
|--------|-------------|
| `auto_accounts` | Auto-generate Open directives |
| `auto_tag` | Automatically tag transactions |
| `box_accrual` | Accrual accounting for boxed periods |
| `gain_loss` | Split capital gains into gain/loss accounts |
| `long_short` | Split capital gains by holding period |
| `check_average_cost` | Validate average cost bookings |
| `check_closing` | Zero balance on account close |
| `check_commodity` | Validate commodity declarations |
| `check_drained` | Ensure accounts drained before close |
| `close_tree` | Close descendant accounts |
| `coherent_cost` | Enforce cost OR price (not both) |
| `commodity_attr` | Validate commodity attributes |
| `currency_accounts` | Auto-generate currency trading postings |
| `effective_date` | Override posting date via metadata |
| `forecast` | Generate recurring transactions |
| `generate_base_ccy_prices` | Create base currency price entries |
| `implicit_prices` | Generate prices from costs |
| `leafonly` | Error on non-leaf account postings |
| `noduplicates` | Detect duplicate transactions |
| `nounused` | Warn on unused accounts |
| `onecommodity` | Single commodity per account |
| `pedantic` | Enable all strict validations |
| `rename_accounts` | Rename accounts via metadata |
| `rx_txn_plugin` | Link related transactions |
| `sellgains` | Cross-check capital gains |
| `split_expenses` | Split expenses across accounts |
| `unique_prices` | One price per day per pair |
| `unrealized` | Calculate unrealized gains |
| `valuation` | Mark-to-market valuation |
| `zerosum` | Group transactions that sum to zero |

Additionally, `document_discovery` is available for auto-discovering document files from directories specified in `option "documents"`.

## Example

```rust
use rustledger_plugin::{NativePluginRegistry, PluginInput, PluginOptions};

let registry = NativePluginRegistry::global();
let plugin = registry.find_synth("auto_accounts").unwrap();

let input = PluginInput {
    directives: vec![],
    options: PluginOptions { operating_currencies: vec![], title: None },
    config: None,
};
let output = plugin.process(input);
```

## Cargo Features

- `wasm-runtime` (default) - WASM plugin support via Wasmtime
- `python-plugins` - Run Python beancount plugins via WASI sandbox

## License

GPL-3.0
