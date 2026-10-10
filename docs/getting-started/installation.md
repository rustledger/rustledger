______________________________________________________________________

## title: Installation description: Install rustledger on macOS, Linux, or Windows

# Installation

## Package Managers

### macOS / Linux (Homebrew)

```bash
brew install rustledger
```

### Arch Linux

```bash
yay -S rustledger-bin
```

### Fedora / RHEL

```bash
sudo dnf copr enable robcohen/rustledger
sudo dnf install rustledger
```

### Windows (Scoop)

```powershell
scoop bucket add rustledger https://github.com/rustledger/scoop-rustledger
scoop install rustledger
```

### Cargo (Rust)

```bash
# Using cargo-binstall (recommended, downloads pre-built binary)
cargo binstall rustledger

# Or build from source
cargo install rustledger
```

### Nix

```bash
# Run without installing
nix run github:rustledger/rustledger

# Or add to your flake
{
  inputs.rustledger.url = "github:rustledger/rustledger";
}
```

### Docker

```bash
docker run --rm -v "$PWD:/data" ghcr.io/rustledger/rustledger check /data/ledger.beancount
```

### Pre-built Binaries

Download from [GitHub Releases](https://github.com/rustledger/rustledger/releases):

| Platform | Download |
|----------|----------|
| Linux x86_64 | `rustledger-v<VERSION>-x86_64-unknown-linux-gnu.tar.gz` |
| Linux ARM64 | `rustledger-v<VERSION>-aarch64-unknown-linux-gnu.tar.gz` |
| macOS x86_64 | `rustledger-v<VERSION>-x86_64-apple-darwin.tar.gz` |
| macOS ARM64 | `rustledger-v<VERSION>-aarch64-apple-darwin.tar.gz` |
| Windows x86_64 | `rustledger-v<VERSION>-x86_64-pc-windows-msvc.zip` |

Replace `<VERSION>` with the release version (e.g., `0.15.0`).

## Plugin Runtimes

The install routes above do not all give the same `rledger`. Release binaries are built without the WASM and Python plugin runtimes, on purpose (smaller, and no plugin sandbox to trust). They run every [built-in native plugin](../reference/plugins.md#built-in-plugins), but not:

- Python plugins (`plugin "my_plugin.py"`, `plugin "python:..."`),
- WASM plugins (`plugin "my_plugin.wasm"`, `rledger check --plugin`),
- WASM importers (`rledger extract --wasm-importer`, `--wasm-importer-dir`).

Asked for one of these, a release binary stops with an error saying the runtimes are missing and naming `cargo install rustledger`.

| Route | Plugin runtimes |
|-------|-----------------|
| GitHub Releases binaries, `cargo binstall`, Homebrew, Scoop, `rustledger-bin` (AUR) | No (release binaries) |
| `cargo install rustledger` | Yes (the default `python-plugin-wasm` feature) |
| Building from source (`cargo build`), `rustledger` (AUR), Fedora COPR, Docker, Nix | Yes (default features) |

To run Python or WASM plugins or WASM importers, install with:

```bash
cargo install rustledger
```

A source build with `--no-default-features` (for a platform the WASM runtime does not build on, such as Termux) leaves them out, as the release binaries do.

## Verify Installation

```bash
rledger --version
```

You should see output like:

```
rledger 0.15.0
```

## Shell Completions

Generate shell completions for your shell:

```bash
# Bash
rledger completions bash > ~/.local/share/bash-completion/completions/rledger

# Zsh
rledger completions zsh > ~/.zfunc/_rledger

# Fish
rledger completions fish > ~/.config/fish/completions/rledger.fish

# PowerShell
rledger completions powershell > $HOME\Documents\PowerShell\Modules\rledger.ps1
```

## Next Steps

- [Quick Start](quick-start.md) - Run your first commands
- [Configuration](configuration.md) - Customize rustledger
