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
