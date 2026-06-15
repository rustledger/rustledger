______________________________________________________________________

## title: rledger config description: Manage rustledger configuration

# rledger config

Manage rustledger configuration files and settings.

## Usage

```bash
rledger config <COMMAND>
```

## Commands

| Command | Description |
|---------|-------------|
| `show` | Show the merged configuration from all sources |
| `path` | Show config file search paths |
| `edit` | Open config file in editor |
| `init` | Generate a default config file |
| `aliases` | List configured aliases |

## Options

| Option | Description |
|--------|-------------|
| `-P, --profile <PROFILE>` | Use a specific profile from config |

## Examples

### Show Current Config

```bash
rledger config show
```

Output:

```toml
# Merged configuration (highest priority wins)
# Sources: user > system

[default]
file = "/home/user/finances/main.beancount"

[output]
format = "text"
```

### Show Config Paths

```bash
rledger config path
```

Output:

```
Configuration file search paths:

  project  (not found)  /home/user/finances/.rledger.toml
  user     (found)      /home/user/.config/rledger/config.toml
  system   (not found)  /etc/rledger/config.toml

Environment variables:
  RLEDGER_FILE     Default beancount file
  RLEDGER_FORMAT   Output format (text, csv, json)
  RLEDGER_PROFILE  Active profile name
  NO_COLOR         Disable colored output
```

### Create Default Config

```bash
rledger config init
```

Creates `~/.config/rledger/config.toml` with default settings.

### Edit Config

```bash
rledger config edit
```

Opens the config file in the editor configured via `default.editor` in the config, or the `$VISUAL`/`$EDITOR` environment variables.

### List Aliases

```bash
rledger config aliases
```

Output:

```
Configured aliases:

  bal = "report balances"
  inc = "report income"

Usage: rledger <alias> [additional args]
```

## Config File Format

See [Configuration](../getting-started/configuration.md) for the full config file reference.

## See Also

- [Configuration](../getting-started/configuration.md) - Config file reference
- [Quick Start](../getting-started/quick-start.md) - Getting started guide
