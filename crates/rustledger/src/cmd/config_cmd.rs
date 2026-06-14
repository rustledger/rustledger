//! rledger config - Configuration management commands.
//!
//! Provides subcommands for viewing and managing rledger configuration:
//!
//! - `rledger config show` - Show merged configuration
//! - `rledger config path` - Show config file search paths
//! - `rledger config edit` - Open config file in editor
//! - `rledger config init` - Generate a default config file

use crate::config::{self, Config, LoadedConfig};
use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use std::fs;
use std::io::{self, Write};

/// Configuration management commands.
#[derive(Parser, Debug)]
#[command(name = "config")]
pub struct Args {
    /// Config subcommand to run.
    #[command(subcommand)]
    pub command: ConfigCommand,
}

/// Config subcommands.
#[derive(Subcommand, Debug)]
pub enum ConfigCommand {
    /// Show the merged configuration from all sources.
    Show {
        /// Show raw configs without merging (one per source).
        #[arg(long)]
        raw: bool,

        /// Output format (toml, json).
        #[arg(long, short, default_value = "toml")]
        format: String,
    },

    /// Show config file search paths.
    Path,

    /// Open config file in editor.
    Edit {
        /// Edit project config instead of user config.
        #[arg(long, conflicts_with = "system")]
        project: bool,

        /// Edit system config instead of user config.
        #[arg(long, conflicts_with = "project")]
        system: bool,
    },

    /// Generate a default config file.
    Init {
        /// Create project config (.rledger.toml) instead of user config.
        #[arg(long)]
        project: bool,

        /// Overwrite existing config file.
        #[arg(long, short)]
        force: bool,
    },

    /// List configured aliases.
    Aliases,
}

/// Run the config command, writing output to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `run_with_writer` with a buffer so e.g.
/// `config show --format json` can be captured into an envelope.
pub fn run(args: &Args) -> Result<()> {
    let mut stdout = io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the config command, writing all stdout-bound output to `out`.
///
/// Behavior matches the original `run()`. The interactive `edit`
/// subcommand still spawns an editor and writes its status notes to
/// `out`; all other subcommands are pure read/format operations whose
/// output is redirected to the injected writer.
pub fn run_with_writer<W: Write>(args: &Args, out: &mut W) -> Result<()> {
    match &args.command {
        ConfigCommand::Show { raw, format } => run_show(*raw, format, out),
        ConfigCommand::Path => run_path(out),
        ConfigCommand::Edit { project, system } => run_edit(*project, *system, out),
        ConfigCommand::Init { project, force } => run_init(*project, *force, out),
        ConfigCommand::Aliases => run_aliases(out),
    }
}

/// Show merged configuration.
fn run_show<W: Write>(raw: bool, format: &str, out: &mut W) -> Result<()> {
    let loaded = Config::load()?;

    if raw {
        // Show each config source separately, highest precedence first
        writeln!(out, "# Configuration sources (highest precedence first)\n")?;

        for source in loaded.sources.iter().rev() {
            match source {
                config::ConfigSource::Project(path)
                | config::ConfigSource::User(path)
                | config::ConfigSource::System(path) => {
                    writeln!(out, "# === {source} ===")?;
                    if let Ok(content) = fs::read_to_string(path) {
                        writeln!(out, "{content}")?;
                    }
                    writeln!(out)?;
                }
                config::ConfigSource::Environment => {
                    writeln!(out, "# === Environment Variables ===")?;
                    if let Ok(file) = std::env::var("RLEDGER_FILE") {
                        writeln!(out, "RLEDGER_FILE={file}")?;
                    }
                    if let Ok(format) = std::env::var("RLEDGER_FORMAT") {
                        writeln!(out, "RLEDGER_FORMAT={format}")?;
                    }
                    if std::env::var("NO_COLOR").is_ok() {
                        writeln!(out, "NO_COLOR=1")?;
                    }
                    if let Ok(profile) = std::env::var("RLEDGER_PROFILE") {
                        writeln!(out, "RLEDGER_PROFILE={profile}")?;
                    }
                    writeln!(out)?;
                }
                _ => {}
            }
        }
    } else {
        // Show merged config
        print_config(&loaded, format, out)?;
    }

    Ok(())
}

/// Print configuration in the specified format.
fn print_config<W: Write>(loaded: &LoadedConfig, format: &str, stdout: &mut W) -> Result<()> {
    match format {
        "toml" => {
            writeln!(stdout, "# Merged configuration (highest priority wins)")?;
            writeln!(stdout, "# Sources: {}", format_sources(&loaded.sources))?;
            writeln!(stdout)?;

            let toml_str = toml::to_string_pretty(&loaded.config)
                .context("Failed to serialize config to TOML")?;
            writeln!(stdout, "{toml_str}")?;
        }
        "json" => {
            let json_str = serde_json::to_string_pretty(&loaded.config)
                .context("Failed to serialize config to JSON")?;
            writeln!(stdout, "{json_str}")?;
        }
        _ => {
            bail!("Unknown format: {format}. Supported: toml, json");
        }
    }

    Ok(())
}

/// Format source list for display (highest precedence first).
fn format_sources(sources: &[config::ConfigSource]) -> String {
    if sources.is_empty() {
        "default".to_string()
    } else {
        sources
            .iter()
            .rev() // Reverse to show highest precedence first
            .map(|s| match s {
                config::ConfigSource::Cli => "cli".to_string(),
                config::ConfigSource::Environment => "env".to_string(),
                config::ConfigSource::Project(_) => "project".to_string(),
                config::ConfigSource::User(_) => "user".to_string(),
                config::ConfigSource::System(_) => "system".to_string(),
                config::ConfigSource::Default => "default".to_string(),
            })
            .collect::<Vec<_>>()
            .join(" > ")
    }
}

/// Show config file search paths.
fn run_path<W: Write>(out: &mut W) -> Result<()> {
    let paths = config::config_search_paths();

    writeln!(out, "Configuration file search paths:\n")?;

    for (level, path, exists) in paths {
        let status = if exists { "(found)" } else { "(not found)" };
        writeln!(out, "  {level:8} {status:12} {}", path.display())?;
    }

    writeln!(out)?;
    writeln!(out, "Environment variables:")?;
    writeln!(out, "  RLEDGER_FILE     Default beancount file")?;
    writeln!(out, "  RLEDGER_FORMAT   Output format (text, csv, json)")?;
    writeln!(out, "  RLEDGER_PROFILE  Active profile name")?;
    writeln!(out, "  NO_COLOR         Disable colored output")?;

    Ok(())
}

/// Open config file in editor.
fn run_edit<W: Write>(project: bool, system: bool, out: &mut W) -> Result<()> {
    let path = if system {
        config::system_config_path().context("System config path not available on this platform")?
    } else if project {
        std::env::current_dir()?.join(".rledger.toml")
    } else {
        config::user_config_path().context("User config path not available")?
    };

    // Ensure parent directory exists for user config
    if !project
        && !system
        && let Some(parent) = path.parent()
        && !parent.exists()
    {
        fs::create_dir_all(parent)
            .with_context(|| format!("Failed to create directory: {}", parent.display()))?;
    }

    // Create file with default content if it doesn't exist
    if !path.exists() {
        fs::write(&path, Config::default_config_content())
            .with_context(|| format!("Failed to create config file: {}", path.display()))?;
        writeln!(out, "Created new config file: {}", path.display())?;
    }

    // Check if user has a custom editor configured (treat empty/whitespace as unset)
    let custom_editor = Config::load()
        .ok()
        .and_then(|l| l.config.default.editor)
        .and_then(|e| {
            let trimmed = e.trim();
            if trimmed.is_empty() { None } else { Some(e) }
        });

    writeln!(out, "Opening {}...", path.display())?;

    if let Some(editor) = custom_editor {
        // User has a custom editor configured - use Command directly
        // Use shell_words to properly parse quoted paths/args (e.g., "C:\Program Files\..." or 'code --wait')
        let parts = shell_words::split(&editor)
            .with_context(|| format!("Invalid editor command syntax: {editor}"))?;

        let (cmd, args) = parts.split_first().context("Editor command is empty")?;

        let status = std::process::Command::new(cmd)
            .args(args)
            .arg(&path)
            .status()
            .with_context(|| format!("Failed to run editor: {editor}"))?;

        if !status.success() {
            match status.code() {
                Some(code) => bail!("Editor exited with error (exit code {code})"),
                None => bail!("Editor terminated by signal"),
            }
        }
    } else {
        // No custom editor - use the `edit` crate for cross-platform auto-detection
        // It handles: VISUAL/EDITOR env vars, platform-specific fallbacks (notepad on Windows),
        // proper PATH/PATHEXT handling, and waiting for the editor to close
        edit::edit_file(&path).with_context(|| {
            "Failed to open editor. Set the EDITOR environment variable or configure \
             'default.editor' in your config file."
        })?;
    }

    Ok(())
}

/// Generate a default config file.
fn run_init<W: Write>(project: bool, force: bool, out: &mut W) -> Result<()> {
    let path = if project {
        std::env::current_dir()?.join(".rledger.toml")
    } else {
        config::user_config_path().context("User config path not available")?
    };

    // Check if file exists
    if path.exists() && !force {
        bail!(
            "Config file already exists: {}\nUse --force to overwrite",
            path.display()
        );
    }

    // Create parent directory if needed
    if let Some(parent) = path.parent()
        && !parent.exists()
    {
        fs::create_dir_all(parent)
            .with_context(|| format!("Failed to create directory: {}", parent.display()))?;
    }

    // Write default config
    fs::write(&path, Config::default_config_content())
        .with_context(|| format!("Failed to write config file: {}", path.display()))?;

    writeln!(out, "Created config file: {}", path.display())?;
    writeln!(out)?;
    writeln!(out, "Edit this file to set your default beancount file:")?;
    writeln!(
        out,
        "  rledger config edit{}",
        if project { " --project" } else { "" }
    )?;

    Ok(())
}

/// List configured aliases.
fn run_aliases<W: Write>(out: &mut W) -> Result<()> {
    let loaded = Config::load()?;

    if loaded.config.aliases.is_empty() {
        writeln!(out, "No aliases configured.")?;
        writeln!(out)?;
        writeln!(out, "Add aliases to your config file:")?;
        writeln!(out, "  [aliases]")?;
        writeln!(out, "  bal = \"report balances\"")?;
        writeln!(out, "  inc = \"report income\"")?;
        return Ok(());
    }

    writeln!(out, "Configured aliases:\n")?;

    // Sort aliases by name for consistent output
    let mut aliases: Vec<_> = loaded.config.aliases.iter().collect();
    aliases.sort_by_key(|(name, _)| *name);

    for (name, expansion) in aliases {
        writeln!(out, "  {name} = \"{expansion}\"")?;
    }

    writeln!(out)?;
    writeln!(out, "Usage: rledger <alias> [additional args]")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_format_sources() {
        // Sources are stored in load order (lowest to highest precedence)
        let sources = vec![
            config::ConfigSource::User("/home/user/.config/rledger/config.toml".into()),
            config::ConfigSource::Project("/test/.rledger.toml".into()),
        ];

        // format_sources reverses to show highest precedence first
        let formatted = format_sources(&sources);
        assert_eq!(formatted, "project > user");
    }

    #[test]
    fn test_format_sources_empty() {
        let sources = vec![];
        let formatted = format_sources(&sources);
        assert_eq!(formatted, "default");
    }

    #[test]
    fn test_init_creates_config() {
        let temp = TempDir::new().unwrap();
        let config_path = temp.path().join("config.toml");

        // Manually create config since run_init uses fixed paths
        fs::write(&config_path, Config::default_config_content()).unwrap();

        assert!(config_path.exists());
        let content = fs::read_to_string(&config_path).unwrap();
        assert!(content.contains("[default]"));
        assert!(content.contains("# file ="));
    }

    #[test]
    fn test_format_sources_all_types() {
        // Sources in load order (lowest to highest precedence)
        let sources = vec![
            config::ConfigSource::System("/etc/rledger/config.toml".into()),
            config::ConfigSource::User("/home/user/.config/rledger/config.toml".into()),
            config::ConfigSource::Project("/project/.rledger.toml".into()),
            config::ConfigSource::Environment,
        ];

        let formatted = format_sources(&sources);
        // Should be reversed to show highest precedence first
        assert_eq!(formatted, "env > project > user > system");
    }

    #[test]
    fn test_format_sources_cli() {
        let sources = vec![config::ConfigSource::Cli];
        let formatted = format_sources(&sources);
        assert_eq!(formatted, "cli");
    }

    #[test]
    fn test_format_sources_default() {
        let sources = vec![config::ConfigSource::Default];
        let formatted = format_sources(&sources);
        assert_eq!(formatted, "default");
    }

    #[test]
    fn test_config_command_parsing() {
        use clap::Parser;

        // Test show command
        let args = Args::try_parse_from(["config", "show"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Show { raw: false, .. }
        ));

        // Test show --raw
        let args = Args::try_parse_from(["config", "show", "--raw"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Show { raw: true, .. }
        ));

        // Test show --format json
        let args = Args::try_parse_from(["config", "show", "--format", "json"]).unwrap();
        if let ConfigCommand::Show { format, .. } = args.command {
            assert_eq!(format, "json");
        }

        // Test path command
        let args = Args::try_parse_from(["config", "path"]).unwrap();
        assert!(matches!(args.command, ConfigCommand::Path));

        // Test edit command
        let args = Args::try_parse_from(["config", "edit"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Edit {
                project: false,
                system: false
            }
        ));

        // Test edit --project
        let args = Args::try_parse_from(["config", "edit", "--project"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Edit {
                project: true,
                system: false
            }
        ));

        // Test edit --system
        let args = Args::try_parse_from(["config", "edit", "--system"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Edit {
                project: false,
                system: true
            }
        ));

        // Test init command
        let args = Args::try_parse_from(["config", "init"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Init {
                project: false,
                force: false
            }
        ));

        // Test init --project
        let args = Args::try_parse_from(["config", "init", "--project"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Init {
                project: true,
                force: false
            }
        ));

        // Test init --force
        let args = Args::try_parse_from(["config", "init", "--force"]).unwrap();
        assert!(matches!(
            args.command,
            ConfigCommand::Init {
                project: false,
                force: true
            }
        ));

        // Test aliases command
        let args = Args::try_parse_from(["config", "aliases"]).unwrap();
        assert!(matches!(args.command, ConfigCommand::Aliases));
    }

    #[test]
    fn test_edit_conflicts_with() {
        use clap::Parser;

        // --project and --system should conflict
        let result = Args::try_parse_from(["config", "edit", "--project", "--system"]);
        assert!(result.is_err());
    }

    #[test]
    fn test_default_config_content_is_valid_toml() {
        let content = Config::default_config_content();
        // Should parse as valid TOML (comments are allowed)
        let result: Result<Config, _> = toml::from_str(&content);
        assert!(result.is_ok());
    }

    #[test]
    fn test_config_show_format_options() {
        // Just verify the format parameter exists and accepts expected values
        use clap::Parser;

        let args = Args::try_parse_from(["config", "show", "-f", "toml"]).unwrap();
        if let ConfigCommand::Show { format, .. } = args.command {
            assert_eq!(format, "toml");
        }

        let args = Args::try_parse_from(["config", "show", "-f", "json"]).unwrap();
        if let ConfigCommand::Show { format, .. } = args.command {
            assert_eq!(format, "json");
        }
    }

    #[test]
    fn test_editor_command_parsing() {
        // Simple command
        let parts = shell_words::split("vim").unwrap();
        assert_eq!(parts, vec!["vim"]);

        // Command with args
        let parts = shell_words::split("code --wait").unwrap();
        assert_eq!(parts, vec!["code", "--wait"]);

        // Quoted path with spaces (Windows-style)
        let parts =
            shell_words::split(r#""C:\Program Files\Notepad++\notepad++.exe" -multiInst"#).unwrap();
        assert_eq!(
            parts,
            vec![r"C:\Program Files\Notepad++\notepad++.exe", "-multiInst"]
        );

        // Single-quoted path
        let parts = shell_words::split("'/usr/bin/my editor' --wait").unwrap();
        assert_eq!(parts, vec!["/usr/bin/my editor", "--wait"]);
    }

    #[test]
    fn test_editor_empty_handling() {
        // Empty string should result in None from our filter
        let editor: Option<String> = Some(String::new());
        let filtered = editor.and_then(|e| {
            let trimmed = e.trim();
            if trimmed.is_empty() { None } else { Some(e) }
        });
        assert!(filtered.is_none());

        // Whitespace-only should also result in None
        let editor: Option<String> = Some(String::from("   "));
        let filtered = editor.and_then(|e| {
            let trimmed = e.trim();
            if trimmed.is_empty() { None } else { Some(e) }
        });
        assert!(filtered.is_none());

        // Non-empty should pass through
        let editor: Option<String> = Some(String::from("vim"));
        let filtered = editor.and_then(|e| {
            let trimmed = e.trim();
            if trimmed.is_empty() { None } else { Some(e) }
        });
        assert_eq!(filtered, Some(String::from("vim")));
    }
}
