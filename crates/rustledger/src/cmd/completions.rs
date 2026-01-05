//! Shell completion generation.
//!
//! Provides utilities for generating shell completion scripts using `clap_complete`.

use clap::{Command, ValueEnum};
use clap_complete::{Generator, Shell};
use std::io;

/// Shell types for completion generation.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ShellType {
    /// Bash shell completions
    Bash,
    /// Zsh shell completions
    Zsh,
    /// Fish shell completions
    Fish,
    /// `PowerShell` completions
    Powershell,
    /// Elvish shell completions
    Elvish,
}

impl Generator for ShellType {
    fn file_name(&self, name: &str) -> String {
        match self {
            Self::Bash => Shell::Bash.file_name(name),
            Self::Zsh => Shell::Zsh.file_name(name),
            Self::Fish => Shell::Fish.file_name(name),
            Self::Powershell => Shell::PowerShell.file_name(name),
            Self::Elvish => Shell::Elvish.file_name(name),
        }
    }

    fn generate(&self, cmd: &Command, buf: &mut dyn io::Write) {
        match self {
            Self::Bash => Shell::Bash.generate(cmd, buf),
            Self::Zsh => Shell::Zsh.generate(cmd, buf),
            Self::Fish => Shell::Fish.generate(cmd, buf),
            Self::Powershell => Shell::PowerShell.generate(cmd, buf),
            Self::Elvish => Shell::Elvish.generate(cmd, buf),
        }
    }
}

/// Generate shell completions and print to stdout.
pub fn generate_completions<C: clap::CommandFactory>(shell: ShellType, bin_name: &str) {
    let mut cmd = C::command();
    clap_complete::generate(shell, &mut cmd, bin_name, &mut io::stdout());
}
