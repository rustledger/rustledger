{
  description = "rustledger - A pure Rust implementation of Beancount";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust toolchain
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Rust build system
    crane.url = "github:ipetkov/crane";

    # Formatting
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Pre-commit hooks
    git-hooks-nix = {
      url = "github:cachix/git-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Process management for dev
    process-compose-flake.url = "github:Platonic-Systems/process-compose-flake";

    # Advisory database for cargo-audit
    advisory-db = {
      url = "github:rustsec/advisory-db";
      flake = false;
    };
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        inputs.treefmt-nix.flakeModule
        inputs.git-hooks-nix.flakeModule
        # Disabled for now - process-compose requires configuration
        # inputs.process-compose-flake.flakeModule
      ];

      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem = { config, self', inputs', pkgs, system, lib, ... }:
        let
          # Rust toolchain with all needed components
          rustToolchain = inputs'.fenix.packages.stable.withComponents [
            "cargo"
            "clippy"
            "rust-src"
            "rustc"
            "rustfmt"
            "llvm-tools-preview" # For coverage
          ];

          # Nightly for fuzzing and some tools
          rustNightly = inputs'.fenix.packages.latest.withComponents [
            "cargo"
            "rustc"
            "rust-src"
          ];

          # WASM target
          rustWasm = inputs'.fenix.packages.targets.wasm32-unknown-unknown.stable.rust-std;

          # Combined toolchain with WASM
          rustToolchainWithWasm = inputs'.fenix.packages.combine [
            rustToolchain
            rustWasm
          ];

          # Crane lib with our toolchain
          craneLib = (inputs.crane.mkLib pkgs).overrideToolchain rustToolchainWithWasm;

          # Common arguments for crane builds
          commonArgs = {
            src = craneLib.cleanCargoSource ./.;
            strictDeps = true;

            buildInputs = [
              # Add platform-specific deps here
            ] ++ lib.optionals pkgs.stdenv.isDarwin [
              pkgs.libiconv
              pkgs.darwin.apple_sdk.frameworks.Security
              pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
            ];

            nativeBuildInputs = [
              pkgs.pkg-config
            ];
          };

          # Build dependencies only (for caching)
          cargoArtifacts = craneLib.buildDepsOnly commonArgs;

          # Build the crate
          rustledger = craneLib.buildPackage (commonArgs // {
            inherit cargoArtifacts;
          });

          # Python with beancount for compatibility testing
          pythonWithBeancount = pkgs.python311.withPackages (ps: with ps; [
            beancount
            pytest
          ]);

          # Development tools
          devTools = with pkgs; [
            # Rust tools (installed via cargo)
            cargo-watch
            cargo-edit
            cargo-expand
            cargo-outdated
            cargo-audit
            cargo-deny
            cargo-nextest
            cargo-llvm-cov
            cargo-mutants
            cargo-machete
            cargo-bloat
            cargo-udeps
            bacon

            # WASM tools
            wasm-pack
            wasm-bindgen-cli
            wasmtime
            binaryen # wasm-opt

            # TLA+ tools
            tlaplus
            tlaplusToolbox

            # General dev tools
            just
            jq
            fd
            ripgrep
            hyperfine # Benchmarking
            tokei # Code stats
            git-cliff # Changelog generation

            # Documentation
            mdbook

            # LSP and editor support
            rust-analyzer

            # Nix tools
            nil # Nix LSP
            nixpkgs-fmt
            nix-tree
            nvd

            # Python for compat testing
            pythonWithBeancount
          ];

        in
        {
          # Formatters
          treefmt = {
            projectRootFile = "flake.nix";
            programs = {
              # Nix
              nixpkgs-fmt.enable = true;

              # Rust
              rustfmt = {
                enable = true;
                package = rustToolchain;
              };

              # TOML
              taplo.enable = true;

              # Markdown
              mdformat.enable = true;

              # Shell
              shfmt.enable = true;

              # YAML
              yamlfmt.enable = true;
            };
          };

          # Pre-commit hooks
          pre-commit = {
            check.enable = true;
            settings.hooks = {
              # Formatting
              treefmt.enable = true;

              # Rust
              clippy = {
                enable = true;
                packageOverrides.cargo = rustToolchainWithWasm;
                packageOverrides.clippy = rustToolchainWithWasm;
              };

              # Nix
              nil.enable = true;

              # Secrets detection
              detect-private-keys.enable = true;

              # Commit message
              commitizen.enable = true;
            };
          };

          # Packages
          packages = {
            default = rustledger;
            rustledger = rustledger;

            # Documentation
            doc = craneLib.cargoDoc (commonArgs // {
              inherit cargoArtifacts;
            });

            # WASM build
            wasm = craneLib.buildPackage (commonArgs // {
              inherit cargoArtifacts;
              cargoExtraArgs = "--target wasm32-unknown-unknown -p rustledger-wasm";
              CARGO_BUILD_TARGET = "wasm32-unknown-unknown";
            });
          };

          # Checks
          checks = {
            inherit rustledger;

            # Clippy
            clippy = craneLib.cargoClippy (commonArgs // {
              inherit cargoArtifacts;
              cargoClippyExtraArgs = "--all-targets -- --deny warnings";
            });

            # Tests
            test = craneLib.cargoTest (commonArgs // {
              inherit cargoArtifacts;
            });

            # Formatting
            fmt = craneLib.cargoFmt {
              src = ./.;
            };

            # Audit
            audit = craneLib.cargoAudit {
              inherit (inputs) advisory-db;
              src = ./.;
            };

            # Deny (license + security)
            deny = craneLib.cargoDeny {
              src = ./.;
            };

            # Doc build
            doc = craneLib.cargoDoc (commonArgs // {
              inherit cargoArtifacts;
              RUSTDOCFLAGS = "-D warnings";
            });

            # Coverage
            coverage = craneLib.cargoLlvmCov (commonArgs // {
              inherit cargoArtifacts;
            });
          };

          # Development shell
          devShells.default = craneLib.devShell {
            # Inherit checks for pre-commit
            checks = self'.checks;

            # Include pre-commit hook installation
            shellHook = ''
              ${config.pre-commit.installationScript}
              echo "🦀 rustledger development environment"
              echo ""
              echo "Available commands:"
              echo "  cargo build       - Build the project"
              echo "  cargo test        - Run tests"
              echo "  cargo clippy      - Run linter"
              echo "  just              - Show available tasks"
              echo "  nix flake check   - Run all checks"
              echo "  treefmt           - Format all files"
              echo ""
              echo "Tools available:"
              echo "  - Rust: $(rustc --version)"
              echo "  - WASM: wasm32-unknown-unknown target"
              echo "  - TLA+: $(which tlc 2>/dev/null && echo 'tlc available' || echo 'tlaplus')"
              echo "  - Python: $(python --version) with beancount"
              echo ""
            '';

            packages = devTools ++ [
              rustToolchainWithWasm
              config.treefmt.build.wrapper
            ];

            # Environment variables
            RUST_BACKTRACE = "1";
            RUST_LOG = "info";

            # For rust-analyzer
            RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";
          };

          # Nightly shell for fuzzing
          devShells.nightly = pkgs.mkShell {
            packages = [
              rustNightly
              pkgs.cargo-fuzz
            ];
            shellHook = ''
              echo "🔬 Nightly shell for fuzzing"
              echo "Run: cargo +nightly fuzz run <target>"
            '';
          };
        };
    };
}
