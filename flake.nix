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
            beanquery  # For bean-query CLI (BQL)
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
              # Rust formatting - matches CI (cargo fmt --all -- --check)
              # Using cargo fmt instead of treefmt because treefmt requires
              # additional formatters (shfmt, yamlfmt, mdformat) that may not
              # be available outside the nix shell
              rustfmt = {
                enable = true;
                entry = lib.mkForce "cargo fmt --all --";
              };

              # Rust linting - always run on every commit to catch all warnings
              clippy = {
                enable = true;
                packageOverrides.cargo = rustToolchainWithWasm;
                packageOverrides.clippy = rustToolchainWithWasm;
                settings = {
                  allFeatures = true;
                  denyWarnings = true;
                  extraArgs = "--all-targets";
                };
                # Always run clippy, not just when .rs files are staged
                # This catches warnings in unchanged files (e.g., from new clippy lints)
                always_run = true;
              };

              # Nix
              nil.enable = true;

              # Secrets detection (defense in depth)
              detect-private-keys.enable = true;

              # Comprehensive secret scanning with gitleaks
              # Uses --staged to only scan staged changes (fast)
              gitleaks = {
                enable = true;
                name = "gitleaks";
                entry = "${pkgs.gitleaks}/bin/gitleaks protect --staged --redact --config .gitleaks.toml";
                language = "system";
                pass_filenames = false;
              };

              # Commit message
              commitizen.enable = true;

              # Branch name validation (runs on pre-push)
              branch-name = {
                enable = true;
                name = "branch-name";
                entry = "${pkgs.writeShellScript "check-branch-name" ''
                  BRANCH=$(git rev-parse --abbrev-ref HEAD)

                  # Skip for main branch
                  if [ "$BRANCH" = "main" ] || [ "$BRANCH" = "HEAD" ]; then
                    exit 0
                  fi

                  # Allow release-plz branches (e.g., release-plz-2026-01-18T17-10-14Z)
                  if [[ "$BRANCH" =~ ^release-plz- ]]; then
                    echo "✅ Branch name '$BRANCH' is valid (release-plz)"
                    exit 0
                  fi

                  PATTERN="^(feature|fix|docs|chore|refactor|release|hotfix|claude|dependabot|copilot)/[a-zA-Z0-9][a-zA-Z0-9/_-]*$"

                  if [[ "$BRANCH" =~ $PATTERN ]]; then
                    echo "✅ Branch name '$BRANCH' is valid"
                    exit 0
                  else
                    echo "❌ Branch name '$BRANCH' does not match pattern"
                    echo ""
                    echo "Branch names must follow: <type>/<description>"
                    echo "  Types: feature, fix, docs, chore, refactor, release, hotfix, claude, dependabot, copilot"
                    echo "  Description: letters, numbers, hyphens, underscores, slashes"
                    echo ""
                    echo "Examples:"
                    echo "  feature/add-csv-export"
                    echo "  fix/balance-calculation"
                    echo "  claude/repo-improvements"
                    echo ""
                    echo "Note: 'feat/' is NOT valid, use 'feature/' instead"
                    exit 1
                  fi
                ''}";
                language = "system";
                stages = [ "pre-push" ];
                pass_filenames = false;
                always_run = true;
              };

              # Run tests before push to catch failures before CI
              cargo-test = {
                enable = true;
                name = "cargo-test";
                entry = "${pkgs.writeShellScript "cargo-test" ''
                  echo "Running cargo test (library tests only for speed)..."
                  cargo test --workspace --lib --quiet
                ''}";
                language = "system";
                stages = [ "pre-push" ];
                pass_filenames = false;
                always_run = true;
              };

              # Check documentation builds without warnings
              cargo-doc = {
                enable = true;
                name = "cargo-doc";
                entry = "${pkgs.writeShellScript "cargo-doc" ''
                  echo "Checking documentation..."
                  RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --quiet 2>&1 | head -20 || {
                    echo "Documentation has warnings. Run 'cargo doc' to see details."
                    exit 1
                  }
                ''}";
                language = "system";
                stages = [ "pre-push" ];
                pass_filenames = false;
                always_run = true;
              };
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
            RUST_MIN_STACK = "8388608"; # 8MB stack for debug builds

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

          # Benchmark shell with all comparison tools (downloads latest releases)
          devShells.bench = pkgs.mkShell {
            packages = [
              rustToolchainWithWasm
              pythonWithBeancount
              pkgs.hyperfine # Use nixpkgs (already latest)
              pkgs.jq
              pkgs.curl
              pkgs.gnutar
              pkgs.gzip
              # Build dependencies for ledger
              pkgs.cmake
              pkgs.boost
              pkgs.gmp
              pkgs.mpfr
              pkgs.libedit
              pkgs.gnumake
              pkgs.gcc
            ];
            shellHook = ''
              # Download latest releases to .bench-tools
              BENCH_TOOLS="$PWD/.bench-tools"
              mkdir -p "$BENCH_TOOLS/bin"
              export PATH="$BENCH_TOOLS/bin:$PATH"

              # Only download if not already present or older than 1 day
              if [ ! -f "$BENCH_TOOLS/.last-update" ] || [ $(find "$BENCH_TOOLS/.last-update" -mtime +1 2>/dev/null) ]; then
                echo "📥 Downloading latest benchmark tools..."

                # hledger (pre-built binary)
                HLEDGER_VERSION=$(curl -s https://api.github.com/repos/simonmichael/hledger/releases/latest | jq -r '.tag_name')
                echo "  hledger $HLEDGER_VERSION"
                curl -sL "https://github.com/simonmichael/hledger/releases/latest/download/hledger-linux-x64.tar.gz" | tar xz -C "$BENCH_TOOLS/bin/"

                # ledger (build from source)
                LEDGER_VERSION=$(curl -s https://api.github.com/repos/ledger/ledger/releases/latest | jq -r '.tag_name')
                echo "  ledger $LEDGER_VERSION (building from source...)"
                curl -sL "https://github.com/ledger/ledger/archive/refs/tags/$LEDGER_VERSION.tar.gz" | tar xz -C /tmp
                cd "/tmp/ledger-''${LEDGER_VERSION#v}"
                cmake -B build -DCMAKE_BUILD_TYPE=Release -DBUILD_DOCS=OFF -DBUILD_WEB_DOCS=OFF -DCMAKE_INSTALL_PREFIX="$BENCH_TOOLS" >/dev/null 2>&1
                cmake --build build --parallel $(nproc) >/dev/null 2>&1
                cp build/ledger "$BENCH_TOOLS/bin/"
                cd - >/dev/null

                touch "$BENCH_TOOLS/.last-update"
                echo ""
              fi

              echo "📊 Benchmark environment"
              echo ""
              echo "Tools available:"
              echo "  - rustledger: cargo build --release -p rustledger"
              echo "  - beancount:  $(bean-check --version 2>&1 | head -1)"
              echo "  - ledger:     $(ledger --version 2>/dev/null | head -1 || echo 'not built yet')"
              echo "  - hledger:    $(hledger --version 2>/dev/null || echo 'not downloaded yet')"
              echo "  - hyperfine:  $(hyperfine --version)"
              echo ""
              echo "Quick benchmark:"
              echo "  ./scripts/bench.sh"
              echo ""
            '';
          };
        };
    };
}
