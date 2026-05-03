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

    # Process management for dev
    process-compose-flake.url = "github:Platonic-Systems/process-compose-flake";

    # Advisory database for cargo-audit
    advisory-db = {
      url = "github:rustsec/advisory-db";
      flake = false;
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        inputs.treefmt-nix.flakeModule
        # Disabled for now - process-compose requires configuration
        # inputs.process-compose-flake.flakeModule
      ];

      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem =
        { config
        , self'
        , inputs'
        , pkgs
        , system
        , lib
        , ...
        }:
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

          # WASM target (for wasm-bindgen/browser)
          rustWasm = inputs'.fenix.packages.targets.wasm32-unknown-unknown.stable.rust-std;

          # WASI target (for wasmtime/Python)
          rustWasi = inputs'.fenix.packages.targets.wasm32-wasip1.stable.rust-std;

          # Combined toolchain with WASM + WASI
          rustToolchainWithWasm = inputs'.fenix.packages.combine [
            rustToolchain
            rustWasm
            rustWasi
          ];

          # Crane lib with our toolchain
          craneLib = (inputs.crane.mkLib pkgs).overrideToolchain rustToolchainWithWasm;

          # Source filter that includes test fixtures (.beancount files and test data)
          # Note: The regex must match both the directory and its contents for Nix to traverse into it
          srcFilter = path: type:
            (craneLib.filterCargoSources path type) ||
            (builtins.match ".*\\.beancount$" path != null) ||
            (builtins.match ".*\\.snap$" path != null) ||
            (builtins.match ".*/tests/fixtures(/.*)?$" path != null) ||
            (builtins.match ".*/tests/snapshots(/.*)?$" path != null);

          src = lib.cleanSourceWith {
            src = ./.;
            filter = srcFilter;
          };

          # Common arguments for crane builds
          # Note: On Darwin, the SDK and frameworks (Security, SystemConfiguration, etc.)
          # are now included automatically via stdenv in nixpkgs 25.05+.
          # libiconv is also propagated by the SDK. We keep minimal Darwin deps for
          # backward compatibility with older nixpkgs versions.
          commonArgs = {
            inherit src;
            strictDeps = true;

            buildInputs = [
              # Add platform-specific deps here
            ]
            # Only add legacy Darwin deps on older nixpkgs without apple-sdk.
            # Modern nixpkgs (25.05+): SDK frameworks are in stdenv automatically,
            # and libiconv is propagated by the SDK.
            ++ lib.optionals (pkgs.stdenv.isDarwin && !(pkgs ? apple-sdk)) [
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
          rustledger = craneLib.buildPackage (
            commonArgs
            // {
              inherit cargoArtifacts;
              meta.mainProgram = "rledger";
            }
          );

          # beanprice isn't packaged in nixpkgs (it's a separate PyPI distribution
          # since beancount v3). Build it locally so we can run differential tests
          # of `rledger price` against `bean-price` from CI / dev shells.
          beanprice = pkgs.python312Packages.buildPythonApplication {
            pname = "beanprice";
            version = "2.1.0";
            pyproject = true;

            src = pkgs.python312Packages.fetchPypi {
              pname = "beanprice";
              version = "2.1.0";
              hash = "sha256-2Q0mZB97rthEPN/bVUXDj40B+XYE7UrUFzsCNZiYKxM=";
            };

            build-system = with pkgs.python312Packages; [ setuptools ];

            dependencies = with pkgs.python312Packages; [
              beancount
              python-dateutil
              requests
              curl-cffi
              diskcache
            ];

            # Network-bound tests; skip in the build sandbox.
            doCheck = false;
          };

          # Python with beancount for compatibility testing
          pythonWithBeancount = pkgs.python312.withPackages (
            ps: with ps; [
              beancount
              beanquery # For bean-query CLI (BQL)
              pytest
            ]
          );

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

            # Git hooks
            prek
            gitleaks
            typos
            commitizen

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
            uv # Python package manager for compat testing
            tmux
            gh

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
            beanprice # `bean-price` CLI for differential price tests
          ];

        in
        {
          # Acknowledge the upstream x86_64-darwin deprecation (Nixpkgs 26.11+).
          # Silences the evaluation warning while we continue to ship Intel macOS
          # binaries; revisit when Nixpkgs fully drops the platform.
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            config.allowDeprecatedx86_64Darwin = true;
          };

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

          # Packages
          packages = {
            default = rustledger;
            rustledger = rustledger;

            # Documentation
            doc = craneLib.cargoDoc (
              commonArgs
              // {
                inherit cargoArtifacts;
              }
            );

            # WASM build
            wasm = craneLib.buildPackage (
              commonArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--target wasm32-unknown-unknown -p rustledger-wasm";
                CARGO_BUILD_TARGET = "wasm32-unknown-unknown";
              }
            );
          };

          # Checks
          checks = {
            inherit rustledger;

            # Clippy
            clippy = craneLib.cargoClippy (
              commonArgs
              // {
                inherit cargoArtifacts;
                cargoClippyExtraArgs = "--all-targets -- --deny warnings";
              }
            );

            # Tests
            test = craneLib.cargoTest (
              commonArgs
              // {
                inherit cargoArtifacts;
              }
            );

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
            doc = craneLib.cargoDoc (
              commonArgs
              // {
                inherit cargoArtifacts;
                RUSTDOCFLAGS = "-D warnings";
              }
            );

            # Coverage
            coverage = craneLib.cargoLlvmCov (
              commonArgs
              // {
                inherit cargoArtifacts;
              }
            );
          };

          # Development shell
          devShells.default = craneLib.devShell {
            # Inherit checks
            checks = self'.checks;

            # Shell initialization
            shellHook = ''
              # Source agent-env when present (for example, to load API keys and claude PATH)
              [[ -f ~/.agent-env ]] && source ~/.agent-env

              # Install prek hooks if not already installed
              if command -v prek &> /dev/null && [ -f .pre-commit-config.yaml ]; then
                prek install --hook-type pre-commit --hook-type pre-push --hook-type commit-msg 2>/dev/null || true
              fi

              echo "🦀 rustledger development environment"
              echo ""
              echo "Available commands:"
              echo "  cargo build        - Build the project"
              echo "  cargo test         - Run tests"
              echo "  cargo clippy       - Run linter"
              echo "  just               - Show available tasks"
              echo "  nix flake check    - Run all checks"
              echo "  treefmt            - Format all files"
              echo "  opencode-container - Run opencode in container"
              echo ""
              echo "Tools available:"
              echo "  - Rust: $(rustc --version)"
              echo "  - WASM: wasm32-unknown-unknown target (wasm-bindgen)"
              echo "  - WASI: wasm32-wasip1 target (wasmtime)"
              echo "  - TLA+: $(if command -v tlc >/dev/null; then tlc -help 2>&1 | grep -i version | head -1 | sed 's/^[[:space:]]*//'; else echo 'not available'; fi)"
              echo "  - Python: $(python --version) with beancount + beanprice (bean-price CLI)"
              echo "  - Podman: $(podman --version)"
              echo ""

              # OpenCode container alias (requires sops-nix secrets)
              # Uses overlayfs to combine container's nix store with host's store
              # Writes go to ephemeral tmpfs (secure - no persistence between runs)
              if [[ -f /run/secrets/api/together-ai && \
                    -f /run/secrets/user/email && \
                    -f /run/secrets/user/realName ]]; then
                alias opencode-container='podman run \
                    -v $(pwd):/data:Z \
                    -v ~/.opencode:/home/nixuser/.opencode \
                    -v /nix/store:/host-nix-store:ro \
                    --cap-add=SYS_ADMIN \
                    --userns=keep-id \
                    --rm -ti \
                    -w /data \
                    -e TOGETHER_API_KEY="$(cat /run/secrets/api/together-ai)" \
                    -e GIT_AUTHOR_NAME="$(cat /run/secrets/user/realName)" \
                    -e GIT_AUTHOR_EMAIL="$(cat /run/secrets/user/email)" \
                    -e GIT_COMMITTER_NAME="$(cat /run/secrets/user/realName)" \
                    -e GIT_COMMITTER_EMAIL="$(cat /run/secrets/user/email)" \
                    ghcr.io/grigio/docker-nixuser:latest \
                    sh -c "mkdir -p /tmp/nix-upper /tmp/nix-work && mount -t overlay overlay -o lowerdir=/nix/store:/host-nix-store,upperdir=/tmp/nix-upper,workdir=/tmp/nix-work /nix/store && opencode"'
              else
                alias opencode-container='echo "Missing sops-nix secrets. Required: api/together-ai, user/email, user/realName"'
              fi
            '';

            packages = devTools ++ [
              rustToolchainWithWasm
              config.treefmt.build.wrapper
              pkgs.podman
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
