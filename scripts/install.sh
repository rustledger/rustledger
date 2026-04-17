#!/usr/bin/env bash
# rustledger installer
# Usage: curl -sSf https://rustledger.github.io/install.sh | bash
#
# Options:
#   --help              Show this help message
#   --version VERSION   Install a specific version (default: latest)
#   --install-dir DIR   Install to a specific directory
#
# Environment variables:
#   RUSTLEDGER_VERSION  - Version to install (default: latest)
#   RUSTLEDGER_INSTALL  - Installation directory (default: ~/.local/bin or /usr/local/bin)

set -e

REPO="rustledger/rustledger"
BINARY_NAME="rustledger"

# Colors (disabled if not a terminal)
if [ -t 1 ]; then
  RED='\033[0;31m'
  GREEN='\033[0;32m'
  YELLOW='\033[0;33m'
  BLUE='\033[0;34m'
  BOLD='\033[1m'
  NC='\033[0m'
else
  RED=''
  GREEN=''
  YELLOW=''
  BLUE=''
  BOLD=''
  NC=''
fi

info() {
  printf "${BLUE}info:${NC} %s\n" "$1"
}

success() {
  printf "${GREEN}success:${NC} %s\n" "$1"
}

warn() {
  printf "${YELLOW}warning:${NC} %s\n" "$1"
}

error() {
  printf "${RED}error:${NC} %s\n" "$1" >&2
  exit 1
}

show_help() {
  printf "rustledger installer\n\n"
  printf "Usage: curl -sSf https://rustledger.github.io/install.sh | bash\n\n"
  printf "Options:\n"
  printf "  --help              Show this help message\n"
  printf "  --version VERSION   Install a specific version (default: latest)\n"
  printf "  --install-dir DIR   Install to a specific directory\n\n"
  printf "Environment variables:\n"
  printf "  RUSTLEDGER_VERSION  - Version to install (default: latest)\n"
  printf "  RUSTLEDGER_INSTALL  - Installation directory\n"
  exit 0
}

# Detect OS
detect_os() {
  case "$(uname -s)" in
  Linux*) echo "linux" ;;
  Darwin*) echo "macos" ;;
  MINGW* | MSYS* | CYGWIN*) echo "windows" ;;
  *) error "Unsupported operating system: $(uname -s)" ;;
  esac
}

# Detect architecture
detect_arch() {
  case "$(uname -m)" in
  x86_64 | amd64) echo "x86_64" ;;
  aarch64 | arm64) echo "aarch64" ;;
  *) error "Unsupported architecture: $(uname -m)" ;;
  esac
}

# Detect if using musl libc (Alpine, etc.)
detect_musl() {
  if [ -f /etc/alpine-release ]; then
    return 0
  fi
  if ldd --version 2>&1 | grep -q musl; then
    return 0
  fi
  return 1
}

# Get the target triple
get_target() {
  local os="$1"
  local arch="$2"

  case "$os" in
  linux)
    if detect_musl; then
      case "$arch" in
      x86_64) echo "x86_64-unknown-linux-musl" ;;
      aarch64) echo "aarch64-unknown-linux-musl" ;;
      esac
    else
      case "$arch" in
      x86_64) echo "x86_64-unknown-linux-gnu" ;;
      aarch64) echo "aarch64-unknown-linux-gnu" ;;
      esac
    fi
    ;;
  macos)
    case "$arch" in
    x86_64) echo "x86_64-apple-darwin" ;;
    aarch64) echo "aarch64-apple-darwin" ;;
    esac
    ;;
  windows)
    case "$arch" in
    x86_64) echo "x86_64-pc-windows-msvc" ;;
    aarch64) echo "aarch64-pc-windows-msvc" ;;
    esac
    ;;
  esac
}

# Get latest version from GitHub
get_latest_version() {
  local url="https://api.github.com/repos/${REPO}/releases/latest"

  if command -v curl >/dev/null 2>&1; then
    curl -sSf "$url" | grep '"tag_name":' | sed -E 's/.*"([^"]+)".*/\1/'
  elif command -v wget >/dev/null 2>&1; then
    wget -qO- "$url" | grep '"tag_name":' | sed -E 's/.*"([^"]+)".*/\1/'
  else
    error "Neither curl nor wget found. Please install one of them."
  fi
}

# Download file
download() {
  local url="$1"
  local output="$2"

  if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$url" -o "$output"
  elif command -v wget >/dev/null 2>&1; then
    wget -q "$url" -O "$output"
  else
    error "Neither curl nor wget found. Please install one of them."
  fi
}

# Verify checksum
verify_checksum() {
  local archive="$1"
  local checksum_url="$2"
  local tmpdir="$3"

  local checksum_file="$tmpdir/checksums.sha256"
  if download "$checksum_url" "$checksum_file" 2>/dev/null; then
    local expected
    expected=$(grep "$(basename "$archive")" "$checksum_file" | awk '{print $1}')
    if [ -n "$expected" ]; then
      local actual
      if command -v sha256sum >/dev/null 2>&1; then
        actual=$(sha256sum "$archive" | awk '{print $1}')
      elif command -v shasum >/dev/null 2>&1; then
        actual=$(shasum -a 256 "$archive" | awk '{print $1}')
      else
        warn "No sha256sum or shasum found, skipping checksum verification"
        return 0
      fi
      if [ "$expected" = "$actual" ]; then
        info "Checksum verified"
        return 0
      else
        error "Checksum mismatch! Expected: $expected, Got: $actual"
      fi
    fi
  fi
  warn "Could not verify checksum (no .sha256 file found), proceeding anyway"
}

# Determine install directory
get_install_dir() {
  if [ -n "$RUSTLEDGER_INSTALL" ]; then
    echo "$RUSTLEDGER_INSTALL"
  elif [ -w "/usr/local/bin" ]; then
    echo "/usr/local/bin"
  else
    echo "$HOME/.local/bin"
  fi
}

# Main installation
main() {
  # Parse arguments
  while [ $# -gt 0 ]; do
    case "$1" in
    --help | -h) show_help ;;
    --version)
      RUSTLEDGER_VERSION="$2"
      shift 2
      ;;
    --install-dir)
      RUSTLEDGER_INSTALL="$2"
      shift 2
      ;;
    *)
      error "Unknown option: $1. Use --help for usage."
      ;;
    esac
  done

  printf "\n${BOLD}rustledger installer${NC}\n\n"

  # Detect platform
  local os
  os=$(detect_os)
  local arch
  arch=$(detect_arch)
  local target
  target=$(get_target "$os" "$arch")

  info "Detected platform: $os ($arch)"
  info "Target: $target"

  # Get version
  local version="${RUSTLEDGER_VERSION:-}"
  if [ -z "$version" ]; then
    info "Fetching latest version..."
    version=$(get_latest_version)
    if [ -z "$version" ]; then
      error "Could not determine latest version. Set RUSTLEDGER_VERSION manually."
    fi
  fi
  info "Version: $version"

  # Determine file extension and check extraction tools
  local ext="tar.gz"
  if [ "$os" = "windows" ]; then
    ext="zip"
    if ! command -v unzip >/dev/null 2>&1; then
      error "unzip is required but not found. Please install it."
    fi
  else
    if ! command -v tar >/dev/null 2>&1; then
      error "tar is required but not found. Please install it."
    fi
  fi

  # Build download URL
  local filename="${BINARY_NAME}-${version}-${target}.${ext}"
  local url="https://github.com/${REPO}/releases/download/${version}/${filename}"

  info "Downloading from: $url"

  # Create temp directory
  local tmpdir
  tmpdir=$(mktemp -d)
  trap "rm -rf '$tmpdir'" EXIT

  local archive="$tmpdir/$filename"

  # Download
  if ! download "$url" "$archive"; then
    error "Download failed. Check that the release exists at:\n  $url"
  fi

  # Verify checksum
  local checksum_url="https://github.com/${REPO}/releases/download/${version}/${filename}.sha256"
  verify_checksum "$archive" "$checksum_url" "$tmpdir"

  # Extract
  info "Extracting..."
  cd "$tmpdir"
  if [ "$ext" = "tar.gz" ]; then
    tar -xzf "$archive"
  else
    unzip -q "$archive"
  fi

  # Find the rledger binary specifically
  local binary=""
  if [ "$os" = "windows" ]; then
    binary=$(find . -name "rledger.exe" -type f | head -1)
  else
    binary=$(find . -name "rledger" -type f | head -1)
  fi

  if [ -z "$binary" ]; then
    error "Could not find rledger binary in archive"
  fi

  # Install
  local install_dir
  install_dir=$(get_install_dir)
  info "Installing to: $install_dir"

  # Create directory if needed
  mkdir -p "$install_dir"

  # Copy all binaries (rledger unified binary and bean-* compatibility variants)
  for bin in rledger \
    bean-check bean-format bean-query bean-report bean-doctor bean-extract bean-price; do
    if [ -f "$tmpdir/$bin" ] || [ -f "$tmpdir/${bin}.exe" ]; then
      if [ "$os" = "windows" ]; then
        cp "$tmpdir/${bin}.exe" "$install_dir/"
      else
        cp "$tmpdir/$bin" "$install_dir/"
        chmod +x "$install_dir/$bin"
      fi
    fi
  done

  printf "\n"
  success "rustledger $version installed successfully!"

  # Check if install dir is in PATH
  case ":$PATH:" in
  *":$install_dir:"*) ;;
  *)
    printf "\n"
    warn "Add $install_dir to your PATH:"
    printf "\n"
    printf "    export PATH=\"%s:\$PATH\"\n" "$install_dir"
    printf "\n"
    printf "  Add this line to your ~/.bashrc, ~/.zshrc, or equivalent.\n"
    ;;
  esac

  printf "\n"
  info "Get started:"
  printf "    rledger check ledger.beancount\n"
  printf "    rledger query ledger.beancount\n"
  printf "\n"
  info "Python beancount compatibility aliases also available:"
  printf "    bean-check, bean-format, bean-query, bean-report, bean-doctor\n"
  printf "\n"
}

main "$@"
