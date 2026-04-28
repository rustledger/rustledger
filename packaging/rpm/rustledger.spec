%global debug_package %{nil}

Name:           rustledger
Version:        0.14.1
Release:        1%{?dist}
Summary:        Fast, pure Rust implementation of Beancount double-entry accounting

License:        GPL-3.0-only
URL:            https://rustledger.github.io
Source0:        https://github.com/rustledger/rustledger/archive/refs/tags/v0.14.1.tar.gz

# Must match `workspace.package.rust-version` in Cargo.toml.
# Edition 2024 stabilized in 1.85, so older toolchains fail at parse
# time regardless of MSRV.
BuildRequires:  rust >= 1.94
BuildRequires:  cargo
BuildRequires:  gcc

ExclusiveArch:  x86_64 aarch64

%description
rustledger is a fast, pure Rust implementation of Beancount, the double-entry
bookkeeping language. It provides a 10-30x faster alternative to Python beancount
with full syntax compatibility.

%prep
%setup -q -n rustledger-0.14.1

%build
cargo build --release

%install
install -d %{buildroot}%{_bindir}

# Main unified binary + LSP server.
# Bean-* compatibility wrappers were removed as compiled binaries; users
# opt in post-install via `rledger compat install --prefix /usr/bin`.
install -m 755 target/release/rledger %{buildroot}%{_bindir}/
install -m 755 target/release/rledger-lsp %{buildroot}%{_bindir}/

%files
%license LICENSE
%{_bindir}/rledger
%{_bindir}/rledger-lsp

%changelog
* Sat Jan 25 2026 rustledger <rustledger@users.noreply.github.com> - 0.7.3-1
- Update to version 0.7.3
- Add CI automation for version sync

* Tue Jan 14 2026 rustledger <rustledger@users.noreply.github.com> - 0.1.0-1
- Switch to semver 0.x.y versioning
