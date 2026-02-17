%global debug_package %{nil}

Name:           rustledger
Version:        0.9.0
Release:        1%{?dist}
Summary:        Fast, pure Rust implementation of Beancount double-entry accounting

License:        GPL-3.0-only
URL:            https://rustledger.github.io
Source0:        https://github.com/rustledger/rustledger/archive/refs/tags/v0.9.0.tar.gz

BuildRequires:  rust >= 1.75
BuildRequires:  cargo
BuildRequires:  gcc

ExclusiveArch:  x86_64 aarch64

%description
rustledger is a fast, pure Rust implementation of Beancount, the double-entry
bookkeeping language. It provides a 10-30x faster alternative to Python beancount
with full syntax compatibility.

%prep
%setup -q -n rustledger-0.9.0

%build
cargo build --release

%install
install -d %{buildroot}%{_bindir}

# Main unified binary
install -m 755 target/release/rledger %{buildroot}%{_bindir}/

# Bean-* compatibility binaries
install -m 755 target/release/bean-check %{buildroot}%{_bindir}/
install -m 755 target/release/bean-format %{buildroot}%{_bindir}/
install -m 755 target/release/bean-query %{buildroot}%{_bindir}/
install -m 755 target/release/bean-report %{buildroot}%{_bindir}/
install -m 755 target/release/bean-doctor %{buildroot}%{_bindir}/
install -m 755 target/release/bean-extract %{buildroot}%{_bindir}/
install -m 755 target/release/bean-price %{buildroot}%{_bindir}/

%files
%license LICENSE
%{_bindir}/rledger
%{_bindir}/bean-*

%changelog
* Sat Jan 25 2026 rustledger <rustledger@users.noreply.github.com> - 0.7.3-1
- Update to version 0.7.3
- Add CI automation for version sync

* Tue Jan 14 2026 rustledger <rustledger@users.noreply.github.com> - 0.1.0-1
- Switch to semver 0.x.y versioning
