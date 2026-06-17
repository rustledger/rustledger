"""Spike (#173): drive the guest-exported `resource session` from wasmtime-py.

Proves the Component-Model resource lifecycle end-to-end: construct via the
WIT `constructor`, call methods (passing the ResourceAny handle as `&self`),
and confirm load-once state is held server-side (entry-count + query with no
re-parse on the host side).
"""

from __future__ import annotations

import sys

from wasmtime import Engine, Store, WasiConfig
from wasmtime.component import Component, Linker

# Reuse rustfava's type-driven marshaller to read the query-result record.
sys.path.insert(0, "/home/dev/rustfava/src")
from rustfava.rustledger.component_engine import _marshal  # noqa: E402

WASM = (
    "/home/dev/rustledger-spike-ledger-resource/target/"
    "wasm32-wasip2/release/rustledger_ffi_component.wasm"
)
IFACE = "rustledger:ledger/ledger@2.1.0"

SRC = (
    "2024-01-01 open Assets:Cash USD\n"
    "2024-01-01 open Expenses:Food USD\n"
    '2024-01-02 * "Coffee"\n'
    "  Expenses:Food  5 USD\n"
    "  Assets:Cash\n"
    '2024-03-01 * "Lunch"\n'
    "  Expenses:Food  9 USD\n"
    "  Assets:Cash\n"
)

engine = Engine()
component = Component.from_file(engine, WASM)
store = Store(engine)
wasi = WasiConfig()
wasi.inherit_stdout()
wasi.inherit_stderr()
store.set_wasi(wasi)
linker = Linker(engine)
linker.add_wasip2()
inst = linker.instantiate(store, component)

iface = component.get_export_index(IFACE)


def func(name: str):
    idx = component.get_export_index(name, iface)
    assert idx is not None, f"export not found: {name}"
    f = inst.get_func(store, idx)
    assert f is not None, f"func not found: {name}"
    return f


ctor = func("[constructor]session")
m_count = func("[method]session.entry-count")
m_query = func("[method]session.query")

# 1) construct the resource (parses + books once, server-side)
handle = ctor(store, SRC)
print("constructed session handle:", type(handle).__name__)

# 2) call a method on the held ledger
count = m_count(store, handle)
print("entry-count:", count)
assert count == 4, f"expected 4 directives, got {count}"

# 3) query the held ledger (no re-parse on the host side)
raw = m_query(store, handle, "SELECT account, position")
result = _marshal(raw, m_query.type(store).result)
print("query columns:", [c["name"] for c in result["columns"]])
print("query rows:", len(result["rows"]))
assert result["columns"][0]["name"] == "account"
assert len(result["rows"]) >= 1

print("\nSPIKE OK: resource lifecycle (constructor + methods + state) works.")
