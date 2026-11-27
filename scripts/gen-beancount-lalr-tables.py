#!/usr/bin/env python3
"""Generate the beancount LALR tables rustledger-parser's error oracle replays.

The grammar is pta-standards' clean-room, MIT-licensed
`formats/beancount/v3/grammar/beancount.y`, vendored at a pinned revision as
`crates/rustledger-parser/grammar/beancount.y` (its SHA-256 is pinned below,
so an edit that did not come from pta-standards fails this script). bison
3.8.2 compiles it with the `yacc.c` skeleton, and this script copies the
parse tables out of the generated C into
`crates/rustledger-parser/src/cst/oracle/beancount/tables.rs`.

bison's skeleton output carries the bison exception (GPL-3.0-or-later with
the special exception that lets the generated parser be embedded under any
license), and the tables are data generated from the MIT grammar, so they are
fine to check in.

bison is the flake-pinned one (nixpkgs' 3.8.2); the script refuses any other
version, since another bison may number states differently and the checked-in
file would churn for no reason:

    nix shell --inputs-from . nixpkgs#bison -c python3 scripts/gen-beancount-lalr-tables.py
    nix shell --inputs-from . nixpkgs#bison -c python3 scripts/gen-beancount-lalr-tables.py --check

`--check` regenerates into memory and fails if the checked-in file differs
(CI runs it). `--vendor PTA_STANDARDS_CHECKOUT` re-copies `beancount.y` from
a pta-standards checkout at `PTA_STANDARDS_REV`; bump the revision and the
hash together when pta-standards changes the grammar.
"""

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GRAMMAR = REPO / "crates/rustledger-parser/grammar/beancount.y"
OUTPUT = REPO / "crates/rustledger-parser/src/cst/oracle/beancount/tables.rs"
PTA_STANDARDS_REV = "1463db773ac55f87d2e56877eda5bd68d9939ff0"
PTA_STANDARDS_PATH = "formats/beancount/v3/grammar/beancount.y"
GRAMMAR_SHA256 = "d86da4ef1d6bda3f0d3b9f72385ee58ebafdb0c28f5b7a4972cf7da5e538694a"
BISON_VERSION = "3.8.2"

ARRAYS = ("yypact", "yydefact", "yypgoto", "yydefgoto", "yytable", "yycheck", "yyr1", "yyr2")
DEFINES = (
    "YYFINAL",
    "YYLAST",
    "YYNTOKENS",
    "YYNNTS",
    "YYNRULES",
    "YYNSTATES",
    "YYPACT_NINF",
    "YYTABLE_NINF",
)
# yytname's special entries, renamed to Rust identifiers.
SPECIAL_NAMES = {"end of file": "Eof", "error": "Error", "invalid token": "Undef"}


def fail(message):
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


def bison_binary():
    bison = os.environ.get("BISON") or shutil.which("bison")
    if not bison:
        fail("bison not found; run under `nix shell --inputs-from . nixpkgs#bison`")
    out = subprocess.run([bison, "--version"], capture_output=True, text=True, check=True)
    first = out.stdout.splitlines()[0] if out.stdout else ""
    if not first.endswith(" " + BISON_VERSION):
        fail(f"need bison {BISON_VERSION}, found `{first}`")
    return bison


def unquote(name):
    # yytname entries for aliased tokens hold a quoted C string.
    name = name.encode().decode("unicode_escape")
    if len(name) >= 2 and name[0] == '"' and name[-1] == '"':
        return name[1:-1]
    return name


def parse_c(source):
    arrays = {}
    for a in ARRAYS:
        m = re.search(r"static const \w+ " + a + r"\[\] =\s*\{([^}]*)\}", source)
        if not m:
            fail(f"table {a} not found in bison output")
        arrays[a] = [int(x) for x in m.group(1).replace("\n", " ").split(",") if x.strip()]
    defines = {}
    for d in DEFINES:
        m = re.search(r"#define " + d + r"\s+\(?(-?\d+)\)?", source)
        if not m:
            fail(f"define {d} not found in bison output")
        defines[d] = int(m.group(1))
    m = re.search(r"static const char \*const yytname\[\] =\s*\{(.*?)YY_NULLPTR", source, re.S)
    if not m:
        fail("yytname not found (the grammar must use `%define parse.error verbose`)")
    names = [unquote(x) for x in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))]
    m = re.search(r"#define yytable_value_is_error\(Yyn\)\s*\\\s*(.*)", source)
    table_ninf_is_error = bool(m and "YYTABLE_NINF" in m.group(1))
    return arrays, defines, names, table_ninf_is_error


def ident(name):
    if name in SPECIAL_NAMES:
        return SPECIAL_NAMES[name]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        fail(f"symbol name {name!r} is not an identifier")
    return "".join(part.capitalize() for part in name.lower().split("_"))


def rust_array(name, ty, values):
    lo, hi = {"i16": (-(2**15), 2**15 - 1), "u8": (0, 255)}[ty]
    for v in values:
        if not lo <= v <= hi:
            fail(f"{name}: value {v} does not fit {ty}")
    body = []
    line = "   "
    for v in values:
        piece = f" {v},"
        if len(line) + len(piece) > 99:
            body.append(line)
            line = "   "
        line += piece
    body.append(line)
    return f"pub(super) const {name}: [{ty}; {len(values)}] = [\n" + "\n".join(body) + "\n];\n"


def render(arrays, defines, names, table_ninf_is_error):
    ntokens = defines["YYNTOKENS"]
    tokens = names[:ntokens]
    nonterminals = names[ntokens:]
    out = []
    out.append(
        "// @generated by scripts/gen-beancount-lalr-tables.py -- DO NOT EDIT.\n"
        "//\n"
        "// LALR(1) tables of pta-standards' clean-room, MIT-licensed beancount grammar\n"
        f"// (`{PTA_STANDARDS_PATH}` at rustledger/pta-standards@{PTA_STANDARDS_REV[:12]},\n"
        "// vendored as `crates/rustledger-parser/grammar/beancount.y`), compiled by\n"
        f"// GNU bison {BISON_VERSION} (yacc.c skeleton). bison's skeleton output carries\n"
        "// the bison exception, so these tables may be embedded in any program.\n"
        "//\n"
        "// The arrays are bison's own, under their bison names without the `yy`\n"
        "// prefix; `super::lr` replays them with yacc.c's semantics.\n\n"
    )
    out.append("#![allow(clippy::unreadable_literal, dead_code)]\n\n")
    for d in DEFINES:
        out.append(f"pub(super) const {d}: i16 = {defines[d]};\n")
    out.append(
        "/// Whether `yytable_value_is_error` tests `YYTABLE_NINF` (bison omits the\n"
        "/// test when no table entry is an explicit error).\n"
        f"pub(super) const TABLE_NINF_IS_ERROR: bool = {'true' if table_ninf_is_error else 'false'};\n\n"
    )
    out.append(
        "/// A terminal of the grammar, numbered as bison's internal symbol numbers\n"
        "/// (`yysymbol_kind_t`), which index the tables.\n"
        "#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]\n"
        "#[repr(u8)]\n"
        "pub enum Tok {\n"
    )
    for i, n in enumerate(tokens):
        out.append(f"    /// `{n}`\n    {ident(n)} = {i},\n")
    out.append("}\n\n")
    out.append(
        "impl Tok {\n"
        "    /// The name bison prints for the token in a syntax error message.\n"
        "    #[must_use]\n"
        "    pub const fn name(self) -> &'static str {\n"
        "        SYMBOL_NAMES[self as usize]\n"
        "    }\n\n"
        "    /// The token with internal symbol number `n`, if `n` is a terminal.\n"
        "    #[must_use]\n"
        "    pub const fn from_symbol(n: usize) -> Option<Self> {\n"
        "        match n {\n"
    )
    for i, n in enumerate(tokens):
        out.append(f"            {i} => Some(Self::{ident(n)}),\n")
    out.append("            _ => None,\n        }\n    }\n}\n\n")
    out.append(
        "/// Nonterminals the oracle's reduction trace names (internal symbol numbers).\n"
    )
    for i, n in enumerate(nonterminals):
        if n in ("$accept",):
            continue
        out.append(f"pub(super) const NT_{n.upper()}: i16 = {ntokens + i};\n")
    out.append("\n/// `yytname`: every symbol's name, terminals first.\n")
    out.append(f"pub(super) const SYMBOL_NAMES: [&str; {len(names)}] = [\n")
    for n in names:
        out.append(f"    {n!r},\n".replace("'", '"'))
    out.append("];\n\n")
    out.append(rust_array("PACT", "i16", arrays["yypact"]))
    out.append(rust_array("DEFACT", "u8", arrays["yydefact"]))
    out.append(rust_array("PGOTO", "i16", arrays["yypgoto"]))
    out.append(rust_array("DEFGOTO", "u8", arrays["yydefgoto"]))
    out.append(rust_array("TABLE", "i16", arrays["yytable"]))
    out.append(rust_array("CHECK", "i16", arrays["yycheck"]))
    out.append(rust_array("R1", "u8", arrays["yyr1"]))
    out.append(rust_array("R2", "u8", arrays["yyr2"]))
    return "".join(out)


def generate():
    digest = hashlib.sha256(GRAMMAR.read_bytes()).hexdigest()
    if digest != GRAMMAR_SHA256:
        fail(
            f"{GRAMMAR.relative_to(REPO)} has sha256 {digest}, expected {GRAMMAR_SHA256}: "
            "re-vendor it with --vendor (and bump PTA_STANDARDS_REV and GRAMMAR_SHA256)"
        )
    bison = bison_binary()
    with tempfile.TemporaryDirectory() as td:
        c_out = Path(td) / "parser.c"
        res = subprocess.run(
            [bison, "-Wall", "-Werror", "-o", str(c_out), str(GRAMMAR)],
            capture_output=True,
            text=True,
        )
        if res.returncode != 0:
            fail(f"bison failed:\n{res.stderr}")
        return render(*parse_c(c_out.read_text()))


def vendor(checkout):
    data = subprocess.run(
        ["git", "-C", checkout, "show", f"{PTA_STANDARDS_REV}:{PTA_STANDARDS_PATH}"],
        capture_output=True,
        check=True,
    ).stdout
    GRAMMAR.write_bytes(data)
    print(f"vendored {PTA_STANDARDS_PATH}@{PTA_STANDARDS_REV[:12]}, sha256 {hashlib.sha256(data).hexdigest()}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the checked-in tables are stale")
    ap.add_argument("--vendor", metavar="PTA_STANDARDS_CHECKOUT", help="re-copy beancount.y first")
    args = ap.parse_args()
    if args.vendor:
        vendor(args.vendor)
    text = generate()
    if args.check:
        current = OUTPUT.read_text() if OUTPUT.exists() else ""
        if current != text:
            fail(
                f"{OUTPUT.relative_to(REPO)} is stale: run "
                "`nix shell --inputs-from . nixpkgs#bison -c python3 scripts/gen-beancount-lalr-tables.py`"
            )
        print(f"{OUTPUT.relative_to(REPO)} is up to date")
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(text)
    print(f"wrote {OUTPUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
