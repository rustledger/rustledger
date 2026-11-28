#!/usr/bin/env python3
"""Find `{{` that VitePress would compile as a Vue interpolation.

VitePress renders every Markdown page as a Vue template. Only fenced code
blocks are escaped. Inline code is NOT: `{{T}}` in backticks renders as an
empty <code></code> with no error, and `{{1525.49 USD}}` fails the website
build with "Error parsing JavaScript expression" at a line of the *compiled*
page, not the source. Beancount's total-cost syntax is `{{...}}`, so this
comes up whenever the docs quote it.

Write such text inside <span v-pre>...</span> (inline) or a `::: v-pre`
container (block); both stop Vue compiling it.

This check runs in seconds, before the full website build, and names the
source line. Usage: check-docs-vue.py [DOCS_DIR]  (default: docs)
"""

import pathlib
import re
import sys

FENCE = re.compile(r"^\s*(```|~~~)")
VPRE_OPEN = re.compile(r"^\s*:::\s*v-pre\s*$")
CONTAINER_CLOSE = re.compile(r"^\s*:::\s*$")
VPRE_SPAN = re.compile(r"<(\w+)\s+v-pre\b[^>]*>.*?</\1>")


def problems(path: pathlib.Path):
    in_fence = None
    in_vpre = False
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        m = FENCE.match(line)
        if m:
            if in_fence is None:
                in_fence = m.group(1)
            elif m.group(1) == in_fence:
                in_fence = None
            continue
        if in_fence is not None:
            continue
        if VPRE_OPEN.match(line):
            in_vpre = True
            continue
        if in_vpre:
            if CONTAINER_CLOSE.match(line):
                in_vpre = False
            continue
        if "{{" in VPRE_SPAN.sub("", line):
            yield lineno, line.strip()


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "docs")
    found = 0
    for path in sorted(root.rglob("*.md")):
        for lineno, text in problems(path):
            found += 1
            print(
                f"::error file={path},line={lineno}::`{{{{` outside a fenced "
                f"block; VitePress compiles it as Vue (inline code is not "
                f"escaped). Wrap it in <span v-pre>...</span>.\n"
                f"    {path}:{lineno}: {text}"
            )
    if found:
        print(f"{found} line(s) would be compiled as Vue.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
