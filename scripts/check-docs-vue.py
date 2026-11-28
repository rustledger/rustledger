#!/usr/bin/env python3
"""Find `{{` that VitePress would compile as a Vue interpolation.

VitePress renders every Markdown page as a Vue template. It escapes `{{`
inside fenced code blocks and inside an inline code span that sits on one
line, but an inline span that wraps onto the next line (`{{1525.49` / `USD}}`)
or a bare `{{` in prose reaches the Vue compiler, which fails the website
build with "Error parsing JavaScript expression" at a line number of the
*compiled* page, not the source. Beancount's total-cost syntax is `{{...}}`,
so this comes up whenever the docs quote it.

This check runs in seconds, before the full website build, and names the
source line. Usage: check-docs-vue.py [DOCS_DIR]  (default: docs)
"""

import pathlib
import re
import sys

FENCE = re.compile(r"^\s*(```|~~~)")
# An inline code span closed on the same line: a run of N backticks, then the
# shortest text up to the next run of exactly N backticks.
INLINE_SPAN = re.compile(r"(`+)(?:(?!\1).)*?\1")


def problems(path: pathlib.Path):
    in_fence = None
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
        stripped = INLINE_SPAN.sub("", line)
        if "{{" in stripped:
            yield lineno, line.strip()


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "docs")
    found = 0
    for path in sorted(root.rglob("*.md")):
        for lineno, text in problems(path):
            found += 1
            print(
                f"::error file={path},line={lineno}::`{{{{` outside a one-line "
                f"code span; VitePress compiles it as Vue. Keep the code span "
                f"on one line or use a fenced block.\n    {path}:{lineno}: {text}"
            )
    if found:
        print(f"{found} line(s) would break the VitePress build.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
