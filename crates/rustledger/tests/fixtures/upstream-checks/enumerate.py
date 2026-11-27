#!/usr/bin/env python3
"""Enumerate every check the installed beancount can report to a user.

Prints one check id per line, sorted. The drift guard
(`crates/rustledger/tests/upstream_checks_test.rs`) compares this list with
`checks.toml` beside this script, so a beancount upgrade that adds, removes
or rewords a check fails the guard until the table says what rledger does.

Why introspect the installed package (AST of its sources) rather than pin a
hash of the scanned files: a hash goes red on ANY edit to those files (a
docstring, a refactor), and says nothing about which check changed, so the
maintainer would redo the walk by hand on every upgrade. An id per error site
goes red only when a check is added, removed or reworded, and names it.

The enumeration has five kinds of id:

  site:<module.function>:<message>
      A construction of one of beancount's error tuples (every NamedTuple /
      collections.namedtuple whose name ends in `Error`, e.g.
      `ValidationError(meta, "Duplicate open directive for {}", entry)`), in
      `beancount/{core,ops,parser,plugins}` and `loader.py`. The message is
      the literal template with each interpolation written `{}`; a message
      held in a variable is resolved from the variable's assignments in the
      same function (one id per assignment); a message the source does not
      spell (`str(exc)`, or one built in C) is `<dynamic>`.
  raise:<module.function>:<message>
      A `raise SomeError("...")` in `beancount/{ops,parser,plugins}` and
      `loader.py`. Beancount turns several of these into user-facing errors
      (the option converters' ValueErrors become "Error for option ...", the
      booking ValueErrors become BookingErrors, an exception escaping a
      plugin becomes "Error applying plugin ...").
  plugin:<module>
      Every module under `beancount/plugins/`, whether or not it reports an
      error itself (check_closing and check_drained check by synthesizing
      balance assertions).
  option-deprecated:<name>
      Every option whose descriptor carries a deprecation message, which the
      grammar reports as a DeprecatedError when the option is set.
  manual:<name>
      Not produced here: checks the AST cannot see (gpg decryption in
      `utils/encryption.py`). The table lists them by hand.

Run with `python3 -I`, so nothing in the working directory shadows a module.
"""

import ast
import os
import sys

import beancount
from beancount.parser import options

ROOT = os.path.dirname(beancount.__file__)
SITE_DIRS = ("core", "ops", "parser", "plugins")
RAISE_DIRS = ("ops", "parser", "plugins")
TOP_LEVEL = ("loader.py",)


def modules(dirs):
    """Yield (dotted module name, path) for non-test sources in `dirs`."""
    for top in TOP_LEVEL:
        yield "beancount." + top[:-3], os.path.join(ROOT, top)
    for sub in dirs:
        base = os.path.join(ROOT, sub)
        for name in sorted(os.listdir(base)):
            if name.endswith(".py") and not name.endswith("_test.py"):
                yield f"beancount.{sub}.{name[:-3]}", os.path.join(base, name)


def call_name(func):
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return None


def template(expr):
    """The literal message template of `expr`, or None."""
    if isinstance(expr, ast.Constant) and isinstance(expr.value, str):
        return expr.value
    if isinstance(expr, ast.JoinedStr):
        return "".join(
            v.value if isinstance(v, ast.Constant) else "{}" for v in expr.values
        )
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Mod):
        return template(expr.left)
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
        left, right = template(expr.left), template(expr.right)
        if left is None and right is None:
            return None
        return (left or "{}") + (right or "{}")
    if (
        isinstance(expr, ast.Call)
        and isinstance(expr.func, ast.Attribute)
        and expr.func.attr == "format"
    ):
        return template(expr.func.value)
    return None


def error_classes(trees):
    names = set()
    for tree in trees:
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and node.name.endswith("Error"):
                if any(call_name(b) == "NamedTuple" for b in node.bases):
                    names.add(node.name)
            if (
                isinstance(node, ast.Assign)
                and isinstance(node.value, ast.Call)
                and call_name(node.value.func) == "namedtuple"
            ):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id.endswith("Error"):
                        names.add(target.id)
    return names


def messages(call, function, position):
    """The message templates of the argument at `position` (or `message=`)."""
    arg = next((k.value for k in call.keywords if k.arg == "message"), None)
    if arg is None:
        if len(call.args) <= position:
            return ["<dynamic>"]
        arg = call.args[position]
    found = template(arg)
    if found is not None:
        return [found]
    # A message held in a variable: every template assigned to it in this
    # function, and `<dynamic>` for an assignment the source does not spell.
    if isinstance(arg, ast.Name) and function is not None:
        found = {
            template(node.value) or "<dynamic>"
            for node in ast.walk(function)
            if isinstance(node, ast.Assign)
            and any(isinstance(tg, ast.Name) and tg.id == arg.id for tg in node.targets)
        }
        if found:
            return sorted(found)
    return ["<dynamic>"]


def scan(module, tree, classes, want_raises):
    ids = set()

    def visit(node, stack, function):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                inner = child if not isinstance(child, ast.ClassDef) else function
                visit(child, stack + [child.name], inner)
                continue
            where = ".".join([module] + stack)
            if isinstance(child, ast.Call) and call_name(child.func) in classes:
                # Every error tuple is (source, message, ...).
                for msg in messages(child, function, 1):
                    ids.add(f"site:{where}:{msg}")
            if (
                want_raises
                and isinstance(child, ast.Raise)
                and isinstance(child.exc, ast.Call)
                and call_name(child.exc.func) != "NotImplementedError"
            ):
                for msg in messages(child.exc, function, 0):
                    ids.add(f"raise:{where}:{msg}")
            visit(child, stack, function)

    visit(tree, [], None)
    return ids


def main():
    parsed = {}
    for module, path in modules(SITE_DIRS):
        with open(path, encoding="utf-8") as f:
            parsed[module] = ast.parse(f.read(), path)
    classes = error_classes(parsed.values())
    raise_modules = {m for m, _ in modules(RAISE_DIRS)}

    ids = set()
    for module, tree in parsed.items():
        ids |= scan(module, tree, classes, module in raise_modules)
    for name in os.listdir(os.path.join(ROOT, "plugins")):
        if name.endswith(".py") and not name.endswith("_test.py") and name != "__init__.py":
            ids.add(f"plugin:beancount.plugins.{name[:-3]}")
    for name, desc in options.OPTIONS.items():
        if desc.deprecated:
            ids.add(f"option-deprecated:{name}")

    if "--version" in sys.argv:
        print(beancount.__version__)
        return
    for check in sorted(ids):
        # One id per line: a message template never spans lines in the
        # table, so a newline inside one is written `\n`.
        print(check.replace("\n", "\\n"))


if __name__ == "__main__":
    main()
