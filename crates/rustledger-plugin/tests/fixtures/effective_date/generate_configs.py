"""Generate effective_date plugin configs and classify each the way upstream
reads it: `if config: literal_eval(config)`, falsy means the default config,
and every entry needs string `earlier` and `later`.

    python3 -I generate_configs.py SEED N > configs.json

Prints [[config, class], ...] with class "default", "error", or
"ok:" + json [[prefix, earlier, later], ...]. `configs.json` here is seed 2536,
N 500, classified by Python 3.13; the Rust test
`the_config_reads_as_literal_eval_reads_it_on_generated_configs` checks
`parse_config` against it. Configs come from a small grammar (every quote
style and prefix, escapes, implicit concatenation, comments, line
continuations, CR and CRLF line breaks, trailing commas, repeated keys, extra
keys, non-string values)
plus random character mutations."""
import ast, json, random, sys, warnings
warnings.simplefilter("ignore")
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2536)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
ACC = ["Expenses", "Expenses:Car", "Income", "Assets:Hold:X", "L:H", "A:H", "Ex'p", 'Ex"p', "Ex\\p", "é:ü", ""]
def qstr(s):
    style = rng.choice(["'", "'", '"', '"', "'''", '"""', "r'", "u'", "R\""] + (["b'"] if rng.random() < 0.05 else []))
    if style.startswith(("r", "R")):
        q = style[1:]
        if q in s or s.endswith("\\"): q = "'" if '"' in s else '"'
        if q in s: return repr(s)
        return style[0] + q + s + q
    if style == "b'":
        try: s.encode("ascii")
        except UnicodeEncodeError: return repr(s)
        return "b" + repr(s)
    body = s.replace("\\", "\\\\")
    for ch, esc in (("A", "\\x41"), ("e", "\\u0065"), ("p", "\\160")):
        if rng.random() < 0.15: body = body.replace(ch, esc)
    q = style
    body = body.replace(q[0], "\\" + q[0])
    if rng.random() < 0.1 and len(body) > 2:
        i = rng.randrange(1, len(body)); return q + body[:i] + q + " " + q + body[i:] + q
    return q + body + q
def ws():
    return rng.choice(["", " ", "  ", "\n", " # c\n", "\t", "\\\n", "\r\n", "\\\r\n", "\r"])
def value():
    r = rng.random()
    if r < 0.97: return qstr(rng.choice(ACC))
    return rng.choice(["1", "None", "True", "[1]", "{}", "0x10", "1_0", "1j"])
def entry():
    fields = []
    keys = ["earlier", "later"] + (["note"] if rng.random() < 0.3 else [])
    if rng.random() < 0.05: keys = keys[1:]
    rng.shuffle(keys)
    for k in keys:
        fields.append(qstr(k) + ws() + ":" + ws() + value())
    if rng.random() < 0.1: fields.append(fields[0])
    inner = "{" + ws() + ("," + ws()).join(fields) + ("," if rng.random() < 0.3 else "") + ws() + "}"
    if rng.random() < 0.05: inner = rng.choice(["'x'", "1", "[]", "None"])
    key = qstr(rng.choice(ACC)) if rng.random() < 0.98 else rng.choice(["1", "None", "(1,)"])
    return key + ws() + ":" + ws() + inner
def config():
    r = rng.random()
    if r < 0.05: return rng.choice(["", " ", "{}", "None", "[]", "0", "''", "()", "False", "0x0", "{,}", "{'a'}"])
    n = rng.choice([1, 1, 2, 3])
    body = "{" + ws() + ("," + ws()).join(entry() for _ in range(n)) + ("," if rng.random() < 0.3 else "") + ws() + "}"
    if rng.random() < 0.05: body = "(" + body + ")"
    if rng.random() < 0.1: body = ws() + body + ws()
    return body
ALPHA = "{}[]()'\":,#\\\n\r rbuxj0_.-+é"
def mutate(s):
    for _ in range(rng.choice([1, 1, 2, 3])):
        if not s: s = rng.choice(ALPHA); continue
        i = rng.randrange(len(s)); op = rng.random()
        if op < 0.4: s = s[:i] + s[i+1:]
        elif op < 0.8: s = s[:i] + rng.choice(ALPHA) + s[i:]
        else:
            j = rng.randrange(i, len(s) + 1); s = s[:i] + s[i:j] + s[i:]
    return s
def classify(c):
    if c == "": return "default"
    try: v = ast.literal_eval(c)
    except Exception: return "error"
    # literal_eval yields only builtin literals, whose truth test never raises.
    if not v: return "default"
    if not isinstance(v, dict): return "error"
    out = []
    for k, d in v.items():
        if not isinstance(k, str) or not isinstance(d, dict): return "error"
        e, l = d.get("earlier"), d.get("later")
        if not isinstance(e, str) or not isinstance(l, str): return "error"
        out.append([k, e, l])
    return "ok:" + json.dumps(out, ensure_ascii=False)
cases = []
seen = set()
while len(cases) < N:
    c = config()
    if rng.random() < 0.35: c = mutate(c)
    if c in seen or "\x00" in c: continue
    seen.add(c); cases.append([c, classify(c)])
json.dump(cases, sys.stdout, ensure_ascii=False, separators=(",", ":"))
