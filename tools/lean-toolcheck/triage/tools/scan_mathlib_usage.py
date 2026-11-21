"""Mathlib deprecation/rename triage for QBP usage. Reads Mathlib sources as TEXT only.

usage: mathlib_triage.py QBP_PROOFS OLD_MATHLIB_ROOT NEW_MATHLIB_ROOT OUT_JSON
(the *_ROOT dirs contain Mathlib/…)
"""

import re, sys, json, pathlib, collections

qbp, old, new, outp = map(pathlib.Path, sys.argv[1:5])


def strip(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--.*", "", s)


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|alias|structure|class|inductive)\s+([^\s:(\[{]+)",
    re.M,
)
NS = re.compile(r"^\s*(namespace|section|end|noncomputable section)\b\s*([\w.]*)", re.M)
DEPR = re.compile(
    r"@\[([^\]]*\bdeprecated\b[^\]]*)\]\s*(?:\n\s*)?(?:(?:protected|private|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|alias|instance|structure|class)\s+([^\s:(\[{]+)",
    re.M,
)


def scan(root):
    names = collections.defaultdict(set)  # last component -> set(full names)
    depr = {}  # full name -> (since, replacement, file)
    depmods = {}
    for f in (root / "Mathlib").rglob("*.lean"):
        txt = f.read_text(encoding="utf-8", errors="replace")
        code = strip(txt)
        if re.search(r"^deprecated_module\b", code, re.M):
            mod = ".".join(f.relative_to(root).with_suffix("").parts)
            m = re.search(
                r'^deprecated_module\s*(?:"([^"]*)")?\s*\(since := "([^"]+)"\)',
                code,
                re.M,
            )
            depmods[mod] = (m.group(2) if m else "?", m.group(1) if m else "")
        # walk lines tracking namespaces
        stack = []
        events = []
        for m in NS.finditer(code):
            events.append((m.start(), "ns", m.group(1), m.group(2)))
        for m in DECL.finditer(code):
            events.append((m.start(), "decl", m.group(1), m.group(2)))
        for m in DEPR.finditer(code):
            events.append((m.end(3) - len(m.group(3)), "depr", m.group(1), m.group(3)))
        events.sort(key=lambda e: (e[0], 0 if e[1] == "ns" else 1))
        for pos, kind, a, b in events:
            if kind == "ns":
                if a == "namespace":
                    stack.append(("ns", b))
                elif a in ("section", "noncomputable section"):
                    stack.append(("sec", b))
                elif a == "end" and stack:
                    stack.pop()
                continue
            nsname = ".".join(x[1] for x in stack if x[0] == "ns" and x[1])
            nm = b
            full = (
                nm[len("_root_.") :]
                if nm.startswith("_root_.")
                else (f"{nsname}.{nm}" if nsname else nm)
            )
            if kind == "decl":
                names[full.split(".")[-1]].add(full)
            else:
                since = re.search(r'since\s*:=\s*"([^"]+)"', a)
                repl = re.search(r"deprecated\s+([^\s(]+)", a)
                depr[full] = (
                    since.group(1) if since else "?",
                    repl.group(1) if repl else "",
                    str(f.relative_to(root)),
                )
    return names, depr, depmods


print("scanning old…", file=sys.stderr)
on, od, odm = scan(old)
print("scanning new…", file=sys.stderr)
nn, nd, ndm = scan(new)

files = [
    p
    for p in qbp.rglob("*.lean")
    if p.relative_to(qbp).parts[0] not in (".lake", "lean-toolcheck")
]
tokens = collections.defaultdict(set)
imports = collections.defaultdict(set)
for p in files:
    code = strip(p.read_text(encoding="utf-8", errors="replace"))
    opens: set[str] = set()
    for line in re.findall(
        r"^\s*open\s+(?:scoped\s+)?([^\n]*?)(?:\s+in)?\s*$", code, re.M
    ):
        opens.update(x for x in line.split() if re.match(r"^[A-Z][\w.]*$", x))
    for t in set(
        re.findall(r"(?<![\w.'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)", code)
    ):
        tokens[t].add(str(p.relative_to(qbp)))
        for o in opens:
            tokens[o + "." + t].add(str(p.relative_to(qbp)))
    for m in re.findall(r"^[ \t]*import\s+(Mathlib[\w.]*)", code, re.M):
        imports[m].add(str(p.relative_to(qbp)))


def exists(root, mod):
    return (root / (mod.replace(".", "/") + ".lean")).exists()


imp = []
for m in sorted(imports):
    imp.append(
        {
            "module": m,
            "old": exists(old, m),
            "new": exists(new, m),
            "deprecated_new": ndm.get(m),
            "used_by": sorted(imports[m]),
        }
    )


def resolve(tok, names):
    last = tok.split(".")[-1]
    cands = names.get(last, set())
    return sorted(c for c in cands if c == tok)


hits_depr, hits_missing = [], []
for tok, users in sorted(tokens.items()):
    oc = resolve(tok, on)
    if not oc:
        continue  # not a Mathlib name at the old pin (QBP-local, Lean core, or a variable)
    for full in oc:
        if full in nd and full not in od:
            s, r, f = nd[full]
            hits_depr.append(
                {
                    "token": tok,
                    "mathlib_name": full,
                    "since": s,
                    "replacement": r,
                    "file": f,
                    "used_by": sorted(users),
                }
            )
    nc = resolve(tok, nn)
    if not nc:
        hits_missing.append({"token": tok, "old_names": oc, "used_by": sorted(users)})

# names QBP uses that were ALREADY deprecated at the old pin (would warn today)
already = []
for tok, users in sorted(tokens.items()):
    for full in resolve(tok, on):
        if full in od:
            already.append(
                {
                    "token": tok,
                    "mathlib_name": full,
                    "since": od[full][0],
                    "used_by": sorted(users),
                }
            )

out = {
    "imports": imp,
    "newly_deprecated_used": hits_depr,
    "missing_at_new": hits_missing,
    "already_deprecated_at_old": already,
    "stats": {
        "qbp_files": len(files),
        "tokens": len(tokens),
        "old_decl_lastnames": len(on),
        "new_decl_lastnames": len(nn),
        "new_deprecations": len(nd),
        "old_deprecations": len(od),
        "new_deprecated_modules": len(ndm),
        "old_deprecated_modules": len(odm),
    },
}
json.dump(out, open(outp, "w"), indent=1)
print(json.dumps(out["stats"], indent=1))
print(
    "imports missing/deprecated at new:",
    [i for i in imp if not i["new"] or i["deprecated_new"]],
)
print("newly deprecated & used:", len(hits_depr))
for h in hits_depr:
    print(
        "  D",
        h["token"],
        "->",
        h["mathlib_name"],
        h["since"],
        h["replacement"],
        h["used_by"][:3],
    )
print("missing at new:", len(hits_missing))
for h in hits_missing:
    print("  M", h["token"], h["old_names"][:3], h["used_by"][:3])
print("already deprecated at old:", len(already))
for h in already[:30]:
    print("  A", h["token"], h["mathlib_name"], h["since"], h["used_by"][:2])
