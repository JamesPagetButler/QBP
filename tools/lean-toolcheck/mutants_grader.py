"""Mutation test of tools/lean-toolcheck/toolcheck.py against selftest_grader.py.

usage: python3 -I tools/lean-toolcheck/mutants_grader.py tools/lean-toolcheck <results/runs/ID/raw> <workdir>
M01-M19 reconstruct the Red Team's mutant set on PR #824 (from its one-line descriptions; the
comment does not include the patches). M20-M25 target the r4 rules; M23 and M26-M34 the
pass-file subset rules (Red Team r2); M35-M51 the structural audit and rules H/I (Red Team r3);
`E …` mutants drop each SUBSET_* list entry in turn. R01-R21 target the r5 code: rule R, the
Lean-parser layer (rules L/P), the subset_kinds.json pin and the auditor pin.
Bounding (r5: one selftest is now ~2 min): MUTANTS_FILTER=<regex> keeps matching names only;
MUTANTS_STRIDE=<k> keeps every k-th of the REST (a deterministic sample, reported as such).
A mutant is KILLED iff selftest_grader.py exits non-zero with the mutated grader.
Disk: about 0.3 GB peak (one mutant's work dir at a time; each is deleted after its run).
"""

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

suite, raw, work = map(Path, sys.argv[1:4])
src = (suite / "toolcheck.py").read_text()

M = {
    "M01 column unit -> bytes": [
        ('LEAN_COLUMN_UNIT = "codepoint"', 'LEAN_COLUMN_UNIT = "bytes"')
    ],
    "M02 column always 0": [
        ("sites[(ln, lean_column(orig_lines[ln - 1], m.start()))]", "sites[(ln, 0)]")
    ],
    "M03 sites only at line start": [
        (
            're.finditer(r"#print\\s+axioms\\s+(\\S+)", line)',
            're.finditer(r"^#print\\s+axioms\\s+(\\S+)", line)',
        )
    ],
    "M04 column from the code-only line": [
        ("lean_column(orig_lines[ln - 1], m.start())", "lean_column(line, m.start())")
    ],
    "M05 block comments do not nest": [
        ('depth += 1 if two == "/-" else -1', 'depth += 0 if two == "/-" else -1')
    ],
    "M06 strings not lexed": [
        ("                in_str = True\n", "                in_str = False\n")
    ],
    "M07 backslash escapes ignored": [('if c == "\\\\" and i + 1 < n:', "if False:")],
    "M08 brace_in_string never fires": [('if cl == "s" and ch in "{}":', "if False:")],
    "M09 last report wins (no union)": [
        ("acc = res.setdefault(thm, set())", "acc = res[thm] = set()")
    ],
    "M10 position check dropped": [
        ('sites.get((m["line"], m["col"])) != thm', "False")
    ],
    "M11 severity check dropped": [('m["sev"] != "information" or ', "")],
    "M12 refused file keeps the lexer's sites": [
        ("    if braces:\n", "    if False:\n")
    ],
    "M13 unexpected refusal not a failure": [
        ("            failures.append(refusal)\n", "            pass\n")
    ],
    "M14 expectation regex over the whole log": [
        (
            "return any(re.search(rx, ln) for ln in lines)",
            "return re.search(rx, log + chk_out, re.M) is not None",
        )
    ],
    "M15 checker regex over every line": [
        (
            '[ln for ln in chk_out.splitlines() if ln.startswith("::error")]',
            "chk_out.splitlines()",
        )
    ],
    "M16 sites in comment-stripped text (strings kept)": [
        (
            "code_lines = lean_lines(code_only(src))",
            "code_lines = lean_lines(strip_comments(src))",
        )
    ],
    "M17 empty-layer check removed": [
        ('if not any(r["kind"] == layer for r in rows):', "if False:")
    ],
    "M18 JSON without severity/data trusted": [
        (
            'if not isinstance(m, dict) or "severity" not in m or "data" not in m:',
            "if not isinstance(m, dict):",
        ),
        ('"sev": m["severity"],', '"sev": m.get("severity", "information"),'),
        ('"text": str(m["data"]),', '"text": str(m.get("data", "")),'),
    ],
    "M19 grader-refuses on an unrefused file not a failure": [
        ('    elif "grader-refuses" in kinds:\n', "    elif False:\n")
    ],
    "M20 pass: unpositioned report not a failure": [
        ("            if n_rejected:\n", "            if False:\n")
    ],
    "M21 pass: duplicate site report not a failure": [
        ("            if dup_sites:\n", "            if False:\n")
    ],
    "M22 pass: non-Lean stdout not a failure": [
        ("            if n_untrusted:\n", "            if False:\n")
    ],
    "M23 pass: leaving the subset not a failure": [
        (
            "            if subset:\n                failures.append(subset_note)",
            "            if False:\n                failures.append(subset_note)",
        )
    ],
    "M26 rule A (column-0 command allowlist) off": [
        ("        if ln and not ln[0].isspace():  # A", "        if False:  # A")
    ],
    "M28 rule A: `noncomputable` need not be `noncomputable def`": [
        ('elif head == "noncomputable" and nxt != "def":', "elif False:")
    ],
    "M29 rule B (`#` commands anywhere) off": [
        ('for m in re.finditer(r"#(\\w+)", ln):  # B', "for m in []:  # B")
    ],
    "M30 rule C (attribute allowlist) off": [
        ('for m in re.finditer(r"@\\[", ln):  # C', "for m in []:  # C")
    ],
    "M31 rule C: an unclosed `@[` accepted": [
        (
            '                out.append(f"[C] l.{i}: `@[` not closed on its line")\n',
            "                pass\n",
        )
    ],
    "M32 rule D (refused keywords anywhere) off": [
        ("for w in SUBSET_DENY_WORDS:  # D", "for w in ():  # D")
    ],
    "M33 attribute prefix `scoped` not stripped": [
        ('_ATTR_PREFIXES = ("scoped",)', "_ATTR_PREFIXES = ()")
    ],
    "M34 `subset-refused` expectation always met": [
        (
            '            failures.append(\n                "expected the file to leave the pass-file subset',
            '            (\n                "expected the file to leave the pass-file subset',
        )
    ],
    "M35 pass: structural-audit problems ignored": [
        (
            '            for pr in audit_probs:\n                failures.append(f"structural audit: {pr}")',
            "            for pr in audit_probs:\n                pass",
        )
    ],
    "M36 pass: structural-audit non-standard axioms ignored": [
        ("for decl, axs in sorted(audit_nonstd.items()):", "for decl, axs in []:")
    ],
    "M37 audit: missing .olean not a problem": [
        ('    if not a.get("olean"):', "    if False:")
    ],
    "M40 audit: exact one-module scope not checked": [
        ("if scope != [mod]:", "if False:")
    ],
    "M38 audit: PR #829 grade_run errors ignored": [
        ('probs += [f"PR #829 grade_run: {e}" for e in errors]', "pass")
    ],
    "M39 audit: compile exit not checked": [
        ('if a.get("compile_exit") != 0:', "if False:")
    ],
    "M41 audit: auditor exit not checked": [
        ('if a.get("auditor_exit") != 0:', "if False:")
    ],
    "M52 rule H: non-word command heads off": [
        (
            "for h in _NONWORD_HEADS:  # H, non-word heads",
            "for h in ():  # H, non-word heads",
        )
    ],
    "M53 rule H: `name%` elaborator tokens off": [
        ("for m in _PCT_TOKEN.finditer(bare):  # H", "for m in []:  # H")
    ],
    "M54 heads pin: T00 import list not compared": [
        ('or COMMAND_HEADS_META.get("imports") != t00_imports()', "or False")
    ],
    "M45 pass: stale command_heads.json accepted": [
        (
            '                failures.append(\n                    "command_heads.json was generated',
            '                (\n                    "command_heads.json was generated',
        )
    ],
    "M46 rule H (command keywords anywhere) off": [
        ("toks = _WORD.findall(_blank_attr_lists(ln))  # H", "toks = []  # H")
    ],
    "M47 rule I (`… in` combinator) off": [
        ('if toks and toks[0] in ("open", "set_option"):  # I', "if False:  # I")
    ],
    "M48 rule H: every `scoped` excused": [
        ('if t == "scoped" and j > 0 and toks[j - 1] == "open":', 'if t == "scoped":')
    ],
    "M49 rule H: every `deriving` excused": [
        (
            'if t == "deriving" and (j + 1 >= len(toks) or toks[j + 1] != "instance"):',
            'if t == "deriving":',
        )
    ],
    "M50 `audit-nonstd` expectation always met": [
        (
            '                failures.append(\n                    f"structural audit did NOT report',
            '                (\n                    f"structural audit did NOT report',
        )
    ],
    "M51 `audit-fails` expectation always met": [
        (
            '                failures.append(\n                    "expected the structural audit to fail',
            '                (\n                    "expected the structural audit to fail',
        )
    ],
    "M24 line model back to str.splitlines()": [
        ('    return text.split("\\n")\n', "    return text.splitlines()\n")
    ],
    "M25 source read in text mode (universal newlines)": [
        (
            'return p.read_bytes().decode("utf-8").replace("\\r\\n", "\\n")',
            'return p.read_text(encoding="utf-8")',
        )
    ],
}


def list_entries(name: str) -> list[str]:
    i = src.index(f"{name} = (\n")
    j = src.index("\n)\n", i)
    return [ln for ln in src[i:j].split("\n")[1:] if ln.strip()]


for lst in ("SUBSET_COMMANDS", "SUBSET_ATTRIBUTES", "SUBSET_DENY_WORDS"):
    for ln in list_entries(lst):
        block_start = src.index(f"{lst} = (\n")
        M[f"E {lst} minus {ln.strip()}"] = [
            (
                src[block_start : src.index("\n)\n", block_start)],
                (
                    src[block_start : src.index("\n)\n", block_start)].replace(
                        ln + "\n", "", 1
                    )
                    if ln + "\n" in src[block_start : src.index("\n)\n", block_start)]
                    else src[block_start : src.index("\n)\n", block_start)].replace(
                        "\n" + ln, "", 1
                    )
                ),
            )
        ]

M.update(
    {
        "R01 rule R raw string off": [
            ("        if _RAW_STRING.search(ln):\n", "        if False:\n")
        ],
        "R02 rule R guillemet off": [
            ('        if "\\u00ab" in ln:\n', "        if False:\n")
        ],
        "R03 Lean-parser layer off": [
            (
                "    subset = subset_violations(src) + lean_parse_subset(src, raw, stem, meta)\n",
                "    subset = subset_violations(src)\n",
            )
        ],
        "R04 parse nonce unchecked": [
            (
                'if not isinstance(d, dict) or not nonce or d.get("nonce") != nonce:',
                "if not isinstance(d, dict):",
            )
        ],
        "R05 top-level kind unchecked": [
            (
                '        if c.get("kind") not in allow["top_kinds"]:\n',
                "        if False:\n",
            )
        ],
        "R06 node kinds unchecked": [('            ("kinds", "syntax kind"),\n', "")],
        "R07 nested kinds unchecked": [
            ('            ("nested", "nested command kind"),\n', "")
        ],
        "R08 attributes unchecked": [('            ("attrs", "attribute"),\n', "")],
        "R09 options unchecked": [('            ("set_option", "option"),\n', "")],
        "R10 tactic configs unchecked": [
            ('            ("config", "tactic config"),\n', "")
        ],
        "R11 parse errors ignored": [
            ('        if c.get("parse_error"):\n', "        if False:\n")
        ],
        "R12 scope errors ignored": [
            ('        if c.get("scope_error"):\n', "        if False:\n")
        ],
        "R13 done line unchecked": [
            ('    if done.get("done") is not True:\n', "    if False:\n")
        ],
        "R14 imports unchecked": [
            (
                '        if m.split(".")[0] not in ALLOWED_IMPORT_ROOTS:\n',
                "        if False:\n",
            )
        ],
        "R15 parse exit unchecked": [
            ('    if rec.get("exit") != 0:\n', "    if False:\n")
        ],
        "R16 rule P column unchecked": [
            ('        if c.get("head_col") != 0:\n', "        if False:\n")
        ],
        "R17 rule P python-only starts ignored": [
            ("    for i in sorted(py_starts - lean_starts):\n", "    for i in []:\n")
        ],
        "R18 rule P lean-only starts ignored": [
            (
                "    for i in sorted(x for x in lean_starts - py_starts if isinstance(x, int)):\n",
                "    for i in []:\n",
            )
        ],
        "R19 subset_kinds pin ignored": [
            (
                "            for pr in subset_kinds_pin_problems(run_meta):\n",
                "            for pr in []:\n",
            )
        ],
        "R20 auditor pin ignored": [
            ("    probs += auditor_pin_problems(run_meta)\n", "    pass\n")
        ],
        "R21 header parse error ignored": [
            ('    if hdr.get("parse_error"):\n', "    if False:\n")
        ],
    }
)
_flt = os.environ.get("MUTANTS_FILTER")
_stride = int(os.environ.get("MUTANTS_STRIDE", "1"))
if _flt or _stride > 1:
    keep: dict[str, list[tuple[str, str]]] = {}
    rest: list[tuple[str, list[tuple[str, str]]]] = []
    for mk, mv in M.items():
        if _flt and re.search(_flt, mk):
            keep[mk] = mv
        else:
            rest.append((mk, mv))
    for j, (mk, mv) in enumerate(rest):
        if _stride > 1 and j % _stride == 0:
            keep[mk] = mv
    print(
        f"(bounded run: {len(keep)} of {len(M)} mutants; filter {_flt!r}, stride {_stride})"
    )
    M = keep
rows = []
for name, reps in M.items():
    s = src
    for old, new in reps:
        n = s.count(old)
        if n != 1:
            rows.append((name, f"PATCH-ERROR ({n} matches for {old[:40]!r})"))
            break
        s = s.replace(old, new)
    else:
        d = work / name.split()[0]
        if d.exists():
            shutil.rmtree(d)
        shutil.copytree(suite, d / "suite", ignore=shutil.ignore_patterns("results"))
        (d / "suite" / "toolcheck.py").write_text(s)
        r = subprocess.run(
            [
                "python3",
                "-I",
                str(suite / "selftest_grader.py"),
                str(d / "suite"),
                str(raw),
                str(d / "w"),
            ],
            capture_output=True,
            text=True,
        )
        rows.append((name, "KILLED" if r.returncode != 0 else "SURVIVED"))
        # Disk bound: each selftest copies the suite + raw logs ~100 times (~0.3 GB). Keeping
        # every mutant's directory filled the shared disk on 2026-11-25, so delete it now.
        shutil.rmtree(d, ignore_errors=True)
for mname, v in rows:
    print(f"| {mname} | {v} |")
k = sum(v == "KILLED" for _, v in rows)
print(f"KILLED {k} / {len(rows)}; SURVIVED {sum(v == 'SURVIVED' for _, v in rows)}")
ent = [(n, v) for n, v in rows if n.startswith("E ")]
print(
    f"  rule mutants: {sum(v == 'KILLED' for n, v in rows if not n.startswith('E '))}"
    f" / {len(rows) - len(ent)} killed; list-entry mutants: "
    f"{sum(v == 'KILLED' for _, v in ent)} / {len(ent)} killed"
)
