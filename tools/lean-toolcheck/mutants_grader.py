"""Mutation test of tools/lean-toolcheck/toolcheck.py against selftest_grader.py.

usage: python3 -I tools/lean-toolcheck/mutants_grader.py tools/lean-toolcheck <results/runs/ID/raw> <workdir>
M01-M19 reconstruct the Red Team's mutant set on PR #824 (from its one-line descriptions; the
comment does not include the patches). M20-M25 target the rules added in this fix round.
A mutant is KILLED iff selftest_grader.py exits non-zero with the mutated grader.
"""

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
    "M23 pass: code-executing construct not a failure": [
        (
            "            if execs:\n                failures",
            "            if False:\n                failures",
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
for mname, v in rows:
    print(f"| {mname} | {v} |")
k = sum(v == "KILLED" for _, v in rows)
print(f"KILLED {k} / {len(rows)}; SURVIVED {sum(v == 'SURVIVED' for _, v in rows)}")
