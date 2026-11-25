#!/usr/bin/env python3
"""Mutation harness for the Lean CI gate (QBP #827 / PR #829).

Each mutant is ONE textual change to a COPY of scripts/ (the checkout is never modified); the
relevant planted suites then run from the copy, with QBP_TEST_FAIL_FAST=1 (the Lean suite stops
at its first failing case). KILLED = some suite exits non-zero; SURVIVED = every suite passed with
the mutant in place; NOT APPLIED = the pattern no longer occurs exactly once (update the mutant).

usage: python3 scripts/tests/mutate_lean_gate.py [PREFIX ...]   (default: every mutant)
  e.g. `... M1 R2` runs the mutants whose names start with M1 or R2.
Lean-side mutants run the 40+-case Lean suite (core Lean, a few minutes each): run them under
`boxrun` on a cool box. Exit 0 = every selected mutant applied and KILLED.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SRC = Path(__file__).resolve().parents[1]
L, F, Y = (
    "test_lean_axiom_audit.py",
    "test_check_lean_foundations.py",
    "test_check_layer_imports.py",
)
CK, AU, LX, FD, LI = (
    "check_lean_axiom_audit.py",
    "LeanAxiomAudit.lean",
    "lean_lexer.py",
    "check_lean_foundations.py",
    "check_layer_imports.py",
)
GN = "gen_lean_axiom_audit.py"
M = [
    (
        "M1 sorryAx added to the standard set",
        AU,
        "|>.insert ``Quot.sound",
        "|>.insert ``Quot.sound |>.insert ``sorryAx",
        [L],
    ),
    (
        "M2 allowlist matches by prefix",
        CK,
        "        entry = allow.get(decl)\n",
        "        entry = next((v for k, v in allow.items() if decl.startswith(k)), None)\n",
        [L],
    ),
    (
        "M3 dependents of an exception excused",
        CK,
        "        entry = allow.get(decl)\n",
        "        entry = allow.get(decl)\n        if entry is None and set(axs) <= excepted_axioms:\n            continue\n",
        [L],
    ),
    (
        "M4 staleness check dropped",
        CK,
        "        if decl not in allowed_hits:\n",
        "        if False:\n",
        [L],
    ),
    (
        "M5 'no runs' error dropped",
        CK,
        '        errors.append("no audit runs — an empty audit is a failure")',
        "        pass",
        [L],
    ),
    (
        "M6 zero-declarations check dropped",
        CK,
        "    if decls <= 0:",
        "    if False:",
        [L],
    ),
    (
        "M7 >=1 result line accepted",
        CK,
        "    if len(results) != 1:",
        "    if len(results) < 1:",
        [L],
    ),
    (
        "M8 nonce check dropped",
        CK,
        '    if r.get("nonce") != d["nonce"]:',
        "    if False:",
        [L],
    ),
    ("M9 root check dropped", CK, '    if r.get("root") != tag:', "    if False:", [L]),
    (
        "M10 malformed non-standard entry accepted",
        CK,
        '        if not ok:\n            errors.append(f"[{tag}] malformed non-standard entry: {b}")\n            continue\n',
        "        if not ok:\n            continue\n",
        [L],
    ),
    (
        "M11 missing-module check dropped",
        CK,
        '    if missing or not set(d["modules"]) <= set(scope):',
        "    if False:",
        [L],
    ),
    (
        "M12 no result line accepted",
        CK,
        "    if len(results) != 1:\n        errors.append(",
        "    if len(results) == 0:\n        return [], 1, []\n    if len(results) != 1:\n        errors.append(",
        [L],
    ),
    (
        "M13 entry allows a superset",
        CK,
        '    if set(got) != set(entry["axioms"]):',
        '    if not set(entry["axioms"]) <= set(got):',
        [L],
    ),
    (
        "M14 wildcard characters accepted",
        CK,
        '_BAD_CHARS = "*?[]"',
        '_BAD_CHARS = ""',
        [L],
    ),
    (
        "M15 auditor drops inductive->ctor deps",
        AU,
        "  | .inductInfo v => t ++ v.ctors.toArray\n",
        "",
        [L],
    ),
    (
        "M16 auditor drops def values",
        AU,
        "  | .defnInfo v => t ++ v.value.getUsedConstants\n",
        "",
        [L],
    ),
    (
        "M16b auditor ignores on-stack deps (old non-SCC closure)",
        AU,
        "            low := low.insert f.n (Nat.min (low.getD f.n 0) di)",
        "            pure ()",
        [L],
    ),
    (
        "M-fp fingerprint pin ignored",
        CK,
        '    if sha(b.get("fp")) != entry["fingerprint"]:',
        "    if False:",
        [L],
    ),
    (
        "M-mod module pin ignored",
        CK,
        '    if b["module"] != entry["module"]:',
        "    if False:",
        [L],
    ),
    (
        "M-axfp axiom fingerprint pin ignored",
        CK,
        '        if sha(got[name].get("fp")) != fp:',
        "        if False:",
        [L],
    ),
    (
        "M-scope auditor scope = Python list only",
        AU,
        "    if projDirs.any (fun d => path.startsWith d) then",
        "    if projDirs.any (fun d => path.startsWith d) && targets.contains m then",
        [L],
    ),
    (
        "M-unres unresolved check dropped",
        CK,
        "    if unresolved:",
        "    if False:",
        [L],
    ),
    # --- PR #829 Red Team r2 rules -------------------------------------------------------------
    (
        "R2a auditor search path project-first (finding 2)",
        AU,
        "  searchPathRef.set ([tcLib] ++ System.SearchPath.parse sp)",
        "  searchPathRef.set (System.SearchPath.parse sp ++ [tcLib])",
        [L],
    ),
    (
        "R2b shadowed-toolchain-module check dropped",
        CK,
        "    if not isinstance(shadowed, list) or shadowed:",
        "    if False:",
        [L],
    ),
    (
        "R2c standard-axiom identity check dropped (finding 3)",
        CK,
        "    if std_bad:",
        "    if False:",
        [L],
    ),
    (
        "R2d standard-axiom fingerprint ignored",
        CK,
        '            or sha(x.get("fp")) != fp\n',
        "",
        [L],
    ),
    (
        "R2e standard-axiom module ignored",
        CK,
        '            or x.get("module") != mod\n',
        "",
        [L],
    ),
    (
        "R2f build-dir coverage check dropped (finding 4)",
        CK,
        "    for bd in a.build_dir:",
        "    for bd in []:",
        [L],
    ),
    (
        "R2g glued-opener exemption widened to ( ) [ ] { } , ; (finding 5)",
        LX,
        '_LEAN_WHITESPACE = set(" \\t\\r\\n")',
        '_LEAN_WHITESPACE = set(" \\t\\r\\n()[]{},;")',
        [F],
    ),
    (
        "R2h glued-opener exemption widened to U+00A0 (finding 5)",
        LX,
        '_LEAN_WHITESPACE = set(" \\t\\r\\n")',
        '_LEAN_WHITESPACE = set(" \\t\\r\\n\\u00a0")',
        [F],
    ),
    # --- PR #829 Red Team r3 rules -------------------------------------------------------------
    (
        "R3a dangling-reference check dropped (checker)",
        CK,
        "    if not isinstance(dangling, list) or dangling:",
        "    if False:",
        [L],
    ),
    (
        "R3b auditor treats a dangling dependency as axiom-free (the old behaviour)",
        AU,
        "        let some dci := env.find? d | dangling := dangling.insert d; memo := memo.insert d {}; continue",
        "        let some dci := env.find? d | memo := memo.insert d {}; continue",
        [L],
    ),
    (
        "N4 fingerprint ignores numeric literals",
        AU,
        '  | .lit (.natVal n) => s!"(N {n})"',
        '  | .lit (.natVal _) => "(N)"',
        [L],
    ),
    # --- PR #829 Gemini r2 rules ----------------------------------------------------------------
    (
        "G1a number lexing reverted to decimal digits only (finding 1)",
        LX,
        "            i = _number_end(src, i)\n",
        "            while i < n and src[i].isascii() and src[i].isdigit():\n                i += 1\n",
        [F],
    ),
    (
        "G1b glued-after-number check dropped",
        LX,
        "            i = _number_end(src, i)\n"
        '            if i < n and (_id_rest(src[i]) or src[i] in "\\"\'«`"):\n',
        "            i = _number_end(src, i)\n            if False:\n",
        [F],
    ),
    (
        "G1c field-index rule dropped (`h.1.symm` read as a number)",
        LX,
        '        elif c.isascii() and c.isdigit() and i > 0 and src[i - 1] == ".":',
        "        elif False:",
        [F],
    ),
    (
        "G1d raw-string ban dropped",
        FD,
        '            (RAW_STRING, lambda t: literal_sites(t)["raw"]),\n',
        "",
        [F],
    ),
    (
        "G1e char-literal ban dropped",
        FD,
        '            (CHAR_LITERAL, lambda t: literal_sites(t)["char"]),\n',
        "",
        [F],
    ),
    (
        "G3 recursor-rule rhs no longer walked (finding 3)",
        AU,
        "  | .recInfo v => if full then v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants) t else t\n",
        "",
        [L],
    ),
    (
        "G5a importModules with loadExts := true (finding 5)",
        AU,
        "  let env ← importModules imports {} (loadExts := false)",
        "  let env ← importModules imports {} (loadExts := true)",
        [L],
    ),
    (
        "G5b theorem values no longer walked",
        AU,
        "  | .thmInfo v => if full then t ++ v.value.getUsedConstants else t\n",
        "",
        [L],
    ),
    (
        "G5c opaque values no longer walked",
        AU,
        "  | .opaqueInfo v => t ++ v.value.getUsedConstants\n",
        "",
        [L],
    ),
    (
        "G5d generator default-target filter dropped",
        GN,
        "    roots = [r for _, rs, d in targets if d for r in rs]",
        "    roots = [r for _, rs, d in targets for r in rs]",
        [L],
    ),
    (
        "G5e generator reserved-root refusal dropped",
        GN,
        'RESERVED_ROOTS = {"Init", "Std", "Lean", "Lake"}',
        "RESERVED_ROOTS: set = set()",
        [L],
    ),
    # --- PR #829 Red Team r5 rule (interim token-declaration ban) -----------------------------
    (
        "T5a token-declaration ban (lexer-code match) dropped",
        FD,
        "            (TOKEN_DECL, lambda t: TOKEN_DECL_CODE.findall(code_only(t))),\n",
        "",
        [F],
    ),
    (
        "T5b token-declaration ban (raw-text fallback) dropped",
        FD,
        "            (TOKEN_DECL_LINE, lambda t: TOKEN_DECL_RAW.findall(t)),\n",
        "",
        [F],
    ),
    (
        "T5c both token-declaration bans dropped (the gate is forged again)",
        FD,
        "            (TOKEN_DECL, lambda t: TOKEN_DECL_CODE.findall(code_only(t))),\n"
        "            (TOKEN_DECL_LINE, lambda t: TOKEN_DECL_RAW.findall(t)),\n",
        "",
        [F],
    ),
    (
        "M17 lexer without nesting",
        LX,
        "                    depth, j = depth + 1, j + 2",
        "                    j += 2",
        [F],
    ),
    (
        "M18 lexer without strings",
        LX,
        "        elif c == '\"':",
        "        elif False:",
        [F],
    ),
    (
        "M19 lexer without the char-literal rule",
        LX,
        '        elif c == "\'" and src[i + 1 : i + 2] != "\'" and _char_lit_end(src, i) > 0:',
        "        elif False:",
        [F],
    ),
    (
        "M20 brace-in-string ban dropped",
        FD,
        "            (BRACE_IN_STRING, brace_in_string),\n",
        "",
        [F],
    ),
    (
        "M21 lexer without -- line comments",
        LX,
        '        elif two == "--":',
        "        elif False:",
        [F],
    ),
    (
        "M22 lexer without raw strings",
        LX,
        '        elif c == "r" and _raw_start(src, i) >= 0:',
        "        elif False:",
        [F],
    ),
    (
        "M23 lexer without guillemet identifiers",
        LX,
        '        if j < n and src[j] == "«":',
        "        if False:",
        [F],
    ),
    (
        "M24 glued-opener ban dropped",
        FD,
        "            (AMBIGUOUS_OPENER, ambiguous_comment_openers),\n",
        "",
        [F],
    ),
    (
        "M25 lexer without identifier consumption",
        LX,
        '        elif _id_first(c) or c == "«":\n            i = _ident_end(src, i)\n',
        "",
        [F],
    ),
    (
        "M26 one import per line (old IMPORT_RE)",
        LI,
        "    return IMPORT_CMD_RE.findall(strip_comments(text))",
        "    return IMPORT_RE.findall(strip_comments(text))",
        [Y, L],
    ),
]

only = sys.argv[1:]
killed = 0
rows = []
for name, f, old, new, suites in M:
    if only and not any(name.startswith(o) for o in only):
        continue
    with tempfile.TemporaryDirectory() as td:
        dst = Path(td) / "scripts"
        shutil.copytree(SRC, dst, ignore=shutil.ignore_patterns("__pycache__"))
        p = dst / f
        s = p.read_text(encoding="utf-8")
        if s.count(old) != 1:
            rows.append((name, f"NOT APPLIED (pattern count {s.count(old)})"))
            print(rows[-1], flush=True)
            continue
        p.write_text(s.replace(old, new), encoding="utf-8")
        verdict = "SURVIVED"
        for t in suites:
            r = subprocess.run(
                [sys.executable, str(dst / t)],
                capture_output=True,
                text=True,
                env=dict(os.environ, QBP_TEST_FAIL_FAST="1"),
            )
            if r.returncode != 0:
                verdict = f"KILLED ({t})"
                break
        killed += verdict.startswith("KILLED")
        rows.append((name, verdict))
        print(rows[-1], flush=True)
print(f"\n{killed}/{len(rows)} killed")
sys.exit(0 if killed == len(rows) else 1)
