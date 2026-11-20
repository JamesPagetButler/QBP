#!/usr/bin/env python3
"""Lean CI axiom audit — QBP issue #827 AC2/AC3.

Reads the output of `lake build` (Lean's own message stream, which Lake prints in the
positioned form `info: <file>:<line>:<col>: <text>`) and asserts that every `#print axioms`
report of every built module stays within {propext, Classical.choice, Quot.sound}. `sorryAx`,
native-evaluation axioms (`…_native.native_decide.ax_…`, `Lean.ofReduceBool`) and any
user-declared `axiom` FAIL the gate.

Trust rules (the same as PR #824's toolcheck grader, Gemini finding (2)):
  (a) a report counts only if it is an `info` message positioned EXACTLY at a
      `#print axioms <thm>` command of that file — found with the shared Lean lexer
      (`scripts/lean_lexer.py`: nested comments, strings and char literals handled) — and its
      theorem name matches the command's argument (the printed name may carry the enclosing
      namespace). Text a file prints itself (`#eval IO.println "'x' does not depend on any
      axioms"`) is a message at the `#eval`'s position and is rejected;
  (b) reports MERGE WORST-CASE: all accepted reports for a site are unioned, so no later
      "does not depend on any axioms" line — not even one forged at the right position —
      can clear an axiom Lean really reported;
  (c) every `#print axioms` site in every built module must have at least one accepted
      report, and the build must have built at least one module with sites (an empty
      audit is a failure, not a pass).

Coverage (AC3, printed on every run): the audit covers exactly the theorems named in
`#print axioms` commands in the modules `lake build` builds (the default targets). A
theorem without an in-file `#print axioms` is NOT audited; the per-run summary counts them.

usage: check_lean_axiom_audit.py --log LAKE_BUILD_OUTPUT [--proofs proofs] [--strip-gha]
       [--json OUT]
Exit 0 = pass; 1 = a non-standard axiom, a missing report, or an empty audit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_lexer import strip_comments  # noqa: E402

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MSG_START = re.compile(
    r"^(?P<sev>info|warning|error): (?P<file>[^\n:]+\.lean):(?P<line>\d+):(?P<col>\d+): (?P<text>.*)$"
)
# Lake status / summary lines end a multi-line message.
STATUS = re.compile(
    r"^(?:[✔⚠ℹ✖] \[\d+/\d+\]|Build completed|Some required targets|(?:info|warning|error|trace): (?!\S+\.lean:\d+:\d+: ))"
)
BUILT = re.compile(
    r"^[✔⚠ℹ✖] \[\d+/\d+\] (?:Built|Replayed) (?P<mod>[^\s:]+)(?P<suffix>:\S+)? "
)
GHA_PREFIX = re.compile(r"^(?:[^\t\n]*\t[^\t\n]*\t)?﻿?\d{4}-\d\d-\d\dT[\d:.]+Z ?")
DEP = re.compile(r"^'(?P<thm>.+)' depends on axioms: \[(?P<ax>.*)\]\s*$", re.DOTALL)
NODEP = re.compile(r"^'(?P<thm>.+)' does not depend on any axioms\s*$", re.DOTALL)
SITE = re.compile(r"^([ \t]*)#print axioms\s+(\S+)")
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)",
    re.M,
)


def parse_messages(text: str, strip_gha: bool) -> tuple[list[dict], set[str]]:
    msgs: list[dict] = []
    built: set[str] = set()
    cur: dict | None = None
    for raw in text.splitlines():
        line = GHA_PREFIX.sub("", raw, count=1) if strip_gha else raw
        b = BUILT.match(line)
        if b and not b.group("suffix"):
            built.add(b.group("mod"))
        m = MSG_START.match(line)
        if m:
            cur = {
                "sev": m.group("sev"),
                "file": os.path.normpath(m.group("file")),
                "line": int(m.group("line")),
                "col": int(m.group("col")),
                "text": m.group("text"),
            }
            msgs.append(cur)
        elif STATUS.match(line):
            cur = None
        elif cur is not None:
            cur["text"] += "\n" + line
    return msgs, built


def module_file(proofs: Path, mod: str) -> Path | None:
    rel = mod.replace(".", "/") + ".lean"
    for base in (proofs, proofs / "Sprint12-Inherited"):
        p = base / rel
        if p.is_file():
            return p
    return None


def sites_of(path: Path) -> dict[tuple[int, int], str]:
    code = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    out: dict[tuple[int, int], str] = {}
    for ln, line in enumerate(code.splitlines(), start=1):
        m = SITE.match(line)
        if m:
            out[(ln, len(m.group(1)))] = m.group(2)
    return out


def name_matches(reported: str, written: str) -> bool:
    written = written.lstrip("@").removeprefix("_root_.")
    return reported == written or reported.endswith("." + written)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True, help="captured `lake build` output")
    ap.add_argument("--proofs", default="proofs")
    ap.add_argument(
        "--strip-gha", action="store_true", help="input is a GitHub Actions job log"
    )
    ap.add_argument("--json", help="write the full audit result here")
    a = ap.parse_args()
    proofs = Path(a.proofs)

    msgs, built = parse_messages(
        Path(a.log).read_text(encoding="utf-8", errors="replace"), a.strip_gha
    )

    # file (relative to proofs, normalised) -> sites
    files: dict[str, Path] = {}
    for mod in sorted(built):
        p = module_file(proofs, mod)
        if p is not None:
            files[os.path.normpath(os.path.relpath(p, proofs))] = p
    sites: dict[tuple[str, int, int], str] = {}
    decls = 0
    for rel, p in files.items():
        for (ln, col), thm in sites_of(p).items():
            sites[(rel, ln, col)] = thm
        decls += len(
            DECL.findall(
                strip_comments(p.read_text(encoding="utf-8", errors="replace"))
            )
        )

    acc: dict[tuple[str, int, int], set[str]] = {}
    rejected: list[dict] = []
    for m in msgs:
        dep, nodep = DEP.match(m["text"]), NODEP.match(m["text"])
        if not (dep or nodep):
            continue
        thm = (dep or nodep).group("thm")  # type: ignore[union-attr]
        key = (m["file"], m["line"], m["col"])
        written = sites.get(key)
        if m["sev"] != "info" or written is None or not name_matches(thm, written):
            rejected.append(
                {"file": m["file"], "line": m["line"], "col": m["col"], "thm": thm}
            )
            continue
        s = acc.setdefault(key, set())
        if dep:
            s.update(
                x.strip()
                for x in dep.group("ax").replace("\n", " ").split(",")
                if x.strip()
            )

    bad, missing = [], []
    for key, written in sorted(sites.items()):
        if key not in acc:
            missing.append((key, written))
        elif acc[key] - STANDARD:
            bad.append((key, written, sorted(acc[key] - STANDARD)))
    audited_names = {written for written in sites.values()}

    print(
        f"axiom audit: {len(built)} module(s) built/replayed; {len(files)} source file(s) resolved; "
        f"{len(sites)} `#print axioms` site(s); {sum(1 for k in sites if k in acc)} with an accepted report; "
        f"{len(rejected)} axiom-like message(s) rejected (not at a site / wrong name / not info)"
    )
    print(
        f"coverage (AC3): {len(audited_names)} distinct theorem name(s) audited; "
        f"{decls} theorem/lemma declaration(s) in the built files — those without an in-file "
        f"`#print axioms` are NOT audited by this gate"
    )
    unbuilt = []
    for p in sorted(proofs.rglob("*.lean")):
        rel = os.path.normpath(os.path.relpath(p, proofs))
        if ".lake" in Path(rel).parts or rel in files:
            continue
        n = len(sites_of(p))
        if n:
            unbuilt.append((rel, n))
    if unbuilt:
        print(
            f"coverage (AC3): {sum(n for _, n in unbuilt)} `#print axioms` site(s) in {len(unbuilt)} file(s) "
            f"NOT built by `lake build` (not in a default target) and so not audited: "
            + ", ".join(f"{r} ({n})" for r, n in unbuilt)
        )
    for (rel, ln, col), w, ax in bad:
        print(
            f"::error file=proofs/{rel},line={ln}::#print axioms {w} reports NON-STANDARD axiom(s) {ax}"
        )
    for (rel, ln, col), w in missing:
        print(
            f"::error file=proofs/{rel},line={ln}::#print axioms {w}: no positioned report in the build output"
        )
    failed = bool(bad or missing)
    if not sites:
        print(
            "::error::axiom audit found ZERO `#print axioms` sites in the built modules — an empty audit is a failure"
        )
        failed = True
    if a.json:
        Path(a.json).write_text(
            json.dumps(
                {
                    "modules": len(built),
                    "files": len(files),
                    "sites": len(sites),
                    "accepted": sum(1 for k in sites if k in acc),
                    "rejected": rejected,
                    "non_standard": [
                        {"file": k[0], "line": k[1], "thm": w, "axioms": ax}
                        for k, w, ax in bad
                    ],
                    "missing": [
                        {"file": k[0], "line": k[1], "thm": w} for k, w in missing
                    ],
                    "audited_theorem_names": len(audited_names),
                    "declarations_in_built_files": decls,
                },
                indent=1,
            )
            + "\n"
        )
    print("axiom audit " + ("FAILED." if failed else "PASSED."))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
