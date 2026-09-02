#!/usr/bin/env python3
"""Tests for the C1/C2/C3 manifest-enforcement gate (scripts/check_anchor_manifest.py).

C1/C2: a declared anchor-worthy deliverable absent from the ledger is a HARD FAIL
(cannot be baselined away); the candidate set is the manifest, not `grep theorem`.
C3: a declared anchor whose witnesses don't resolve in source is a HARD FAIL
(#613/#615 class). Run: python3 scripts/test_check_anchor_manifest.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_anchor_manifest.py")


def run(manifest, ledger, *, skip_witnesses=True, root=None):
    with tempfile.TemporaryDirectory() as d:
        mf = os.path.join(d, "m.json")
        open(mf, "w", encoding="utf-8").write(json.dumps(manifest, ensure_ascii=False))
        lf = os.path.join(d, "l.json")
        open(lf, "w", encoding="utf-8").write(json.dumps(ledger, ensure_ascii=False))
        cmd = [
            sys.executable,
            SCRIPT,
            "--manifest",
            mf,
            "--ledger",
            lf,
            "--root",
            root or d,
        ]
        if skip_witnesses:
            cmd.append("--skip-witnesses")
        return subprocess.run(cmd, capture_output=True, text=True).returncode


def led(*items):  # items: id or (id, proof_file)
    anchors = []
    for it in items:
        if isinstance(it, tuple):
            anchors.append({"id": it[0], "proof_file": it[1]})
        else:
            anchors.append({"id": it})
    return {"anchors": anchors}


def man(*entries):  # entries: id or (id, [witnesses], proof_system)
    out = []
    for e in entries:
        if isinstance(e, tuple):
            out.append(
                {
                    "anchor_id": e[0],
                    "proof_system": e[2] if len(e) > 2 else "lean4",
                    "declared_by": "#1",
                    "witnesses": e[1],
                }
            )
        else:
            out.append(
                {
                    "anchor_id": e,
                    "proof_system": "lean4",
                    "declared_by": "#1",
                    "witnesses": [],
                }
            )
    return {"manifest_version": "test", "entries": out}


def main():
    failures = 0

    # ---- C1/C2 (witnesses skipped) ----
    c12 = [
        ("C1: all declared present → PASS", man("A", "B"), led("A", "B", "aux1"), 0),
        ("C2: declared anchor missing → HARD FAIL", man("A", "B"), led("A"), 1),
        ("empty manifest → PASS", man(), led("A"), 0),
        ("auxiliary lemma not in manifest does not fail", man("A"), led("A"), 0),
    ]
    for name, m, l, exp in c12:
        got = run(m, l, skip_witnesses=True)
        ok = got == exp
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        failures += not ok

    # ---- C3 (witnesses-resolve, needs source) ----
    with tempfile.TemporaryDirectory() as root:
        os.makedirs(os.path.join(root, "proofs"), exist_ok=True)
        src = os.path.join("proofs", "X.lean")
        open(os.path.join(root, src), "w").write("theorem foo : True := trivial\n")
        c3 = [
            (
                "C3: witness resolves in source → PASS",
                man(("A", ["Mod.foo"])),
                led(("A", src)),
                0,
            ),
            (
                "C3: witness NOT in source → HARD FAIL",
                man(("A", ["Mod.bar_missing"])),
                led(("A", src)),
                1,
            ),
            (
                "C3: proof_file missing → HARD FAIL",
                man(("A", ["Mod.foo"])),
                led(("A", "proofs/nope.lean")),
                1,
            ),
        ]
        for name, m, l, exp in c3:
            got = run(m, l, skip_witnesses=False, root=root)
            ok = got == exp
            print(
                f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})"
            )
            failures += not ok

    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll manifest-gate tests passed (C1/C2/C3).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
