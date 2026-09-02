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
        # No register on disk in this temp dir -> register empty -> C3-FULL trivially
        # passes for the C1/C2/C3 fixtures (their anchors carry no provenance_kind:proof).
        cmd += ["--register", os.path.join(d, "no-register.json")]
        return subprocess.run(cmd, capture_output=True, text=True).returncode


def run_full_ledger(ledger, register, *, root):
    """Exercise C3-FULL: empty manifest, witnesses skipped, given ledger + register."""
    with tempfile.TemporaryDirectory() as d:
        mf = os.path.join(d, "m.json")
        open(mf, "w", encoding="utf-8").write(
            json.dumps({"manifest_version": "t", "entries": []})
        )
        lf = os.path.join(d, "l.json")
        open(lf, "w", encoding="utf-8").write(json.dumps(ledger, ensure_ascii=False))
        rf = os.path.join(d, "r.json")
        open(rf, "w", encoding="utf-8").write(
            json.dumps({"entries": register}, ensure_ascii=False)
        )
        cmd = [
            sys.executable,
            SCRIPT,
            "--manifest",
            mf,
            "--ledger",
            lf,
            "--register",
            rf,
            "--root",
            root,
            "--skip-witnesses",
        ]
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

    # ---- C3-FULL (full-ledger proof_file resolution + shrink-only register) ----
    with tempfile.TemporaryDirectory() as root:
        os.makedirs(os.path.join(root, "proofs"), exist_ok=True)
        real = os.path.join("proofs", "Real.lean")
        open(os.path.join(root, real), "w").write("theorem t : True := trivial\n")

        def pledger(*anchors):
            # anchors: (id, provenance_kind, proof_file)
            return {
                "anchors": [
                    {"id": a[0], "provenance_kind": a[1], "proof_file": a[2]}
                    for a in anchors
                ]
            }

        def reg(*items):  # items: (id, issue) or id
            out = []
            for it in items:
                if isinstance(it, tuple):
                    out.append({"anchor_id": it[0], "issue": it[1]})
                else:
                    out.append({"anchor_id": it, "issue": "#1"})
            return out

        cf = [
            (
                "C3-FULL: proof anchor resolves -> PASS",
                pledger(("A", "proof", real)),
                reg(),
                0,
            ),
            (
                "C3-FULL: non-proof anchor with 404 file is ignored -> PASS",
                pledger(("A", "theory", "proofs/nope.lean")),
                reg(),
                0,
            ),
            (
                "C3-FULL: proof anchor 404 + registered -> PASS",
                pledger(("A", "proof", "proofs/nope.lean")),
                reg(("A", "#615")),
                0,
            ),
            (
                "C3-FULL: proof anchor 404 NOT registered -> HARD FAIL (new over-claim)",
                pledger(("A", "proof", "proofs/nope.lean")),
                reg(),
                1,
            ),
            (
                "C3-FULL: registered anchor now resolves -> HARD FAIL (stale, shrink-only)",
                pledger(("A", "proof", real)),
                reg(("A", "#615")),
                1,
            ),
            (
                "C3-FULL: registered anchor reclassified to theory -> HARD FAIL (stale)",
                pledger(("A", "theory", "proofs/nope.lean")),
                reg(("A", "#615")),
                1,
            ),
            (
                "C3-FULL: register entry missing issue -> HARD FAIL",
                pledger(("A", "proof", "proofs/nope.lean")),
                reg(("A", "")),
                1,
            ),
        ]
        for name, l, r, exp in cf:
            got = run_full_ledger(l, r, root=root)
            ok = got == exp
            print(
                f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})"
            )
            failures += not ok

    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll manifest-gate tests passed (C1/C2/C3/C3-FULL).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
