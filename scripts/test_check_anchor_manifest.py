#!/usr/bin/env python3
"""Tests for the C1/C2 manifest-enforcement gate (scripts/check_anchor_manifest.py).

Asserts: a declared anchor-worthy deliverable absent from the ledger is a HARD FAIL
(FAULT-S4-005 C2 — cannot be baselined away); the candidate set is the manifest, not
`grep theorem` (auxiliary lemmas not in the manifest never register).
Run: python3 scripts/test_check_anchor_manifest.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_anchor_manifest.py")


def run(manifest, ledger):
    with tempfile.TemporaryDirectory() as d:
        mf = os.path.join(d, "m.json")
        open(mf, "w").write(json.dumps(manifest))
        lf = os.path.join(d, "l.json")
        open(lf, "w").write(json.dumps(ledger))
        r = subprocess.run(
            [sys.executable, SCRIPT, "--manifest", mf, "--ledger", lf],
            capture_output=True,
            text=True,
        )
        return r.returncode


def ledger(*ids):
    return {"anchors": [{"id": i} for i in ids]}


def manifest(*ids):
    return {
        "manifest_version": "test",
        "entries": [
            {
                "anchor_id": i,
                "proof_system": "lean4",
                "declared_by": "#1",
                "witnesses": ["A.b"],
            }
            for i in ids
        ],
    }


CASES = [
    (
        "all declared anchors present → PASS",
        manifest("A", "B"),
        ledger("A", "B", "aux1"),
        0,
    ),
    ("a declared anchor missing → HARD FAIL", manifest("A", "B"), ledger("A"), 1),
    ("empty manifest → PASS (nothing declared)", manifest(), ledger("A"), 0),
    # candidate set is the manifest, not grep: an un-anchored source lemma NOT in the
    # manifest must NOT fail the gate (that was the 640-orphan trap).
    ("auxiliary lemma (not in manifest) does not fail", manifest("A"), ledger("A"), 0),
]


def main():
    failures = 0
    for name, m, l, exp in CASES:
        got = run(m, l)
        ok = got == exp
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        failures += not ok
    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll manifest-gate tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
