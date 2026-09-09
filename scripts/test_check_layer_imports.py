#!/usr/bin/env python3
"""Tests for the layer-import linter (scripts/check_layer_imports.py).

Focus: Rule 5 — BUILD-VISIBILITY. A .lean under a physics/Sprint12 dir that is
reachable from no declared lakefile build-target root is compiled by nothing, so a
broken proof in it rides CI-green (the General3D.lean class, #625/#619). The gate
must flag it, unless it is listed in the shrink-only, issue-linked quarantine.

Per the gate-validation discipline in docs/cth/proof-anchor-best-practices.md ("a
gate is judged by what it catches"), the centrepiece is an ADVERSARIAL test that
plants a build-invisible physics file and asserts the gate catches it (#625 AC2).

Each case builds a minimal synthetic proofs/ tree in a tempdir and runs the real
checker via `--proofs`. Run: python3 scripts/test_check_layer_imports.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_layer_imports.py")

# A minimal, fully-clean proofs tree: passes rules 1–5. Tests copy this and mutate.
#   - QBP lib root QBP.lean imports Foundations + one Experiments file.
#   - Sprint12 lib (its own srcDir) with one root file.
#   - an `oracle` exe whose root reaches an Oracle file not imported by QBP.lean.
BASE_FILES = {
    "lakefile.lean": (
        "import Lake\n"
        "open Lake DSL\n\n"
        "package «T» where\n\n"
        "@[default_target]\n"
        "lean_lib «QBP» where\n"
        "  roots := #[`QBP]\n\n"
        "@[default_target]\n"
        "lean_lib «QBPSprint12» where\n"
        '  srcDir := "Sprint12-Inherited"\n'
        "  roots := #[`S1]\n\n"
        "lean_exe «oracle» where\n"
        "  root := `QBP.Oracle.Main\n"
    ),
    "QBP.lean": "import QBP.Foundations\nimport QBP.Experiments.Exp1\n",
    "QBP/Foundations.lean": "import QBP.Foundations.F1\n",
    "QBP/Foundations/F1.lean": "-- foundations leaf\n",
    "QBP/Experiments/Exp1.lean": "-- physics leaf, visible via QBP.lean\n",
    "QBP/Oracle/Main.lean": "import QBP.Oracle.Compute\n-- exe root\n",
    "QBP/Oracle/Compute.lean": "-- visible only via the `oracle` exe root\n",
    "Sprint12-Inherited/S1.lean": "-- Sprint12 lib root, visible\n",
}


def run(files):
    """Write `files` under a temp proofs/ and return (returncode, stdout)."""
    with tempfile.TemporaryDirectory() as d:
        proofs = os.path.join(d, "proofs")
        for rel, content in files.items():
            p = os.path.join(proofs, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(content)
        res = subprocess.run(
            [sys.executable, SCRIPT, "--proofs", proofs],
            capture_output=True,
            text=True,
        )
        return res.returncode, res.stdout


def with_quarantine(files, entries):
    files = dict(files)
    files["QBP/.build-visibility-quarantine.json"] = json.dumps({"entries": entries})
    return files


def main():
    passed = 0

    def check(name, cond):
        nonlocal passed
        assert cond, f"FAILED: {name}"
        passed += 1

    # 0. Baseline: the clean synthetic tree passes all rules.
    rc, out = run(BASE_FILES)
    check("clean tree passes", rc == 0)

    # 1. ADVERSARIAL (#625 AC2): a planted, unreferenced physics file is flagged.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Orphan.lean"] = "-- not imported by anything\n"
    rc, out = run(files)
    check("planted invisible physics file fails", rc == 1)
    check("planted file named in the violation", "QBP/Experiments/Orphan.lean" in out)
    check("violation explains build-invisibility", "build-invisible" in out)

    # 2. Sprint12 coverage (#625 AC1): a non-root, unreferenced Sprint12 file is flagged.
    files = dict(BASE_FILES)
    files["Sprint12-Inherited/Orphan.lean"] = "-- not a lib root, imported by nothing\n"
    rc, out = run(files)
    check("planted invisible Sprint12 file fails", rc == 1)
    check("Sprint12 orphan named", "Sprint12-Inherited/Orphan.lean" in out)

    # 3. Transitive visibility: a physics file reached only via another visible
    #    physics file (not directly by QBP.lean) is visible — guards against a
    #    naive direct-import-only check.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Exp1.lean"] = "import QBP.Experiments.Exp2\n"
    files["QBP/Experiments/Exp2.lean"] = "-- reached transitively via Exp1\n"
    rc, out = run(files)
    check("transitively-reachable physics file passes", rc == 0)

    # 4. exe-root reachability: a file reachable only via a lean_exe root is visible.
    #    (Compute is in BASE, reached via the `oracle` exe root, not QBP.lean.)
    #    Prove it matters: drop the exe target and Compute becomes invisible.
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"].replace(
        "lean_exe «oracle» where\n  root := `QBP.Oracle.Main\n", ""
    )
    rc, out = run(files)
    check("dropping the exe target makes its files invisible", rc == 1)
    check("Oracle files flagged when exe target gone", "QBP/Oracle/" in out)

    # 5. Quarantine lets a known-invisible file pass (with issue + reason).
    files = dict(BASE_FILES)
    files["QBP/Experiments/Orphan.lean"] = "-- intentionally unwired\n"
    files = with_quarantine(
        files,
        [{"file": "QBP/Experiments/Orphan.lean", "reason": "tracked", "issue": "#644"}],
    )
    rc, out = run(files)
    check("quarantined invisible file passes", rc == 0)

    # 6. A quarantine entry with no issue is rejected (no silent baselining).
    files = dict(BASE_FILES)
    files["QBP/Experiments/Orphan.lean"] = "-- intentionally unwired\n"
    files = with_quarantine(
        files, [{"file": "QBP/Experiments/Orphan.lean", "reason": "tracked"}]
    )
    rc, out = run(files)
    check("quarantine entry with no issue fails", rc == 1)
    check("no-issue violation explained", "no 'issue'" in out)

    # 7. Stale quarantine: a listed file that is actually build-visible must be removed.
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Experiments/Exp1.lean", "reason": "stale", "issue": "#644"}],
    )
    rc, out = run(files)
    check("stale (now-visible) quarantine entry fails", rc == 1)
    check("stale-visible violation explained", "stale quarantine entry" in out)

    # 8. Stale quarantine: a listed file that no longer exists must be removed.
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Experiments/Gone.lean", "reason": "deleted", "issue": "#644"}],
    )
    rc, out = run(files)
    check("stale (missing-file) quarantine entry fails", rc == 1)
    check("missing-file violation explained", "does not exist" in out)

    # 9. Quarantine may only govern the enforced tree (not e.g. Foundations).
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Foundations/F1.lean", "reason": "wrong scope", "issue": "#644"}],
    )
    rc, out = run(files)
    check("quarantine outside enforced dir fails", rc == 1)
    check("out-of-scope violation explained", "not under an enforced dir" in out)

    # 10. Rule-2 regression: a physics file importing QBP.Substrate is still caught.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Exp1.lean"] = "import QBP.Substrate.AC1\n"
    rc, out = run(files)
    check("physics importing Substrate fails", rc == 1)
    check("forbidden-import violation explained", "forbidden" in out)

    print(f"check_layer_imports: {passed}/{passed} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
