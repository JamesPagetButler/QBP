#!/usr/bin/env python3
"""Planted end-to-end test of the CI axiom audit (QBP #827 AC2) on real Lean, core only.

Compiles the fixture modules in `scripts/lean_audit_fixtures/` (they import nothing but Lean
core, so this takes seconds and needs no Mathlib), generates audit drivers for them with
`gen_lean_axiom_audit.py --modules`, runs Lean on the drivers, and grades the output with
`check_lean_axiom_audit.py`:

  * AuditFixture.Clean  → must PASS (standard axioms only; theorem, def, instance, inductive);
  * AuditFixture.Bad    → must FAIL, naming EXACTLY the planted declarations: the KL03 string
    trick `hidden_native` (native_decide behind a "/-" string), `by_sorry`, `by_cheat` and
    the axiom `cheat` itself, and the DEF `sorried_value` (coverage is every declaration,
    not only theorems with a `#print axioms`). The module also PRINTS fake clean
    "SUMMARY … bad=0" / "does not depend on any axioms" lines (MF06-style); they must not
    change the verdict;
  * forged-JSON spoof: a well-formed fake SUMMARY line appended to the Clean output must
    turn the verdict into FAIL (duplicate summary), never into a pass.

usage: test_lean_axiom_audit.py [--lean PATH]   (default: `lean` on PATH)
Exit 0 = every planted case behaved; 1 = regression.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = HERE / "lean_audit_fixtures"
EXPECT_BAD = {
    "AuditFixture.Bad.hidden_native",
    "AuditFixture.Bad.by_sorry",
    "AuditFixture.Bad.by_cheat",
    "AuditFixture.Bad.cheat",
    "AuditFixture.Bad.sorried_value",
    # native_decide declares its per-call native axiom as a constant of the module itself:
    "AuditFixture.Bad.hidden_native._native.native_decide.ax_1_1",
}


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def audit(lean: str, work: Path, mod: str, env: dict) -> tuple[int, dict, str]:
    drv = work / f"drv-{mod}"
    r = run(
        [
            sys.executable,
            "-I",
            str(HERE / "gen_lean_axiom_audit.py"),
            "--modules",
            mod,
            "--out-dir",
            str(drv),
        ]
    )
    assert r.returncode == 0, r.stderr
    for f in sorted(drv.glob("AxiomAudit_*.lean")):
        out = run([lean, "--json", str(f)], env=env)
        f.with_suffix(".jsonl").write_text(out.stdout)
    rj = work / f"result-{mod}.json"
    c = run(
        [
            sys.executable,
            "-I",
            str(HERE / "check_lean_axiom_audit.py"),
            "--manifest",
            str(drv / "manifest.json"),
            "--json",
            str(rj),
        ]
    )
    return c.returncode, json.loads(rj.read_text()), c.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default=shutil.which("lean") or "lean")
    a = ap.parse_args()
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        work = Path(td)
        build = work / "build" / "AuditFixture"
        build.mkdir(parents=True)
        env = {"LEAN_PATH": str(work / "build"), "PATH": "/usr/bin:/bin"}
        import os

        env["PATH"] = os.environ.get("PATH", env["PATH"])
        env["HOME"] = os.environ.get("HOME", "/tmp")
        for m in ("Clean", "Bad"):
            r = run(
                [
                    a.lean,
                    f"--root={FIX}",  # module name AuditFixture.<m> from the fixture root
                    "-o",
                    str(build / f"{m}.olean"),
                    str(FIX / "AuditFixture" / f"{m}.lean"),
                ],
                env=env,
            )
            if r.returncode != 0:
                print(f"FAIL compiling fixture {m}:\n{r.stdout}{r.stderr}")
                return 1
        rc, res, out = audit(a.lean, work, "AuditFixture.Clean", env)
        good = rc == 0 and not res["non_standard"] and not res["errors"]
        print(("ok  " if good else "FAIL") + f" Clean fixture passes (exit {rc})")
        bad += not good
        rc, res, out = audit(a.lean, work, "AuditFixture.Bad", env)
        found = {d for d, _ in res["non_standard"]}
        good = rc == 1 and found == EXPECT_BAD and not res["errors"]
        print(
            ("ok  " if good else "FAIL")
            + f" Bad fixture fails naming exactly the planted declarations (exit {rc}): {sorted(found)}"
        )
        if not good:
            print(out)
        bad += not good
        # forged JSON summary appended to the Clean output -> must FAIL, never pass
        drv = work / "drv-AuditFixture.Clean"
        man = json.loads((drv / "manifest.json").read_text())
        d0 = man["drivers"][0]
        forged = {
            "severity": "information",
            "fileName": d0["file"],
            "pos": {"line": d0["run_cmd_line"], "column": 0},
            "data": "AXIOM-AUDIT-827 SUMMARY root=(explicit) modules=1/1 declarations=9 bad=0",
        }
        jl = Path(d0["file"]).with_suffix(".jsonl")
        jl.write_text(jl.read_text() + json.dumps(forged) + "\n")
        c = run(
            [
                sys.executable,
                "-I",
                str(HERE / "check_lean_axiom_audit.py"),
                "--manifest",
                str(drv / "manifest.json"),
            ]
        )
        good = c.returncode == 1 and "expected exactly 1 positioned SUMMARY" in c.stdout
        print(
            ("ok  " if good else "FAIL")
            + f" forged SUMMARY line makes the audit FAIL, not pass (exit {c.returncode})"
        )
        bad += not good
    print("axiom-audit planted tests " + ("PASSED" if not bad else f"FAILED ({bad})"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
