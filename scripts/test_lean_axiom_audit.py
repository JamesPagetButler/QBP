#!/usr/bin/env python3
"""Planted end-to-end test of the CI axiom audit (QBP #827 AC2) on real Lean, core only.

Compiles the fixture modules in `scripts/lean_audit_fixtures/` (they import nothing but Lean
core, so this takes seconds and needs no Mathlib), generates the auditor's arguments for them
with `gen_lean_axiom_audit.py --modules`, runs `lean --run scripts/LeanAxiomAudit.lean` exactly
as CI does (LEAN_PATH unset, project path in QBP_AUDIT_LEAN_PATH), and grades the output with
`check_lean_axiom_audit.py`:

  * AuditFixture.Clean  → must PASS (standard axioms only; theorem, def, instance, inductive);
  * AuditFixture.Bad    → must FAIL, naming EXACTLY the planted declarations: the KL03 string
    trick `hidden_native` (native_decide behind a "/-" string), `by_sorry`, `by_cheat` and
    the axiom `cheat` itself, and the DEF `sorried_value` (coverage is every declaration,
    not only theorems with a `#print axioms`). The module also PRINTS fake clean
    "SUMMARY … bad=0" / "does not depend on any axioms" lines (MF06-style); they must not
    change the verdict;
  * allowlist (#827 option (a)): an allowlisted native_decide declaration passes; the same
    declaration without an entry fails; a SECOND native_decide in the allowlisted file fails;
    a STALE entry fails; an entry naming the wrong axiom does not allow; a wildcard is rejected;
    a theorem that USES the excepted declaration fails (the gate is transitive — Cartan seq 5688);
  * injection (PR #829 Gemini r1 finding 1): AuditFixture.Inject exports a high-priority `!`
    macro and an `initialize` printing a fake clean summary (this PASSED the first,
    in-environment driver on Lean 4.30.0); AuditFixture.InjectId exports `BEq Name` /
    `HAdd Nat Nat Nat` overrides and a same-named helper in the driver's old opened namespace.
    Each must FAIL naming exactly its planted `sorry` theorem;
  * forged output: a clean result appended to the Bad run's output (right nonce), or replacing
    it with a wrong nonce, must turn the verdict into FAIL, never into a pass.

usage: test_lean_axiom_audit.py [--lean PATH]   (default: `lean` on PATH)
Exit 0 = every planted case behaved; 1 = regression.
"""

from __future__ import annotations

import argparse
import json
import os
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
EXPECT_INJECT = {
    "AuditFixture.Inject": {"AuditFixture.Inject.by_sorry"},
    "AuditFixture.InjectId": {"AuditFixture.InjectId.by_sorry"},
}
FIXTURES = ("Clean", "Bad", "AllowOne", "AllowTwo", "AllowDep", "Inject", "InjectId")


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def ns(prefix: str, name: str) -> str:
    return f"AuditFixture.{prefix}.{name}"


def native_entries(prefix: str, name: str, issue: int = 582) -> list[dict]:
    """Allowlist entries for one native_decide theorem: the theorem and its per-call axiom."""
    ax = f"{ns(prefix, name)}._native.native_decide.ax_1_1"
    return [
        {
            "declaration": ns(prefix, name),
            "axioms": [ax],
            "issue": issue,
            "reason": "planted test",
        },
        {"declaration": ax, "axioms": [ax], "issue": issue, "reason": "planted test"},
    ]


def audit(
    lean: str, work: Path, mod: str, env: dict, allowlist: list[dict] | None = None
) -> tuple[int, dict, str]:
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
    for f in sorted(drv.glob("AxiomAudit_*.args")):
        args = f.read_text(encoding="utf-8").splitlines()
        # As in CI: LEAN_PATH unset (the auditor is elaborated against the toolchain only), the
        # project's search path handed over in QBP_AUDIT_LEAN_PATH.
        aenv = {k: v for k, v in env.items() if k != "LEAN_PATH"}
        aenv["QBP_AUDIT_LEAN_PATH"] = env["LEAN_PATH"]
        out = run([lean, "--run", str(HERE / "LeanAxiomAudit.lean"), *args], env=aenv)
        f.with_suffix(".out").write_text(out.stdout)
        if out.returncode != 0:
            print(f"     auditor exit {out.returncode}: {out.stderr[:600]}")
    al = ""
    if allowlist is not None:
        p = work / f"allow-{mod}-{len(allowlist)}.json"
        p.write_text(json.dumps({"entries": allowlist}))
        al = str(p)
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
            "--allowlist",
            al,
        ]
    )
    return c.returncode, json.loads(rj.read_text()), c.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default=shutil.which("lean") or "lean")
    a = ap.parse_args()
    bad = 0

    def report(good: bool, what: str, out: str = "") -> None:
        nonlocal bad
        print(("ok  " if good else "FAIL") + " " + what)
        if not good and out:
            print(out)
        bad += not good

    with tempfile.TemporaryDirectory() as td:
        work = Path(td)
        build = work / "build" / "AuditFixture"
        build.mkdir(parents=True)
        env = {
            "LEAN_PATH": str(work / "build"),
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": os.environ.get("HOME", "/tmp"),
        }
        for m in FIXTURES:
            r = run(
                [
                    a.lean,
                    f"--root={FIX}",
                    "-o",
                    str(build / f"{m}.olean"),
                    str(FIX / "AuditFixture" / f"{m}.lean"),
                ],
                env=env,
            )
            if r.returncode != 0:
                print(f"FAIL compiling fixture {m}:\n{r.stdout}{r.stderr}")
                return 1

        # The lexer fixtures of test_check_lean_foundations.py (PR #829 findings 2/3) are REAL
        # Lean, and Lean sees the declaration the first Python lexer hid in a fake comment.
        lex = HERE / "lean_lexer_fixtures"
        (work / "build" / "LexFix").mkdir(parents=True)
        for f in sorted((lex / "LexFix").glob("*.lean")):
            mod = f"LexFix.{f.stem}"
            r = run(
                [
                    a.lean,
                    f"--root={lex}",
                    "-o",
                    str(work / "build" / "LexFix" / f"{f.stem}.olean"),
                    str(f),
                ],
                env=env,
            )
            decl = "honest" if f.stem == "LegitRaw" else "vac"
            probe = work / f"Probe{f.stem}.lean"
            probe.write_text(f"import {mod}\n#check @{mod}.{decl}\n", encoding="utf-8")
            p = run([a.lean, str(probe)], env=env) if r.returncode == 0 else r
            report(
                r.returncode == 0 and p.returncode == 0,
                f"lexer fixture {mod} compiles and Lean sees `{decl}` as a declaration",
                r.stdout + r.stderr + p.stdout + p.stderr,
            )

        rc, res, out = audit(a.lean, work, "AuditFixture.Clean", env)
        report(
            rc == 0 and not res["non_standard"] and not res["errors"],
            f"Clean fixture passes (exit {rc})",
            out,
        )

        rc, res, out = audit(a.lean, work, "AuditFixture.Bad", env)
        found = {d for d, _ in res["non_standard"]}
        report(
            rc == 1 and found == EXPECT_BAD and not res["errors"],
            f"Bad fixture fails naming exactly the planted declarations (exit {rc}): {sorted(found)}",
            out,
        )

        # PR #829 Gemini r1 finding 1. Inject: a high-priority `!` macro + an `initialize`
        # printing a fake clean summary — against the first (in-environment) driver this PASSED
        # (reproduced on 4.30.0). InjectId: `BEq Name` / `HAdd Nat Nat Nat` overrides and a
        # same-named helper in the driver's opened namespace. Each must FAIL naming exactly its
        # planted `sorry` theorem, with no other error: the auditor never sees the module's
        # syntax and never runs its code.
        for mod, want in EXPECT_INJECT.items():
            rc, res, out = audit(a.lean, work, mod, env)
            found = {d for d, _ in res["non_standard"]}
            report(
                rc == 1 and found == want and not res["errors"],
                f"injection fixture {mod} fails closed (exit {rc}): {sorted(found)}",
                out,
            )

        # Allowlist (director ruling on #827, option (a)): exact, per-declaration, issue-linked.
        rc, res, out = audit(
            a.lean,
            work,
            "AuditFixture.AllowOne",
            env,
            native_entries("AllowOne", "allowed_native"),
        )
        report(
            rc == 0
            and len(res["allowlisted"]) == 2
            and not res["non_standard"]
            and not res["errors"],
            f"allowlisted native_decide declaration passes (exit {rc})",
            out,
        )
        rc, res, out = audit(a.lean, work, "AuditFixture.AllowOne", env)
        report(
            rc == 1,
            f"the same declaration WITHOUT an allowlist entry fails (exit {rc})",
            out,
        )
        rc, res, out = audit(
            a.lean,
            work,
            "AuditFixture.AllowTwo",
            env,
            native_entries("AllowTwo", "allowed_native"),
        )
        found = {d for d, _ in res["non_standard"]}
        want = {
            ns("AllowTwo", "second_native"),
            ns("AllowTwo", "second_native") + "._native.native_decide.ax_1_1",
        }
        report(
            rc == 1 and found == want and len(res["allowlisted"]) == 2,
            f"a SECOND native_decide in the allowlisted file fails (exit {rc}): {sorted(found)}",
            out,
        )
        # TRANSITIVITY (Cartan, seq 5688): a theorem USING the excepted declaration inherits its
        # native axiom and must fail; only the exactly-named declaration (+ its axiom) is allowed.
        rc, res, out = audit(
            a.lean,
            work,
            "AuditFixture.AllowDep",
            env,
            native_entries("AllowDep", "allowed_native"),
        )
        found = {d for d, _ in res["non_standard"]}
        # The failure comes from rule 1 alone (any axiom outside the standard three, no entry of
        # its own) — NOT from matching a native-axiom name; the "inherits …" text is only a hint.
        report(
            rc == 1
            and found == {ns("AllowDep", "uses_allowed")}
            and len(res["allowlisted"]) == 2,
            f"a theorem USING the excepted declaration fails — the gate is transitive (exit {rc}): {sorted(found)}",
            out,
        )
        stale = native_entries("Clean", "gone")
        rc, res, out = audit(a.lean, work, "AuditFixture.Clean", env, stale)
        report(
            rc == 1 and any("STALE allowlist entry" in e for e in res["errors"]),
            f"a STALE allowlist entry fails (exit {rc})",
            out,
        )
        wrong_ax = [
            dict(e, axioms=["sorryAx"])
            for e in native_entries("AllowOne", "allowed_native")
        ]
        rc, res, out = audit(a.lean, work, "AuditFixture.AllowOne", env, wrong_ax)
        report(
            rc == 1,
            f"an entry naming the WRONG axiom does not allow it (exit {rc})",
            out,
        )
        wild = [
            {
                "declaration": "AuditFixture.AllowOne.*",
                "axioms": ["*"],
                "issue": 582,
                "reason": "wildcard",
            }
        ]
        rc, res, out = audit(a.lean, work, "AuditFixture.AllowOne", env, wild)
        report(
            rc == 1 and any("malformed allowlist entry" in e for e in res["errors"]),
            f"a wildcard entry is rejected (exit {rc})",
            out,
        )

        # Forged auditor output on the Bad module's run -> must FAIL, never pass:
        #   (1) a well-formed CLEAN result with the right nonce appended (two results);
        #   (2) the real output replaced by a clean result with a wrong nonce (a file planted
        #       before this generation, e.g. by build-time code).
        drv = work / "drv-AuditFixture.Bad"
        d0 = json.loads((drv / "manifest.json").read_text())["drivers"][0]
        outp = Path(d0["output"])
        real = outp.read_text()
        clean = {
            "mark": "AXIOM-AUDIT-827",
            "nonce": d0["nonce"],
            "root": d0["label"],
            "targets": d0["modules"],
            "missing": [],
            "declarations": 9,
            "nonstd": [],
        }
        for what, text in (
            ("a forged clean result appended", real + json.dumps(clean) + "\n"),
            (
                "the output replaced by a clean result with a WRONG nonce",
                json.dumps(dict(clean, nonce="0" * 32)) + "\n",
            ),
        ):
            outp.write_text(text)
            rj = work / "result-forged.json"
            c = run(
                [
                    sys.executable,
                    "-I",
                    str(HERE / "check_lean_axiom_audit.py"),
                    "--manifest",
                    str(drv / "manifest.json"),
                    "--allowlist",
                    "",
                    "--json",
                    str(rj),
                ]
            )
            res = json.loads(rj.read_text())
            report(
                c.returncode == 1 and len(res["errors"]) == 1,
                f"{what} makes the audit FAIL, not pass (exit {c.returncode}, {len(res['errors'])} error)",
                c.stdout,
            )
    print("axiom-audit planted tests " + ("PASSED" if not bad else f"FAILED ({bad})"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
