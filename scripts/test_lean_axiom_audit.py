#!/usr/bin/env python3
"""Planted end-to-end test of the CI axiom audit (QBP #827 AC2, PR #829) on real Lean, core only.

Compiles the fixture modules in `scripts/lean_audit_fixtures/` (they import nothing but Lean
core, so this takes minutes at most and needs no Mathlib), generates the auditor's arguments
with `gen_lean_axiom_audit.py --modules`, runs `lean --run scripts/LeanAxiomAudit.lean` exactly
as CI does (LEAN_PATH unset, project path in QBP_AUDIT_LEAN_PATH, the fixture build directory as
the project scope), and grades the output with `check_lean_axiom_audit.py`. Every case asserts
the exit code and the EXACT failing set / error count, never message wording:

  * Clean passes; Bad fails naming exactly its planted declarations (native_decide behind a
    "/-" string, sorry, a user axiom and its user, a sorried DEF);
  * EXACT CLOSURE (Red Team 9): on Bad, Cycle (inductive <-> constructor cycle), AllowTwo and
    AllowDep the auditor's failing set equals the set Lean's own `collectAxioms` gives;
  * INJECTION (Gemini r1 1, Red Team 1-2): Inject (`!` macro, an `initialize` that prints a
    forged summary and one that calls `IO.Process.exit 0`) and InjectId (`BEq Name` / `HAdd Nat`
    overrides, a same-named helper, `macro_rules` rewriting `run_cmd`) each fail naming exactly
    their `sorry` theorem, with no other error;
  * SCOPE (Red Team 4): ScopeRoot imports ScopeA and ScopeHidden on ONE line; Lean's scope must
    include ScopeHidden, so its `sorry` fails the audit;
  * ALLOWLIST (#827 option (a); Red Team 3, M2, M13): a pinned native_decide declaration passes;
    no entry fails; a second native_decide fails; a dependent fails (transitive); a name
    extending the entry fails; an entry never allows a superset; a FORGED same-named
    declaration + axiom in another module fails; a wrong fingerprint or module pin fails; a
    stale entry, a wrong-axiom entry and a wildcard entry fail;
  * TRUST (M5, M6, M11, M12 and the M8-M10 analogues): no runs, an import error, and forged
    outputs (appended duplicate, wrong nonce, wrong root, zero declarations, a missing module, a
    scope lacking a module, an unresolved module, a malformed entry) each fail;
  * the lexer fixtures of test_check_lean_foundations.py compile, and Lean sees the declaration
    the first Python lexer hid.

usage: test_lean_axiom_audit.py [--lean PATH]   (default: `lean` on PATH)
Exit 0 = every planted case behaved; 1 = regression.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = HERE / "lean_audit_fixtures"
AX = "._native.native_decide.ax_1_1"
EXPECT_BAD = {
    "AuditFixture.Bad.hidden_native",
    "AuditFixture.Bad.by_sorry",
    "AuditFixture.Bad.by_cheat",
    "AuditFixture.Bad.cheat",
    "AuditFixture.Bad.sorried_value",
    # native_decide declares its per-call native axiom as a constant of the module itself:
    "AuditFixture.Bad.hidden_native" + AX,
}
EXPECT_INJECT = {
    "AuditFixture.Inject": {"AuditFixture.Inject.by_sorry"},
    "AuditFixture.InjectId": {"AuditFixture.InjectId.by_sorry"},
}
# Build order matters: ScopeRoot imports ScopeA and ScopeHidden.
# Lexer fixtures that Lean 4.30 itself does not compile (PR #829 Gemini r2 F1, P1-P3).
LEAN_REJECTS = {"NumHexRaw", "NumHexChar", "NumSciRaw"}
FIXTURES = (
    "Clean",
    "Bad",
    "AllowOne",
    "AllowTwo",
    "AllowDep",
    "AllowPrefix",
    "AllowPlus",
    "AllowForge",
    "Cycle",
    "Inject",
    "InjectId",
    "ScopeA",
    "ScopeHidden",
    "ScopeRoot",
    "PreludeProp",
    "AllowLit",
    "DangleA",
    "DangleB",
    "OpaqueSorry",
    "VacB3",
    "VacB4",
    "VacB6",
    "VacB8",
    "VacSpell",
    "VacControl",
    "VacKinds",
    "VacB3Def",
    "VacIrred",
    "VacRec",
    "VacBudget",
    "VacIrredSort",
)
# The ORACLE is Lean's own in-file `collectAxioms` (what `#print axioms` uses), run at the END
# of a copy of the fixture, on the module's own constants (`map₂`). It is NOT computed through an
# import: the per-module axiom data that oleans carry is less complete across an inductive's
# cycle (it calls `Cycle.I` clean), which is exactly why the auditor recomputes the closure.
ORACLE = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  for (n, _) in env.constants.map₂.toList do
    let axs ← collectAxioms n
    if axs.any (fun a => !std.contains a) then logInfo m!"ORACLE {n}"
"""


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def ns(prefix: str, name: str) -> str:
    return f"AuditFixture.{prefix}.{name}"


def sha(t: str) -> str:
    return hashlib.sha256(t.encode("utf-8")).hexdigest()


class Harness:
    def __init__(self, lean: str, work: Path, env: dict) -> None:
        self.lean, self.work, self.env, self.n = lean, work, env, 0
        self.vac_path = str(
            HERE / "lean_vacuity_allowlist.json"
        )  # the real one (empty)

    def gen(self, mods: list[str], allowlist: list[dict] | None) -> tuple[Path, str]:
        self.n += 1
        drv = self.work / f"drv-{self.n}"
        al = ""
        if allowlist is not None:
            p = self.work / f"allow-{self.n}.json"
            p.write_text(json.dumps({"entries": allowlist}))
            al = str(p)
        r = run(
            [
                sys.executable,
                "-I",
                str(HERE / "gen_lean_axiom_audit.py"),
                "--modules",
                *mods,
                "--out-dir",
                str(drv),
                "--project-dir",
                str(self.work / "build"),
                "--allowlist",
                al,
                "--vacuity-allowlist",
                self.vac_path,
            ]
        )
        assert r.returncode == 0, r.stderr
        return drv, al

    def run_auditor(
        self, drv: Path, lean_path: str | None = None, vac_budget: int | None = None
    ) -> None:
        for f in sorted(drv.glob("AxiomAudit_*.args")):
            args = f.read_text(encoding="utf-8").splitlines()
            # As in CI: LEAN_PATH unset (the auditor is elaborated against the toolchain only),
            # the project's search path handed over in QBP_AUDIT_LEAN_PATH.
            aenv = {k: v for k, v in self.env.items() if k != "LEAN_PATH"}
            aenv["QBP_AUDIT_LEAN_PATH"] = lean_path or self.env["LEAN_PATH"]
            if vac_budget is not None:
                aenv["QBP_AUDIT_VACUITY_HEARTBEATS"] = str(vac_budget)
            out = run(
                [self.lean, "--run", str(HERE / "LeanAxiomAudit.lean"), *args], env=aenv
            )
            f.with_suffix(".out").write_text(out.stdout)

    def check(
        self, drv: Path, al: str, build_dirs: list[str] | None = None
    ) -> tuple[int, dict, str]:
        rj = drv / "result.json"
        extra = [x for bd in (build_dirs or []) for x in ("--build-dir", bd)]
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
                "--vacuity-allowlist",
                self.vac_path,
                *extra,
            ]
        )
        return c.returncode, json.loads(rj.read_text()), c.stdout

    def audit(
        self,
        mod: str | list[str],
        allowlist: list[dict] | None = None,
        lean_path: str | None = None,
        build_dirs: list[str] | None = None,
        vacuity: list[dict] | None = None,
        vac_budget: int | None = None,
    ) -> tuple[int, dict, str]:
        self.vac_path = str(HERE / "lean_vacuity_allowlist.json")
        if vacuity is not None:
            self.n += 1
            vp = self.work / f"vac-{self.n}.json"
            vp.write_text(json.dumps({"entries": vacuity}))
            self.vac_path = str(vp)
        drv, al = self.gen([mod] if isinstance(mod, str) else mod, allowlist)
        self.run_auditor(drv, lean_path, vac_budget)
        return self.check(drv, al, build_dirs)

    def pins(self, mod: str, names: list[str]) -> list[dict]:
        """Genuine pinned entries for `names` in `mod` (read back from a first audit run)."""
        dummy = [
            {
                "declaration": n,
                "module": mod,
                "fingerprint": "0" * 64,
                "axioms": [{"name": n, "module": mod, "fingerprint": "0" * 64}],
                "issue": 582,
                "reason": "pin probe",
            }
            for n in names
        ]
        _, res, _ = self.audit(mod, dummy)
        out = []
        for n in names:
            b = next(r for r in res["reports"] if r["decl"] == n)
            out.append(
                {
                    "declaration": n,
                    "module": b["module"],
                    "fingerprint": sha(b["fp"]),
                    "axioms": [
                        {
                            "name": x["name"],
                            "module": x["module"],
                            "fingerprint": sha(x["fp"]),
                        }
                        for x in b["axioms"]
                    ],
                    "issue": 582,
                    "reason": "planted test",
                }
            )
        return out

    def oracle(self, mod: str) -> set[str] | None:
        """Declarations of `mod` that Lean's own `collectAxioms` says rest on a non-standard axiom."""
        self.n += 1
        p = self.work / f"Oracle{self.n}.lean"
        src = (FIX / "AuditFixture" / f"{mod.split('.')[-1]}.lean").read_text(
            encoding="utf-8"
        )
        p.write_text("import Lean\n" + src + ORACLE, encoding="utf-8")
        r = run([self.lean, "--json", str(p)], env=self.env)
        got = set()
        for line in r.stdout.splitlines():
            try:
                m = json.loads(line)
            except json.JSONDecodeError:
                continue
            if m.get("severity") == "error":
                return None
            d = m.get("data", "")
            if d.startswith("ORACLE "):
                got.add(d[len("ORACLE ") :].strip())
        return got


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default=shutil.which("lean") or "lean")
    a = ap.parse_args()
    bad = 0

    def report(good: bool, what: str, out: str = "") -> None:
        nonlocal bad
        print(("ok  " if good else "FAIL") + " " + what)
        if not good and out:
            print(out[-3000:])
        bad += not good
        if not good and os.environ.get("QBP_TEST_FAIL_FAST"):
            sys.exit(1)  # mutation runs: one failing case is a kill

    def found(res: dict) -> set[str]:
        return {d for d, _ in res["non_standard"]}

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
        h = Harness(a.lean, work, env)

        # PR #829 Gemini r2 finding 5: the generator's own paths (no Lean needed).
        # (a) only @[default_target] libraries are roots: a fake tree with a default lib A and a
        #     non-default lib B must give exactly [A] (the default filter is the gate's scope);
        # (b) a module under a toolchain root (`Lean.Evil`) is refused outright.
        fake = work / "fake-proofs"
        fake.mkdir()
        (fake / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage «P» where\n\n"
            "@[default_target]\nlean_lib «A» where\n  roots := #[`A]\n\n"
            "lean_lib «B» where\n  roots := #[`B]\n",
            encoding="utf-8",
        )
        (fake / "A.lean").write_text("theorem a : True := trivial\n", encoding="utf-8")
        (fake / "B.lean").write_text("theorem b : True := trivial\n", encoding="utf-8")
        g = run(
            [
                sys.executable,
                "-I",
                str(HERE / "gen_lean_axiom_audit.py"),
                "--proofs",
                str(fake),
                "--topo",
            ]
        )
        report(
            g.returncode == 0 and g.stdout.split() == ["A"],
            f"generator scope = default targets only (got {g.stdout.split()})",
            g.stdout + g.stderr,
        )
        g = run(
            [
                sys.executable,
                "-I",
                str(HERE / "gen_lean_axiom_audit.py"),
                "--modules",
                "Lean.Evil",
                "--out-dir",
                str(work / "drv-reserved"),
                "--allowlist",
                "",
            ]
        )
        report(
            g.returncode != 0
            and not (work / "drv-reserved" / "manifest.json").exists(),
            f"generator refuses a module under a toolchain root (exit {g.returncode})",
            g.stdout + g.stderr,
        )

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
            if f.stem in LEAN_REJECTS:
                # Gemini r2 F1 shapes P1-P3: Lean 4.30 itself REJECTS them (a function argument
                # needs whitespace before it: "unexpected token; expected command" right after
                # the number), so the forge is not real there; the lexer still refuses them.
                report(
                    r.returncode != 0 and "unexpected token" in r.stdout + r.stderr,
                    f"lexer fixture {mod} is rejected by Lean itself (exit {r.returncode})",
                    r.stdout + r.stderr,
                )
                continue
            decl = "honest" if f.stem == "LegitRaw" else "vac"
            probe = work / f"Probe{f.stem}.lean"
            probe.write_text(f"import {mod}\n#check @{mod}.{decl}\n", encoding="utf-8")
            p = run([a.lean, str(probe)], env=env) if r.returncode == 0 else r
            report(
                r.returncode == 0 and p.returncode == 0,
                f"lexer fixture {mod} compiles and Lean sees `{decl}` as a declaration",
                r.stdout + r.stderr + p.stdout + p.stderr,
            )

        rc, res, out = h.audit("AuditFixture.Clean")
        report(
            rc == 0 and not res["non_standard"] and not res["errors"],
            f"Clean fixture passes (exit {rc})",
            out,
        )
        rc, res, out = h.audit("AuditFixture.Bad")
        report(
            rc == 1 and found(res) == EXPECT_BAD and not res["errors"],
            f"Bad fixture fails naming exactly the planted declarations (exit {rc}): {sorted(found(res))}",
            out,
        )
        bad_drv = work / f"drv-{h.n}"

        # Red Team 9 / M15: the closure is EXACT — it equals Lean's own collectAxioms.
        for mod in (
            "AuditFixture.Bad",
            "AuditFixture.Cycle",
            "AuditFixture.AllowTwo",
            "AuditFixture.AllowDep",
            "AuditFixture.OpaqueSorry",
        ):
            rc, res, out = h.audit(mod)
            want = h.oracle(mod)
            report(
                want is not None and rc == 1 and found(res) == want,
                f"{mod}: failing set equals Lean's collectAxioms set (exit {rc}, {len(found(res))} decls)",
                out + f"\noracle: {sorted(want or [])}\naudit: {sorted(found(res))}",
            )
        rc, res, out = h.audit("AuditFixture.Cycle")
        report(
            {ns("Cycle", "I"), ns("Cycle", "uses_type")} <= found(res),
            "Cycle: the inductive `I` and `uses_type` (through the cycle) are flagged",
            out,
        )

        # Gemini r1 1 / Red Team 1-2: injection and initializers cannot reach the auditor.
        for mod, want in EXPECT_INJECT.items():
            rc, res, out = h.audit(mod)
            report(
                rc == 1 and found(res) == want and not res["errors"],
                f"injection fixture {mod} fails closed (exit {rc}): {sorted(found(res))}",
                out,
            )

        # Red Team r2 finding 2 (T2): an empty `prelude` module named `Init` placed FIRST on the
        # project search path. The toolchain library comes first, so the real `Init` is used and
        # Bad still fails naming exactly its planted declarations, with no other error.
        fake_src = work / "fakeinit-src"
        fake_src.mkdir()
        (fake_src / "Init.lean").write_text("prelude\n", encoding="utf-8")
        fake = work / "fakeinit"
        fake.mkdir()
        r = run(
            [
                a.lean,
                f"--root={fake_src}",
                "-o",
                str(fake / "Init.olean"),
                str(fake_src / "Init.lean"),
            ],
            env=env,
        )
        report(r.returncode == 0, "fake `Init` module compiles", r.stdout + r.stderr)
        rc, res, out = h.audit("AuditFixture.Bad", lean_path=f"{fake}:{work / 'build'}")
        report(
            rc == 1 and found(res) == EXPECT_BAD and not res["errors"],
            f"a fake `Init` first on the project path cannot hide sorryAx (exit {rc}): {len(found(res))} decls",
            out,
        )

        # Red Team r2 finding 3 (T3): a `prelude` module declaring its own `axiom propext : False`.
        # The name `propext` must denote the toolchain's axiom (Init.Core, pinned fingerprint).
        rc, res, out = h.audit("AuditFixture.PreludeProp")
        report(
            rc == 1 and not res["non_standard"] and len(res["errors"]) == 1,
            f"a same-named `propext` from a prelude module fails the standard-axiom pins (exit {rc})",
            out,
        )

        # Red Team r2 finding 4 (T4): coverage fails CLOSED against the build directory. A build
        # directory holding Clean and ScopeA, audited for Clean only, must FAIL (ScopeA built but
        # not audited); audited for both, it passes.
        cov = work / "cov" / "AuditFixture"
        cov.mkdir(parents=True)
        for m in ("Clean", "ScopeA"):
            shutil.copy(build / f"{m}.olean", cov / f"{m}.olean")
        bd = [str(work / "cov")]
        rc, res, out = h.audit("AuditFixture.Clean", build_dirs=bd)
        report(
            rc == 1 and not res["non_standard"] and len(res["errors"]) == 1,
            f"a built module that no run audits fails coverage (exit {rc})",
            out,
        )
        rc, res, out = h.audit(
            ["AuditFixture.Clean", "AuditFixture.ScopeA"], build_dirs=bd
        )
        report(
            rc == 0 and not res["errors"],
            f"every built module audited: coverage passes (exit {rc})",
            out,
        )

        # Red Team r3: DANGLING references fail closed. DangleB uses DangleA.helper; replace
        # DangleA.olean by a compile of a different source without `helper` (an inconsistent
        # .olean set, as in the S1 probe). The reference no longer resolves: the run must FAIL on
        # it (exactly 1 error, no declaration named), never count it as axiom-free.
        rc, res, out = h.audit("AuditFixture.DangleB")
        report(
            rc == 1 and found(res) == {ns("DangleB", "uses"), ns("DangleA", "helper")},
            f"DangleB before the substitution fails on its sorry (exit {rc})",
            out,
        )
        sub = work / "subst-src" / "AuditFixture"
        sub.mkdir(parents=True)
        (sub / "DangleA.lean").write_text(
            "namespace AuditFixture.DangleA\ntheorem other : (1 : Nat) = 1 := rfl\nend AuditFixture.DangleA\n",
            encoding="utf-8",
        )
        r = run(
            [
                a.lean,
                f"--root={sub.parent}",
                "-o",
                str(build / "DangleA.olean"),
                str(sub / "DangleA.lean"),
            ],
            env=env,
        )
        report(
            r.returncode == 0, "substitute DangleA.olean compiles", r.stdout + r.stderr
        )
        rc, res, out = h.audit("AuditFixture.DangleB")
        report(
            rc == 1 and not res["non_standard"] and len(res["errors"]) == 1,
            f"a dangling reference after an .olean substitution fails closed (exit {rc})",
            out,
        )

        # Red Team r3 / mutant N4: change ONE numeric literal of an allowlisted declaration's
        # statement (`≤ 50` -> `≤ 51`), keep the old pins: the pins must no longer match.
        lit = [ns("AllowLit", "allowed_native"), ns("AllowLit", "allowed_native") + AX]
        lit_pins = h.pins("AuditFixture.AllowLit", lit)
        rc, res, out = h.audit("AuditFixture.AllowLit", lit_pins)
        report(
            rc == 0 and sorted(res["allowlisted"]) == sorted(lit),
            f"AllowLit with its genuine pins passes (exit {rc})",
            out,
        )
        lit_src = work / "lit-src" / "AuditFixture"
        lit_src.mkdir(parents=True)
        (lit_src / "AllowLit.lean").write_text(
            (FIX / "AuditFixture" / "AllowLit.lean")
            .read_text(encoding="utf-8")
            .replace("(List.range 10).sum ≤ 50", "(List.range 10).sum ≤ 51"),
            encoding="utf-8",
        )
        r = run(
            [
                a.lean,
                f"--root={lit_src.parent}",
                "-o",
                str(build / "AllowLit.olean"),
                str(lit_src / "AllowLit.lean"),
            ],
            env=env,
        )
        report(
            r.returncode == 0,
            "AllowLit with one literal changed compiles",
            r.stdout + r.stderr,
        )
        rc, res, out = h.audit("AuditFixture.AllowLit", lit_pins)
        report(
            rc == 1 and found(res) == set(lit) and not res["allowlisted"],
            f"one numeric literal changed: the old pins no longer allow it (exit {rc})",
            out,
        )

        # PR #829 Red Team r6 (director's option (b)): SEMANTIC VACUITY. B3/B4/B6/B8 declare a token
        # (binder_predicate, run_cmd + parsed notation, @[term_parser], #eval in CommandElabM) and
        # hide `theorem vac : True` from the Python token gate, which PASSES them (shown first, so
        # the catch below is the vacuity check's alone). The axiom audit — which never uses the token
        # gate — must FAIL each one, naming exactly `vac` as vacuous (1 error, no axiom issue).
        for fx in ("VacB3", "VacB4", "VacB6", "VacB8", "VacB3Def"):
            fdir = work / f"gate-{fx}"
            fdir.mkdir()
            shutil.copy(FIX / "AuditFixture" / f"{fx}.lean", fdir / f"{fx}.lean")
            base = work / f"gate-{fx}.json"
            base.write_text(json.dumps({"sorry": 0, "vacuous-`: True :=` theorem": 0}))
            g = run(
                [
                    sys.executable,
                    "-I",
                    str(HERE / "check_lean_foundations.py"),
                    "--dir",
                    str(fdir),
                    "--baseline",
                    str(base),
                ]
            )
            report(
                g.returncode == 0,
                f"{fx}: the token gate is fooled (exit {g.returncode})",
                g.stdout,
            )
            rc, res, out = h.audit(f"AuditFixture.{fx}")
            report(
                rc == 1
                and res["vacuous"] == [ns(fx, "vac")]
                and not res["non_standard"]
                and len(res["errors"]) == 1,
                f"{fx}: the semantic vacuity check FAILS exactly `vac` (exit {rc}): {res['vacuous']}",
                out,
            )
        spell = [ns("VacSpell", f"v{k}") for k in range(1, 8)]
        rc, res, out = h.audit("AuditFixture.VacSpell")
        report(
            rc == 1 and res["vacuous"] == sorted(spell) and len(res["errors"]) == 7,
            f"VacSpell: (True), id True, True ∧ True, ∀ n, True, a def, p → True, True ↔ True all flagged (exit {rc})",
            out,
        )
        rc, res, out = h.audit("AuditFixture.VacControl")
        report(
            rc == 0 and not res["vacuous"] and not res["errors"],
            f"VacControl: real statements proved by trivial / rfl pass (exit {rc})",
            out,
        )
        # Red Team r7: every Prop-typed constant (def / abbrev / opaque / noncomputable def), `.all`
        # transparency (@[irreducible]), recursion (structural; well-founded) — each flagged exactly.
        for fx, want_v in (
            ("VacKinds", ["vd", "va", "vo", "vn"]),
            ("VacIrred", ["vi"]),
            ("VacRec", ["r0", "r3", "w2"]),
            ("VacIrredSort", ["vac", "vac2"]),
        ):
            rc, res, out = h.audit(f"AuditFixture.{fx}")
            exp_v = sorted(ns(fx, w) for w in want_v)
            report(
                rc == 1
                and res["vacuous"] == exp_v
                and len(res["errors"]) == len(exp_v),
                f"{fx}: exactly {want_v} flagged vacuous (exit {rc}): {res['vacuous']}",
                out,
            )
        # Heartbeat enforcement (Gemini r5; Red Team r7 finding 6, mutants X1/X3): the exponential
        # ∧-chain `big` is decided (vacuous) with the default budget; with a budget of 1 heartbeat the
        # real auditor must report it UNDECIDED, which fails the run — never pass it, never drop it.
        rc, res, out = h.audit("AuditFixture.VacBudget")
        report(
            rc == 1
            and res["vacuous"] == [ns("VacBudget", "big")]
            and len(res["errors"]) == 1,
            f"VacBudget, default budget: `big` decided vacuous (exit {rc})",
            out,
        )
        rc, res, out = h.audit("AuditFixture.VacBudget", vac_budget=1)
        report(
            rc == 1
            and not res["vacuous"]
            and len(res["errors"]) == 1
            and "could not decide" in res["errors"][0]
            and ns("VacBudget", "big") in res["errors"][0],
            f"VacBudget, 1-heartbeat budget: `big` UNDECIDED, the run fails closed (exit {rc})",
            out,
        )

        # The vacuity allowlist: an entry pinned to module + fingerprint allows exactly that theorem;
        # a wrong fingerprint does not; a stale entry fails.
        dummy = [
            {
                "declaration": spell[0],
                "module": "AuditFixture.VacSpell",
                "fingerprint": "0" * 64,
                "issue": 1,
                "reason": "probe",
            }
        ]
        rc, res, out = h.audit("AuditFixture.VacSpell", vacuity=dummy)
        fp = next(x["fp"] for x in res["vacuous_reports"] if x["decl"] == spell[0])
        pin = [dict(dummy[0], fingerprint=sha(fp))]
        rc, res, out = h.audit("AuditFixture.VacSpell", vacuity=pin)
        report(
            rc == 1
            and res["vacuous_allowed"] == [spell[0]]
            and res["vacuous"] == sorted(spell[1:])
            and len(res["errors"]) == 6,
            f"a pinned vacuity entry allows exactly its theorem (exit {rc})",
            out,
        )
        rc, res, out = h.audit("AuditFixture.VacSpell", vacuity=dummy)
        report(
            rc == 1 and not res["vacuous_allowed"] and len(res["errors"]) == 8,
            f"a wrong vacuity fingerprint does not allow it, and the entry is stale (exit {rc})",
            out,
        )
        # Red Team r7 X6: the right fingerprint under a WRONG module does not allow it.
        rc, res, out = h.audit(
            "AuditFixture.VacSpell",
            vacuity=[dict(pin[0], module="AuditFixture.Elsewhere")],
        )
        report(
            rc == 1 and not res["vacuous_allowed"] and len(res["errors"]) == 8,
            f"a vacuity entry with the right fingerprint but the wrong module does not allow it (exit {rc})",
            out,
        )
        # Gemini r5: a DUPLICATE vacuity entry is an error even when both copies match.
        rc, res, out = h.audit("AuditFixture.VacSpell", vacuity=[pin[0], pin[0]])
        report(
            rc == 1
            and res["vacuous_allowed"] == [spell[0]]
            and len(res["errors"]) == 7,
            f"a duplicate vacuity entry is refused (exit {rc}, {len(res['errors'])} errors)",
            out,
        )

        # Red Team 4: two imports on one line — Lean's scope includes the hidden module.
        rc, res, out = h.audit("AuditFixture.ScopeRoot")
        report(
            rc == 1
            and found(res) == {ns("ScopeHidden", "by_sorry")}
            and "AuditFixture.ScopeHidden" in res["modules"]
            and not res["errors"],
            f"one-line `import A import Hidden`: Hidden is audited and fails (exit {rc}): {sorted(found(res))}",
            out,
        )

        # Allowlist (director ruling on #827, option (a)): exact, pinned, issue-linked.
        one = [ns("AllowOne", "allowed_native"), ns("AllowOne", "allowed_native") + AX]
        pinned = h.pins("AuditFixture.AllowOne", one)
        rc, res, out = h.audit("AuditFixture.AllowOne", pinned)
        report(
            rc == 0
            and sorted(res["allowlisted"]) == sorted(one)
            and not res["non_standard"]
            and not res["errors"],
            f"pinned native_decide declaration passes (exit {rc})",
            out,
        )
        rc, res, out = h.audit("AuditFixture.AllowOne")
        report(
            rc == 1 and found(res) == set(one),
            f"the same declaration WITHOUT an entry fails (exit {rc})",
            out,
        )
        # Red Team 3 / probe e4: a FORGED same-named theorem + axiom in another module.
        rc, res, out = h.audit("AuditFixture.AllowForge", pinned)
        report(
            rc == 1
            and found(res) == set(one)
            and not res["allowlisted"]
            and len(res["errors"]) == 2,
            f"FORGED same-named declaration + axiom fails the pins (exit {rc}): {sorted(found(res))}",
            out,
        )
        for what, mutate in (
            (
                "a wrong declaration fingerprint",
                lambda e: dict(e, fingerprint="1" * 64),
            ),
            ("a wrong module pin", lambda e: dict(e, module="AuditFixture.Elsewhere")),
            (
                "a wrong axiom fingerprint",
                lambda e: dict(
                    e, axioms=[dict(x, fingerprint="2" * 64) for x in e["axioms"]]
                ),
            ),
        ):
            rc, res, out = h.audit(
                "AuditFixture.AllowOne", [mutate(pinned[0]), pinned[1]]
            )
            report(
                rc == 1 and found(res) == {one[0]} and res["allowlisted"] == [one[1]],
                f"{what} does not allow the declaration (exit {rc})",
                out,
            )
        two = [ns("AllowTwo", "allowed_native"), ns("AllowTwo", "allowed_native") + AX]
        rc, res, out = h.audit(
            "AuditFixture.AllowTwo", h.pins("AuditFixture.AllowTwo", two)
        )
        report(
            rc == 1
            and found(res)
            == {ns("AllowTwo", "second_native"), ns("AllowTwo", "second_native") + AX}
            and sorted(res["allowlisted"]) == sorted(two),
            f"a SECOND native_decide in the allowlisted file fails (exit {rc}): {sorted(found(res))}",
            out,
        )
        # TRANSITIVITY (Cartan, seq 5688): a dependent of the excepted declaration fails by
        # rule 1 alone (it has no entry), never by matching an axiom name.
        dep = [ns("AllowDep", "allowed_native"), ns("AllowDep", "allowed_native") + AX]
        rc, res, out = h.audit(
            "AuditFixture.AllowDep", h.pins("AuditFixture.AllowDep", dep)
        )
        report(
            rc == 1
            and found(res) == {ns("AllowDep", "uses_allowed")}
            and sorted(res["allowlisted"]) == sorted(dep),
            f"a theorem USING the excepted declaration fails — transitive (exit {rc}): {sorted(found(res))}",
            out,
        )
        # M2: a name EXTENDING the entry's name is not covered by it.
        pre = [
            ns("AllowPrefix", "allowed_native"),
            ns("AllowPrefix", "allowed_native") + AX,
        ]
        rc, res, out = h.audit(
            "AuditFixture.AllowPrefix", h.pins("AuditFixture.AllowPrefix", pre)
        )
        report(
            rc == 1
            and found(res) == {ns("AllowPrefix", "allowed_native.extra")}
            and sorted(res["allowlisted"]) == sorted(pre),
            f"`allowed_native.extra` is not covered by the entry for `allowed_native` (exit {rc})",
            out,
        )
        # M13: an entry never allows a SUPERSET of its axioms (here: + sorryAx).
        plus = [
            ns("AllowPlus", "allowed_native"),
            ns("AllowPlus", "allowed_native") + AX,
        ]
        pp = h.pins("AuditFixture.AllowPlus", plus)
        pp[0] = dict(pp[0], axioms=[x for x in pp[0]["axioms"] if x["name"] == plus[1]])
        rc, res, out = h.audit("AuditFixture.AllowPlus", pp)
        report(
            rc == 1 and found(res) == {plus[0]} and res["allowlisted"] == [plus[1]],
            f"native axiom + sorryAx is not allowed by an entry for the native axiom (exit {rc})",
            out,
        )
        stale = [dict(pinned[0], declaration=ns("Clean", "gone"))]
        rc, res, out = h.audit("AuditFixture.Clean", stale)
        report(
            rc == 1 and not res["non_standard"] and len(res["errors"]) == 1,
            f"a STALE entry fails (exit {rc}, {len(res['errors'])} error)",
            out,
        )
        wrong_ax = [
            dict(
                e,
                axioms=[
                    {
                        "name": "sorryAx",
                        "module": "Init.Prelude",
                        "fingerprint": "3" * 64,
                    }
                ],
            )
            for e in pinned
        ]
        rc, res, out = h.audit("AuditFixture.AllowOne", wrong_ax)
        report(
            rc == 1 and found(res) == set(one) and not res["allowlisted"],
            f"an entry naming the WRONG axiom does not allow it (exit {rc})",
            out,
        )
        wild = [dict(pinned[0], declaration="AuditFixture.AllowOne.*")]
        rc, res, out = h.audit("AuditFixture.AllowOne", wild)
        report(
            rc == 1
            and found(res) == set(one)
            and len(res["errors"]) == 1
            and res["rejected_entries"] == 1,
            f"a wildcard entry is rejected as malformed (exit {rc})",
            out,
        )

        # M12: a run whose import fails produces no result and fails.
        rc, res, out = h.audit("AuditFixture.Nope")
        report(
            rc == 1 and len(res["errors"]) == 1 and not res["non_standard"],
            f"an import error fails (exit {rc})",
            out,
        )
        # M5: no runs at all.
        empty = work / "empty"
        empty.mkdir()
        (empty / "manifest.json").write_text(json.dumps({"drivers": []}))
        rc, res, out = h.check(empty, "")
        report(
            rc == 1 and len(res["errors"]) == 1,
            f"an empty manifest (no runs) fails (exit {rc})",
            out,
        )

        # Forged auditor output on the Bad module's run -> must FAIL, never pass.
        d0 = json.loads((bad_drv / "manifest.json").read_text())["drivers"][0]
        outp = Path(d0["output"])
        real = outp.read_text()
        real_res = json.loads(real.strip().splitlines()[-1])
        clean = {
            "shadowed": [],
            "dangling": [],
            "std": real_res["std"],
            "mark": "AXIOM-AUDIT-827",
            "nonce": d0["nonce"],
            "root": d0["label"],
            "scope": d0["modules"],
            "missing": [],
            "unresolved": [],
            "declarations": 9,
            "nonstd": [],
            "theorems_checked": 1,
            "vacuous": [],
            "vacuity_errors": [],
        }
        forged = [
            (
                "a forged clean result appended (duplicate)",
                real + json.dumps(clean) + "\n",
            ),
            (
                "a clean result with a WRONG nonce",
                json.dumps(dict(clean, nonce="0" * 32)),
            ),
            ("a clean result for another root", json.dumps(dict(clean, root="Other"))),
            (
                "a result with zero declarations (M6)",
                json.dumps(dict(clean, declarations=0)),
            ),
            (
                "a result with a missing module (M11)",
                json.dumps(dict(clean, missing=["X"])),
            ),
            (
                "a result whose scope lacks the module",
                json.dumps(dict(clean, scope=[])),
            ),
            (
                "a result with an unresolved module",
                json.dumps(dict(clean, unresolved=["Y"])),
            ),
            (
                "a malformed non-standard entry",
                json.dumps(dict(clean, nonstd=[{"decl": 5}])),
            ),
            (
                "a result with a shadowed toolchain module",
                json.dumps(dict(clean, shadowed=["Init"])),
            ),
            (
                "a result whose propext comes from another module",
                json.dumps(
                    dict(
                        clean,
                        std=[
                            dict(x, module="Evil") if x["name"] == "propext" else x
                            for x in real_res["std"]
                        ],
                    )
                ),
            ),
            (
                "a result whose propext has another statement (fingerprint)",
                json.dumps(
                    dict(
                        clean,
                        std=[
                            (
                                dict(x, fp=x["fp"] + " forged")
                                if x["name"] == "propext"
                                else x
                            )
                            for x in real_res["std"]
                        ],
                    )
                ),
            ),
            (
                "a result without the semantic-vacuity report",
                json.dumps({k: v for k, v in clean.items() if k != "vacuous"}),
            ),
            (
                "a result with an undecided vacuity check (timeout)",
                json.dumps(
                    dict(clean, vacuity_errors=[{"decl": "X.y", "error": "timeout"}])
                ),
            ),
            (
                "a result with a dangling reference",
                json.dumps(dict(clean, dangling=["X.y"])),
            ),
            (
                "a result whose propext is not an axiom",
                json.dumps(
                    dict(
                        clean,
                        std=[
                            dict(x, axiom=False) if x["name"] == "propext" else x
                            for x in real_res["std"]
                        ],
                    )
                ),
            ),
        ]
        for what, text in forged:
            outp.write_text(text + "\n")
            rc, res, out = h.check(bad_drv, "")
            report(
                rc == 1 and len(res["errors"]) == 1 and not res["non_standard"],
                f"{what} makes the audit FAIL, not pass (exit {rc}, {len(res['errors'])} error)",
                out,
            )
    print("axiom-audit planted tests " + ("PASSED" if not bad else f"FAILED ({bad})"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
