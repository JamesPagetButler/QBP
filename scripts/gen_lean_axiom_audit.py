#!/usr/bin/env python3
"""Generate the Lean axiom-audit runs — QBP issue #827 AC2/AC3.

COVERAGE COMES FROM LEAN, NOT FROM PYTHON. Python only decides which MODULES are in scope —
the transitive import closure of the `@[default_target]` roots in `proofs/lakefile.lean`,
i.e. exactly what CI's bare `lake build` compiles (parsed with `check_layer_imports.py`'s
lakefile/import helpers). For each default-target root it writes the ARGUMENTS of one run of
the fixed auditor program `scripts/LeanAxiomAudit.lean`, which loads that root's ELABORATED
ENVIRONMENT from the built .olean files: every constant whose defining module is in scope —
theorem, def, instance, axiom, inductive, auxiliary lemma, however the source is written
(comments, strings, `#print axioms` or not) — has its axiom closure computed, and any axiom
outside {propext, Classical.choice, Quot.sound} is reported. One run per root because roots
can clash when imported together (e.g. two `lean_exe` roots each defining `main`).

WHY THERE IS NO GENERATED .lean DRIVER (PR #829, Gemini r1 finding 1). The first version wrote
a `.lean` driver that IMPORTED the audited modules and ran the audit in a `run_cmd`. Such a file
is elaborated under every syntax extension its imports export: a high-priority `!` macro, a
`BEq Name` or `HAdd Nat Nat Nat` instance, and so on. Reproduced on Lean 4.30.0 with
`lean_audit_fixtures/AuditFixture/Inject.lean`: the old driver emitted a genuine, correctly
positioned `SUMMARY … bad=0` for a module resting on `sorryAx`, and the gate PASSED. The
auditor is now ONE fixed program, elaborated against the toolchain only (it imports nothing but
`Lean` and is run with LEAN_PATH unset). It loads the audited modules at RUN time with
`importModules (loadExts := false)`, as data. None of their macros, instances or initializers
exists while the auditor is elaborated, and none of their code runs. This generator writes only
the auditor's arguments and the manifest the checker grades against.

usage:
  gen_lean_axiom_audit.py --proofs proofs --out-dir DIR      write DIR/AxiomAudit_<n>.args + DIR/manifest.json
  gen_lean_axiom_audit.py --proofs proofs --topo             print the in-scope modules in build order
  gen_lean_axiom_audit.py --proofs proofs --modules M1 M2 --out-dir DIR
                                                             (fixtures/tests) audit exactly these modules
Run each DIR/AxiomAudit_<n>.args (one argument per line) as
  env -u LEAN_PATH QBP_AUDIT_LEAN_PATH=<project LEAN_PATH> lean --run scripts/LeanAxiomAudit.lean <args…> > DIR/AxiomAudit_<n>.out
"""

from __future__ import annotations

import argparse
import json
import os
import secrets
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_layer_imports import (
    imports_of,
    lakefile_targets,
    resolve_module,
)  # noqa: E402

AUDIT_MARK = "AXIOM-AUDIT-827"
AUDITOR = Path(__file__).resolve().parent / "LeanAxiomAudit.lean"
# Module-name roots owned by the toolchain. A project module under one of these could shadow the
# toolchain library on the project search path, so the generator refuses it outright.
RESERVED_ROOTS = {"Init", "Std", "Lean", "Lake"}


def scope(proofs: Path) -> tuple[list[str], dict[str, list[str]], list[str]]:
    """(default roots, closure per root in build order, srcdirs)."""
    errors: list[str] = []
    targets = lakefile_targets(proofs, errors)
    if errors:
        raise SystemExit("; ".join(errors))
    srcdirs = ["."] + sorted({sd for sd, _, _ in targets if sd != "."})
    roots = [r for _, rs, d in targets if d for r in rs]
    closures: dict[str, list[str]] = {}
    for root in roots:
        order: list[str] = []
        seen: set[str] = set()

        def visit(mod: str) -> None:  # post-order = build order
            if mod in seen:
                return
            seen.add(mod)
            p = resolve_module(mod, proofs, srcdirs)
            if p is None:
                return  # external (Mathlib, Init, …)
            for dep in imports_of(p):
                visit(dep)
            order.append(mod)

        sys.setrecursionlimit(10000)
        visit(root)
        closures[root] = order
    return roots, closures, srcdirs


def all_modules(proofs: Path, srcdirs: list[str]) -> list[str]:
    out = set()
    for p in proofs.rglob("*.lean"):
        rel = p.relative_to(proofs)
        if ".lake" in rel.parts or rel.name == "lakefile.lean":
            continue
        for sd in sorted(srcdirs, key=len, reverse=True):
            base = proofs / sd
            try:
                r = p.relative_to(base)
            except ValueError:
                continue
            if sd == "." and any(rel.parts[0] == s for s in srcdirs if s != "."):
                continue
            out.add(".".join(r.with_suffix("").parts))
            break
    return sorted(out)


def write(out: Path, groups: list[tuple[str, list[str]]], extra: dict) -> None:
    """One auditor run per root: DIR/AxiomAudit_<k>.args (one argument per line: NONCE, LABEL,
    then `i:<import>` and `t:<target module>` items) + DIR/manifest.json. The NONCE is fresh per
    generation (CI generates after `lake build`), so no file written during the build can pass
    for the auditor's output; leftover outputs in DIR are deleted first."""
    out.mkdir(parents=True, exist_ok=True)
    for old in list(out.glob("AxiomAudit_*")):
        old.unlink()
    reserved = sorted(
        {m for _, mods in groups for m in mods if m.split(".")[0] in RESERVED_ROOTS}
    )
    if reserved:
        raise SystemExit(
            f"refusing to audit modules under a toolchain root {sorted(RESERVED_ROOTS)}: {reserved}"
        )
    files = []
    for k, (root, mods) in enumerate(groups):
        nonce = secrets.token_hex(16)
        label = root or "(explicit)"
        imports = [root] if root else list(mods)
        args = [nonce, label] + [f"i:{m}" for m in imports] + [f"t:{m}" for m in mods]
        f = out / f"AxiomAudit_{k}.args"
        f.write_text("\n".join(args) + "\n", encoding="utf-8")
        files.append(
            {
                "args": str(f),
                "output": str(f.with_suffix(".out")),
                "root": root,
                "label": label,
                "nonce": nonce,
                "imports": imports,
                "modules": mods,
            }
        )
    (out / "manifest.json").write_text(
        json.dumps({"auditor": str(AUDITOR), "drivers": files, **extra}, indent=1)
        + "\n"
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proofs", default="proofs")
    ap.add_argument("--out-dir")
    ap.add_argument("--topo", action="store_true")
    ap.add_argument("--modules", nargs="*")
    a = ap.parse_args()
    proofs = Path(a.proofs)
    if a.modules:
        write(
            Path(a.out_dir), [("", a.modules)], {"in_scope": a.modules, "not_built": []}
        )
        return 0
    roots, closures, srcdirs = scope(proofs)
    in_scope: list[str] = []
    for r in roots:
        for m in closures[r]:
            if m not in in_scope:
                in_scope.append(m)
    if a.topo:
        print("\n".join(in_scope))
        return 0
    not_built = [m for m in all_modules(proofs, srcdirs) if m not in in_scope]
    write(
        Path(a.out_dir),
        [(r, closures[r]) for r in roots],
        {"in_scope": in_scope, "not_built": not_built},
    )
    print(
        f"axiom-audit runs: {len(roots)} root(s), {len(in_scope)} in-scope module(s); "
        f"{len(not_built)} module(s) in proofs/ not built by `lake build`: {', '.join(not_built) or '—'}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
