#!/usr/bin/env python3
"""Generate the Lean axiom-audit runs — QBP issue #827 AC2/AC3.

COVERAGE AND SCOPE COME FROM LEAN, NOT FROM PYTHON. Python picks only the ROOTS (the
`@[default_target]` roots in `proofs/lakefile.lean`, i.e. what CI's bare `lake build` compiles)
and writes, for each root, the ARGUMENTS of one run of the fixed auditor program
`scripts/LeanAxiomAudit.lean`. The auditor loads that root's environment from the built .olean
files and audits every module it really loaded whose .olean lies in the project build directory
(PR #829 Red Team finding 4: a Python import regex had missed `import A import Hidden` on one
line). Every constant of those modules — theorem, def, instance, axiom, inductive, auxiliary
lemma, however the source is written — has its exact axiom closure computed, and any axiom
outside {propext, Classical.choice, Quot.sound} is reported. The Python import closure
(`check_layer_imports.py` helpers, now multi-import-per-line) is kept only as a cross-check:
each of its modules must be in Lean's scope. One run per root because roots can clash when
imported together (e.g. two `lean_exe` roots each defining `main`). The allowlist's declarations
are passed along so the auditor fingerprints them (identity pins, Red Team finding 3).

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
  gen_lean_axiom_audit.py --proofs proofs --out-dir DIR [--allowlist FILE] [--project-dir D]
                                                             write DIR/AxiomAudit_<n>.args + DIR/manifest.json
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


def allowlist_names(path: str) -> list[str]:
    """Declarations named by the allowlist (the auditor fingerprints exactly these)."""
    if not path or not Path(path).exists():
        return []
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    return sorted(
        {e["declaration"] for e in data.get("entries", []) if isinstance(e, dict)}
    )


def write(
    out: Path,
    groups: list[tuple[str, list[str]]],
    extra: dict,
    project_dirs: list[str],
    allow: list[str],
) -> None:
    """One auditor run per root: DIR/AxiomAudit_<k>.args (one argument per line: NONCE, LABEL,
    then `i:<import>`, `t:<expected module>`, `p:<project build dir>`, `a:<allowlisted name>`
    items) + DIR/manifest.json. The NONCE is fresh per generation (CI generates after
    `lake build`), so no file written during the build can pass for the auditor's output;
    leftover outputs in DIR are deleted first. The SCOPE is decided by Lean (every loaded
    module whose .olean lies under a `p:` directory); `t:` is only a cross-check."""
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
        args = (
            [nonce, label]
            + [f"i:{m}" for m in imports]
            + [f"t:{m}" for m in mods]
            + [f"p:{d}" for d in project_dirs]
            + [f"a:{n}" for n in allow]
        )
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
    ap.add_argument(
        "--project-dir",
        action="append",
        help="project build dir(s) holding the audited .olean files "
        "(default PROOFS/.lake/build/lib/lean)",
    )
    ap.add_argument(
        "--allowlist",
        default=str(Path(__file__).resolve().parent / "lean_axiom_allowlist.json"),
        help="allowlist whose declarations the auditor fingerprints ('' = none)",
    )
    ap.add_argument(
        "--vacuity-allowlist",
        default=str(Path(__file__).resolve().parent / "lean_vacuity_allowlist.json"),
        help="vacuity allowlist whose theorems the auditor fingerprints ('' = none)",
    )
    a = ap.parse_args()
    proofs = Path(a.proofs)
    # absolute: the auditor runs from inside proofs/, not from where this script was called
    pdirs = [
        str(Path(d).resolve())
        for d in (a.project_dir or [str(proofs / ".lake" / "build" / "lib" / "lean")])
    ]
    allow = sorted(
        set(allowlist_names(a.allowlist)) | set(allowlist_names(a.vacuity_allowlist))
    )
    if a.modules:
        write(
            Path(a.out_dir),
            [("", a.modules)],
            {"in_scope": a.modules, "all_modules": a.modules},
            pdirs,
            allow,
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
    everything = all_modules(proofs, srcdirs)
    write(
        Path(a.out_dir),
        [(r, closures[r]) for r in roots],
        {"in_scope": in_scope, "all_modules": everything},
        pdirs,
        allow,
    )
    print(
        f"axiom-audit runs: {len(roots)} root(s); the Python import closure lists "
        f"{len(in_scope)} module(s) (a cross-check — Lean decides the audited scope)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
