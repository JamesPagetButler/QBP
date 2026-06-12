#!/usr/bin/env python3
"""Layer-import linter for the QBP proofs tree.

Enforces docs/foundations/layer-architecture.md §5:
  1. Foundations files never import QBP.Physics or QBP.Substrate.
  2. Physics-layer files never import QBP.Substrate.
  3. Every .lean under a layer directory is reachable from its aggregator root,
     unless listed in the aggregator's quarantine table (| `QBP.Foo.Bar` | ... |).

Exit 0 = clean; exit 1 = violations (printed).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PROOFS = Path(__file__).resolve().parent.parent / "proofs"

# Physics layer currently lives in these directories (pre-migration, see §6).
PHYSICS_DIRS = [
    "QBP/Physics",
    "QBP/Cosmo",
    "QBP/Cosmology",
    "QBP/Experiments",
    "QBP/Optics",
    "QBP/Oracle",
    "QBP/Units",
]
FOUNDATIONS_DIR = "QBP/Foundations"
SUBSTRATE_DIR = "QBP/Substrate"

IMPORT_RE = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)
QUARANTINE_RE = re.compile(r"^\|\s*`(QBP\.[\w.]+)`", re.MULTILINE)


def imports_of(path: Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(PROOFS).with_suffix("").parts)


def main() -> int:
    errors: list[str] = []

    # Rules 1 & 2: forbidden imports.
    for lean in sorted((PROOFS / FOUNDATIONS_DIR).rglob("*.lean")):
        for imp in imports_of(lean):
            if imp.startswith("QBP.Physics") or imp.startswith("QBP.Substrate"):
                errors.append(f"{lean}: Foundations imports {imp} (forbidden)")
    for pdir in PHYSICS_DIRS:
        base = PROOFS / pdir
        if not base.is_dir():
            continue
        for lean in sorted(base.rglob("*.lean")):
            for imp in imports_of(lean):
                if imp.startswith("QBP.Substrate"):
                    errors.append(f"{lean}: Physics imports {imp} (forbidden)")

    # Rule 3: aggregator completeness for Foundations.
    aggregator = PROOFS / "QBP" / "Foundations.lean"
    if aggregator.is_file():
        text = aggregator.read_text(encoding="utf-8")
        all_imports = IMPORT_RE.findall(text)
        # Duplicate-import guard: the aggregator uses git merge=union (append-only,
        # order-independent), whose one failure mode is a duplicated import line
        # when two branches add the same module. `lake build` tolerates duplicate
        # imports, so this is the only place that catch can live.
        seen: set[str] = set()
        for imp in all_imports:
            if imp in seen:
                errors.append(
                    f"QBP/Foundations.lean: duplicate import {imp} "
                    f"(union-merge artifact — dedupe the aggregator)"
                )
            seen.add(imp)
        imported = set(all_imports)
        quarantined = set(QUARANTINE_RE.findall(text))
        # Stale-import guard (Gemini #527 point-5): union-merge's OTHER failure
        # mode is a divergent same-line edit (two branches rename the same
        # import differently) → union keeps BOTH lines, one possibly pointing at
        # a deleted/renamed module. The duplicate guard above only catches
        # *identical* doubled lines, so it misses this; without the check below
        # the only net is a slow `lake build` missing-module error. Here we
        # verify every QBP.Foundations.* import the aggregator names resolves to
        # an existing file — a fast, deterministic companion catch.
        for imp in sorted(imported):
            if not imp.startswith("QBP.Foundations."):
                continue
            target = PROOFS / Path(*imp.split(".")).with_suffix(".lean")
            if not target.is_file():
                errors.append(
                    f"QBP/Foundations.lean: import {imp} resolves to no file "
                    f"({target.relative_to(PROOFS)} missing — stale/renamed import, "
                    f"possibly a union-merge divergent-edit artifact)"
                )
        for lean in sorted((PROOFS / FOUNDATIONS_DIR).rglob("*.lean")):
            mod = module_of(lean)
            if mod not in imported and mod not in quarantined:
                errors.append(
                    f"{lean}: not imported by QBP/Foundations.lean aggregator and "
                    f"not in its quarantine table (build-invisibility)"
                )
    else:
        errors.append("proofs/QBP/Foundations.lean aggregator missing")

    # Substrate must contain no .lean files yet.
    sub = PROOFS / SUBSTRATE_DIR
    if sub.is_dir():
        for lean in sorted(sub.rglob("*.lean")):
            errors.append(
                f"{lean}: Substrate layer is reserved — no Lean files "
                f"until the first real theorem (layer-architecture §1)"
            )

    if errors:
        print("LAYER-IMPORT VIOLATIONS:")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("layer imports clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
