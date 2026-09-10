#!/usr/bin/env python3
"""Layer-import linter for the QBP proofs tree.

Enforces docs/foundations/layer-architecture.md §5:
  1. Foundations files never import QBP.Physics or QBP.Substrate.
  2. Physics-layer files never import QBP.Substrate.
  3. Every .lean under a layer directory is reachable from its aggregator root,
     unless listed in the aggregator's quarantine table (| `QBP.Foo.Bar` | ... |).
  4. Substrate files (allowed since the beekeeper's 2026-09-07 lift, AC1-hosting only)
     state what they host and what they do not derive, cite the lift, and are reachable
     from QBP/Substrate.lean (layer-architecture §1).
  5. BUILD-VISIBILITY for the physics dirs (Experiments/Optics/Cosmo/Oracle/Units) and
     the Sprint12 corpus. Every .lean under these dirs must be transitively reachable
     from a DEFAULT-target root (a lakefile target carrying `@[default_target]` — the
     `QBP` lean_lib root and the Sprint12 lib roots), OR be listed in the shrink-only,
     issue-linked build-visibility quarantine.

     Rationale: CI runs bare `lake build`, which compiles only the `@[default_target]`s.
     A .lean reachable from none of them is compiled by nothing in CI — it can be
     committed build-broken while `lake build` stays green (the General3D.lean
     build-invisibility class that let an unclosed goal ride CI-green, issue #625/#619).
     "Reachable via a declared-but-non-default target" (a `lean_exe`) is NOT enough:
     CI does not build a non-default target, so its files are invisible to CI too.
     (The QBP `oracle`/`gen_test_vectors` exes were promoted to `@[default_target]`
     in #646 so CI now compiles them; a future non-default target would be caught
     here.) Foundations/Substrate get completeness via their per-dir aggregators
     (rules 3/4); the physics + Sprint12 dirs have no single aggregator (files wire
     directly into QBP.lean, Cosmo has its own aggregator, Oracle/Units files hang off
     lean_exe roots, Sprint12 files are each a lib root), so this rule uses the REAL
     import graph instead.

Exit 0 = clean; exit 1 = violations (printed).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DEFAULT_PROOFS = Path(__file__).resolve().parent.parent / "proofs"

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

# The shrink-only build-visibility quarantine, relative to the proofs root.
QUARANTINE_REL = "QBP/.build-visibility-quarantine.json"

# Directories whose every .lean must be build-visible (reachable from a declared
# lakefile target root) or quarantined. Foundations/Substrate get completeness from
# their own aggregators (rules 3/4); rule 5 covers these via the real build graph.
# Sprint12-Inherited is a separate lean_lib with its own srcDir — issue #625 AC1
# names it explicitly.
BUILD_VISIBILITY_DIRS = PHYSICS_DIRS + ["Sprint12-Inherited"]

IMPORT_RE = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)
QUARANTINE_RE = re.compile(r"^\|\s*`(QBP\.[\w.]+)`", re.MULTILINE)
# Lakefile parsing: `lean_lib`/`lean_exe` target blocks, each with an optional
# `srcDir := "X"` and roots given as `root := `Mod`` or `roots := #[`A, `B]`.
LAKE_DECL_RE = re.compile(r"^\s*lean_(?:lib|exe)\b", re.MULTILINE)
LAKE_SRCDIR_RE = re.compile(r'srcDir\s*:=\s*"([^"]*)"')
LAKE_ROOT_RE = re.compile(r"root\s*:=\s*`([\w.]+)")
LAKE_ROOTS_RE = re.compile(r"roots\s*:=\s*#\[([^\]]*)\]")
BACKTICK_NAME_RE = re.compile(r"`([\w.]+)")


def imports_of(path: Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def module_of(path: Path, proofs: Path) -> str:
    return ".".join(path.relative_to(proofs).with_suffix("").parts)


def _has_default_attr(text_before_decl: str) -> bool:
    """Is the target declared right after `text_before_decl` a `@[default_target]`?

    Walks upward over the contiguous run of attribute/blank lines directly above
    the declaration. `@[default_target]` on such a line marks it default; a comment
    line (`--` or a `/-` docstring) or any other content ends the run WITHOUT
    marking it — so a commented-out `-- @[default_target]` never counts, and a
    docstring or blank lines between attributes and the decl do not break detection.
    Robust to formatting, unlike a fixed-width character window (Gemini/#645, Knuth).
    """
    for line in reversed(text_before_decl.splitlines()):
        s = line.strip()
        if not s:
            continue  # blank line — keep scanning upward
        if s.startswith("@["):
            if "default_target" in s:
                return True
            continue  # a different attribute — another may sit above it
        return False  # comment, docstring, or code — end of the attribute run
    return False


def lakefile_targets(
    proofs: Path, errors: list[str]
) -> list[tuple[str, list[str], bool]]:
    """Every `lean_lib`/`lean_exe` target as `(srcDir, [root modules], is_default)`.

    `is_default` is True when the target carries the `@[default_target]` attribute
    (on the line before its declaration) — the ONLY targets bare `lake build`
    compiles, which is what CI runs. Non-default targets (the exes) are declared
    but not built by CI, so files reachable only through them are build-invisible
    to CI. Parsing the lakefile (rather than hardcoding `QBP`) keeps the linter
    honest when a target is added; capturing each target's `srcDir` lets roots
    under a non-default srcDir (the Sprint12 corpus) resolve to the right files.
    """
    lakefile = proofs / "lakefile.lean"
    if not lakefile.is_file():
        errors.append("proofs/lakefile.lean missing — cannot determine build roots")
        return []
    text = lakefile.read_text(encoding="utf-8")
    starts = [m.start() for m in LAKE_DECL_RE.finditer(text)]
    if not starts:
        errors.append("proofs/lakefile.lean declares no lean_lib/lean_exe targets")
        return []
    bounds = starts + [len(text)]
    targets: list[tuple[str, list[str], bool]] = []
    for i in range(len(starts)):
        block = text[bounds[i] : bounds[i + 1]]
        is_default = _has_default_attr(text[: starts[i]])
        sd = LAKE_SRCDIR_RE.search(block)
        srcdir = sd.group(1) if sd else "."
        roots: list[str] = list(LAKE_ROOT_RE.findall(block))
        for group in LAKE_ROOTS_RE.findall(block):
            roots.extend(BACKTICK_NAME_RE.findall(group))
        if roots:
            targets.append((srcdir, roots, is_default))
    return targets


def resolve_module(module: str, proofs: Path, srcdirs: list[str]) -> Path | None:
    """First existing file for `module` across the candidate srcDirs, else None.

    A Lean module name resolves against the srcDir of some package library; here
    we try each declared srcDir (default "." first). Externals (Mathlib/Init/...)
    resolve to no file and are naturally skipped.
    """
    for sd in srcdirs:
        target = (proofs / sd / Path(*module.split("."))).with_suffix(".lean")
        if target.is_file():
            return target
    return None


def build_visible_files(
    proofs: Path, targets: list[tuple[str, list[str], bool]], srcdirs: list[str]
) -> set[Path]:
    """Resolved-file transitive import closure from the DEFAULT-target roots.

    Only `@[default_target]` roots seed the closure, because bare `lake build`
    (what CI runs) compiles only those. A .lean whose resolved path is in this set
    is actually compiled by CI; one that is not is build-invisible to CI — even if
    it is reachable from a declared-but-non-default target such as a non-default
    `lean_exe`. Keyed on resolved file paths, not module names (which can collide
    across srcDirs).
    """
    seen: set[Path] = set()
    stack: list[str] = []
    for _srcdir, roots, is_default in targets:
        if is_default:
            stack.extend(roots)
    while stack:
        module = stack.pop()
        path = resolve_module(module, proofs, srcdirs)
        if path is None:
            continue
        rp = path.resolve()
        if rp in seen:
            continue
        seen.add(rp)
        stack.extend(imports_of(path))
    return seen


def load_quarantine(proofs: Path, errors: list[str]) -> dict[str, dict]:
    """Read the shrink-only build-visibility quarantine, keyed on proofs-relative path.

    Schema: {"entries": [{"file": "QBP/Oracle/FFI.lean", "reason": "...",
    "issue": "#NNN"}]}. Every entry MUST carry a non-empty issue and reason — a
    quarantine with no tracking issue is exactly the silent-baseline anti-pattern
    this gate exists to prevent.
    """
    qfile = proofs / QUARANTINE_REL
    if not qfile.is_file():
        return {}
    name = qfile.name
    try:
        data = json.loads(qfile.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        errors.append(f"{name}: invalid JSON ({exc})")
        return {}
    out: dict[str, dict] = {}
    for entry in data.get("entries", []):
        rel = entry.get("file")
        if not rel:
            errors.append(f"{name}: entry with no 'file' field")
            continue
        if not entry.get("issue"):
            errors.append(
                f"{name}: quarantine entry for {rel} has no 'issue' — every "
                f"quarantined file must name a tracking issue (no silent baselining)"
            )
        if not entry.get("reason"):
            errors.append(f"{name}: quarantine entry for {rel} has no 'reason'")
        out[rel] = entry
    return out


def check(proofs: Path) -> list[str]:
    errors: list[str] = []
    qf_name = (proofs / QUARANTINE_REL).name

    # Rules 1 & 2: forbidden imports.
    for lean in sorted((proofs / FOUNDATIONS_DIR).rglob("*.lean")):
        for imp in imports_of(lean):
            if imp.startswith("QBP.Physics") or imp.startswith("QBP.Substrate"):
                errors.append(f"{lean}: Foundations imports {imp} (forbidden)")
    for pdir in PHYSICS_DIRS:
        base = proofs / pdir
        if not base.is_dir():
            continue
        for lean in sorted(base.rglob("*.lean")):
            for imp in imports_of(lean):
                if imp.startswith("QBP.Substrate"):
                    errors.append(f"{lean}: Physics imports {imp} (forbidden)")

    # Rule 3: aggregator completeness for Foundations.
    aggregator = proofs / "QBP" / "Foundations.lean"
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
            target = proofs / Path(*imp.split(".")).with_suffix(".lean")
            if not target.is_file():
                errors.append(
                    f"QBP/Foundations.lean: import {imp} resolves to no file "
                    f"({target.relative_to(proofs)} missing — stale/renamed import, "
                    f"possibly a union-merge divergent-edit artifact)"
                )
        for lean in sorted((proofs / FOUNDATIONS_DIR).rglob("*.lean")):
            mod = module_of(lean, proofs)
            if mod not in imported and mod not in quarantined:
                errors.append(
                    f"{lean}: not imported by QBP/Foundations.lean aggregator and "
                    f"not in its quarantine table (build-invisibility)"
                )
    else:
        errors.append("proofs/QBP/Foundations.lean aggregator missing")

    # Substrate: reserved until 2026-09-07, when the beekeeper lifted the empty-Substrate
    # rule for AC1-hosting work only (#473 issuecomment-5574256922). The lift carries a
    # per-file discipline (layer-architecture §1): every Substrate .lean file must state in
    # its module docstring what it HOSTS and what it does NOT DERIVE, and cite the lift.
    # It must also be reachable from the QBP/Substrate.lean aggregator (mirror of rule 3).
    sub = proofs / SUBSTRATE_DIR
    if sub.is_dir():
        sub_agg = proofs / "QBP" / "Substrate.lean"
        sub_imported = set(imports_of(sub_agg)) if sub_agg.exists() else set()
        for lean in sorted(sub.rglob("*.lean")):
            text = lean.read_text(encoding="utf-8")
            head = text[:6000]
            missing = []
            if "host" not in head.lower():
                missing.append("a statement of what it HOSTS")
            if (
                "not derive" not in head.lower()
                and "does not derive" not in head.lower()
            ):
                missing.append("a statement of what it does NOT DERIVE")
            if "5574256922" not in head and "#473" not in head:
                missing.append(
                    "a citation of the beekeeper's lift (#473 issuecomment-5574256922)"
                )
            if missing:
                errors.append(
                    f"{lean}: Substrate file lacks the per-file discipline of the lift "
                    f"(layer-architecture §1): {'; '.join(missing)}"
                )
            mod = module_of(lean, proofs)
            if not sub_agg.exists():
                errors.append(
                    "proofs/QBP/Substrate.lean aggregator missing (Substrate has .lean files)"
                )
            elif mod not in sub_imported:
                errors.append(
                    f"{lean}: not imported by QBP/Substrate.lean aggregator (build-invisibility)"
                )

    # Rule 5: build-visibility for the physics dirs + Sprint12 corpus. "Visible" =
    # its resolved file is in the transitive import closure of the DEFAULT-target
    # roots — what bare `lake build` (CI) actually compiles. A file reachable only
    # via a non-default target (a lean_exe) is invisible to CI and must be
    # quarantined. These dirs have no single per-dir aggregator to key a membership
    # check on, so we use the closure directly.
    targets = lakefile_targets(proofs, errors)
    srcdirs: list[str] = ["."]
    for srcdir, _roots, _is_default in targets:
        if srcdir not in srcdirs:
            srcdirs.append(srcdir)
    visible = build_visible_files(proofs, targets, srcdirs)
    quarantine = load_quarantine(proofs, errors)

    enforced_files: set[str] = set()
    for vdir in BUILD_VISIBILITY_DIRS:
        base = proofs / vdir
        if not base.is_dir():
            continue
        for lean in sorted(base.rglob("*.lean")):
            rel = str(lean.relative_to(proofs))
            enforced_files.add(rel)
            in_build = lean.resolve() in visible
            in_quar = rel in quarantine
            if not in_build and not in_quar:
                errors.append(
                    f"{rel}: build-invisible — its resolved file is reachable from no "
                    f"lakefile target root and it is not in {qf_name}. Nothing compiles "
                    f"it, so it can be committed broken while `lake build` stays green. "
                    f"Wire it into an imported module, or quarantine it with a "
                    f"tracking issue."
                )
            elif in_build and in_quar:
                errors.append(
                    f"{rel}: listed in {qf_name} but is now build-visible (reachable "
                    f"from a target root) — stale quarantine entry, remove it (the "
                    f"quarantine is shrink-only)."
                )

    # Stale-quarantine guard: an entry whose file is gone, or that is not under an
    # enforced dir (the quarantine only governs the enforced tree).
    for rel in sorted(quarantine):
        if not (proofs / rel).is_file():
            errors.append(
                f"{rel}: quarantined in {qf_name} but the file does not exist — "
                f"stale entry, remove it."
            )
        elif rel not in enforced_files:
            errors.append(
                f"{rel}: quarantined in {qf_name} but is not under an enforced dir "
                f"{BUILD_VISIBILITY_DIRS} — the quarantine only governs the enforced "
                f"tree; remove it."
            )

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--proofs",
        default=str(DEFAULT_PROOFS),
        help="Path to the proofs/ tree to check (default: the repo's proofs/).",
    )
    args = parser.parse_args(argv)
    errors = check(Path(args.proofs))
    if errors:
        print("LAYER-IMPORT VIOLATIONS:")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("layer imports clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
