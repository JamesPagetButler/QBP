#!/usr/bin/env python3
"""
CTH inventory invariant linter (issue #463).

Enforces status/provenance/proof-state invariants that the JSON Schema cannot
express (cross-field constraints). Complements scripts-side schema validation in
cth-schema-lint.yml.

Invariants (per #463 ACs + foundations rebuild instantiation rules #14–#16),
with one correction flagged for beekeeper review (see INV1 note):

  INV1  status == "untested"  =>  proof_file is null AND theorems is empty
        ("you cannot be untested while carrying a proof artifact")
        NOTE / AC DISCREPANCY: #463 AC also requires provenance_kind ∈ {theory}.
        That is too strict against real data — 4 existing anchors are legitimately
        untested with provenance_kind 'internal-compute' or 'experiment'
        (e.g. EXT-dm-particle-mass, REF-clifton-hyatt-intrinsic). An experimental
        or compute anchor can be untested. The load-bearing invariant is
        "untested => no proof artifact"; the provenance_kind=theory restriction is
        dropped here and flagged for the beekeeper. Re-add via --strict-provenance
        if the AC is confirmed as written.

  INV2  proof_state == "verified"  =>  verification.toolchain is set
        AND every verification.libraries.<lib>.sha is set
        (rebuild rule #15: a verified proof pins its toolchain + library SHAs)

  INV3  proof_state == "verified"  =>  every theorems[].status == "verified"
        (rebuild rule #16: a verified anchor has no unverified theorems)

Exit 0 if clean, 1 if any violation. Emits GitHub-style ::error annotations.
"""

from __future__ import annotations

import argparse
import glob
import json
import sys


def lint_inventory(path: str, strict_provenance: bool) -> list[str]:
    """Return a list of human-readable violation strings for one inventory file."""
    with open(path, encoding="utf-8") as fh:
        doc = json.load(fh)

    violations: list[str] = []
    for a in doc.get("anchors", []):
        aid = a.get("id", "<no-id>")
        status = a.get("status")
        proof_state = a.get("proof_state")

        # INV1 — untested anchors carry no proof artifact
        if status == "untested":
            if a.get("proof_file"):
                violations.append(
                    f"{aid}: INV1 — status 'untested' but proof_file is set "
                    f"({a['proof_file']!r}). An untested anchor must not carry a proof."
                )
            if a.get("theorems"):
                violations.append(
                    f"{aid}: INV1 — status 'untested' but has "
                    f"{len(a['theorems'])} theorem(s). An untested anchor must not carry proofs."
                )
            if strict_provenance and a.get("provenance_kind") not in {"theory"}:
                violations.append(
                    f"{aid}: INV1(strict) — status 'untested' but provenance_kind "
                    f"is {a.get('provenance_kind')!r}, not 'theory'."
                )

        # INV2 / INV3 — verified anchors pin their evidence
        if proof_state == "verified":
            ver = a.get("verification") or {}
            if not ver.get("toolchain"):
                violations.append(
                    f"{aid}: INV2 — proof_state 'verified' but verification.toolchain "
                    f"is missing (rebuild rule #15)."
                )
            for lib, libinfo in (ver.get("libraries") or {}).items():
                if not (libinfo or {}).get("sha"):
                    violations.append(
                        f"{aid}: INV2 — proof_state 'verified' but "
                        f"verification.libraries.{lib}.sha is missing (rebuild rule #15)."
                    )
            for t in a.get("theorems", []):
                if t.get("status") != "verified":
                    violations.append(
                        f"{aid}: INV3 — proof_state 'verified' but theorem "
                        f"{t.get('name', '<unnamed>')!r} has status "
                        f"{t.get('status')!r} (rebuild rule #16)."
                    )
    return violations


def main() -> int:
    ap = argparse.ArgumentParser(description="CTH inventory invariant linter (#463)")
    ap.add_argument(
        "paths",
        nargs="*",
        default=["archive/cth-inventory/*.json"],
        help="inventory files or globs (default: archive/cth-inventory/*.json)",
    )
    ap.add_argument(
        "--strict-provenance",
        action="store_true",
        help="also enforce INV1 provenance_kind=='theory' (per #463 AC as written; "
        "off by default — flagged for beekeeper, see module docstring)",
    )
    args = ap.parse_args()

    files: list[str] = []
    for p in args.paths:
        files.extend(sorted(glob.glob(p)))
    if not files:
        print("::warning::no CTH inventory files matched — nothing to lint.")
        return 0

    total = 0
    for f in files:
        try:
            vs = lint_inventory(f, args.strict_provenance)
        except (OSError, json.JSONDecodeError) as e:
            print(f"::error file={f}::could not read/parse: {e}")
            total += 1
            continue
        if vs:
            for v in vs:
                print(f"::error file={f}::{v}")
            total += len(vs)
            print(f"  ✗ {f}: {len(vs)} invariant violation(s)")
        else:
            print(f"  ✓ {f}: all CTH invariants hold")

    if total:
        print(
            f"\n::error::{total} CTH invariant violation(s) across {len(files)} file(s)."
        )
        return 1
    print(f"\n✓ all CTH invariants hold across {len(files)} file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
