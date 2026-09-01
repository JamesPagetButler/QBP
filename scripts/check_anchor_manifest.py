#!/usr/bin/env python3
"""C1/C2 manifest-enforcement gate — FAULT-S4-005 Step 3.

The root cause of FAULT-S4-005: the inverse-anchor-audit ratchet counted EVERY
`grep theorem` (640, mostly auxiliary lemmas) as an anchor candidate, so anchoring
all of them was impossible and the only viable response was silently raising the
baseline — which turned the ratchet into a logbook, not a gate.

The fix (C1 + C2), one manifest:
  C1  candidate set = the DECLARED anchor-worthy deliverables in
      docs/cth/anchor-worthy-manifest.json (top-level, non-private, named in an
      issue-AC / #474-row) — NOT `grep theorem`. (640 -> ~dozen.)
  C2  a declared deliverable whose anchor_id is ABSENT from the CTH ledger is a
      HARD FAIL. It cannot be baselined away — declared deliverables must be
      *anchored*, full stop. No raisable soft-escape.

  C3  (witnesses-resolve-on-master) rides qbp-cu #66 Step-1 + qbp-architecture §5 —
      stubbed below, not yet enforced.

Usage: check_anchor_manifest.py [--manifest F] [--ledger F]
Exit 0 = every declared anchor is in the ledger; 1 = one or more declared-but-unanchored.
"""

import argparse
import json
import sys

DEFAULT_MANIFEST = "docs/cth/anchor-worthy-manifest.json"
DEFAULT_LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"


def load_ledger_ids(path):
    with open(path, encoding="utf-8") as f:
        return {a["id"] for a in json.load(f).get("anchors", [])}


def check_witnesses_resolve(manifest, ledger_ids):  # noqa: ARG001
    """C3 STUB — rides qbp-cu #66 Step-1 infra-vs-drift run-pattern + qbp-architecture §5.
    Will verify each entry's `witnesses` resolve on master (Lean qualified name /
    Agda Module.def), fail-closed on real drift, soft-pass on infra failure. Not yet
    wired (no #66 dependency here)."""
    return []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=DEFAULT_MANIFEST)
    ap.add_argument("--ledger", default=DEFAULT_LEDGER)
    args = ap.parse_args()

    with open(args.manifest, encoding="utf-8") as f:
        manifest = json.load(f)
    entries = manifest.get("entries", [])
    ledger_ids = load_ledger_ids(args.ledger)

    # C1: orphan = a DECLARED (manifest) anchor absent from the ledger.
    orphans = [e for e in entries if e["anchor_id"] not in ledger_ids]

    print(
        f"Anchor-worthiness manifest: {len(entries)} declared deliverable(s); "
        f"ledger carries {len(ledger_ids)} anchors."
    )
    if orphans:
        print(
            "::error::C1/C2 — declared anchor-worthy deliverable(s) are NOT anchored in "
            "the CTH ledger. A declared deliverable MUST ship its anchor (it cannot be "
            "baselined away — FAULT-S4-005). Add the anchor, or remove the manifest entry "
            "if it was declared in error:"
        )
        for e in orphans:
            print(
                f"  - {e['anchor_id']} (declared_by {e.get('declared_by','?')}, "
                f"{e.get('proof_system','?')})"
            )
        return 1

    print(
        "PASS: every declared anchor-worthy deliverable is anchored in the ledger (C1/C2)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
