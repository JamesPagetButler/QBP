#!/usr/bin/env python3
"""C1/C2/C3 manifest-enforcement gate — FAULT-S4-005 Step 3.

The root cause of FAULT-S4-005: the inverse-anchor-audit ratchet counted EVERY
`grep theorem` (640, mostly auxiliary lemmas) as an anchor candidate, so anchoring
all of them was impossible and the only viable response was silently raising the
baseline — which turned the ratchet into a logbook, not a gate.

The fix — ONE manifest (docs/cth/anchor-worthy-manifest.json), three clauses:
  C1  candidate set = the DECLARED anchor-worthy deliverables (top-level, non-private,
      named in an issue-AC / #474-row) — NOT `grep theorem`. (640 -> ~dozen.)
  C2  a declared deliverable whose anchor_id is ABSENT from the CTH ledger is a
      HARD FAIL. It cannot be baselined away — no raisable soft-escape.
  C3  a declared anchor's WITNESSES must RESOLVE in source on the PR head (the ledger
      anchor's proof_file exists AND each witness theorem name appears in it). Catches
      the #613/#615 class: a `provenance_kind:proof` anchor whose witnesses/proof_file
      don't resolve. HARD FAIL on real drift, no escape.
      (Clauses a/b of qbp-cu #66's run-pattern. Clause (c) infra-soft-pass is
      fetch-conditional — N/A here, C3 is intra-QBP, no cross-repo fetch; per
      qbp-cu-implementor seq=1021. #68 persistent-infra escalation inherited later.)

Usage: check_anchor_manifest.py [--manifest F] [--ledger F] [--root DIR] [--skip-witnesses]
Exit 0 = clean; 1 = a declared-but-unanchored (C1/C2) or a witness that fails to resolve (C3).
"""

import argparse
import json
import os
import sys

DEFAULT_MANIFEST = "docs/cth/anchor-worthy-manifest.json"
DEFAULT_LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"


def load_ledger(path):
    with open(path, encoding="utf-8") as f:
        return {a["id"]: a for a in json.load(f).get("anchors", [])}


def _short(qualified):
    # last dotted component: "QBP.Foundations.CPPhase.cos_sq_delta_CP" -> "cos_sq_delta_CP";
    # "S3FromCD.S³-HSpace" -> "S³-HSpace".
    return qualified.rsplit(".", 1)[-1]


def check_witnesses_resolve(entries, ledger_by_id, root="."):
    """C3: each declared anchor's witnesses must resolve in source. Returns a list of
    (anchor_id, reason) for anything that does not resolve (real drift → caller hard-fails).
    """
    unresolved = []
    for e in entries:
        anchor = ledger_by_id.get(e["anchor_id"])
        if anchor is None:
            continue  # C1/C2 already reported this as an orphan
        pf = anchor.get("proof_file")
        if not pf:
            unresolved.append((e["anchor_id"], "ledger anchor has no proof_file"))
            continue
        path = os.path.join(root, pf)
        if not os.path.exists(path):
            unresolved.append((e["anchor_id"], f"proof_file does not exist: {pf}"))
            continue
        with open(path, encoding="utf-8") as f:
            src = f.read()
        for w in e.get("witnesses", []):
            if _short(w) not in src:
                unresolved.append((e["anchor_id"], f"witness not found in {pf}: {w}"))
    return unresolved


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=DEFAULT_MANIFEST)
    ap.add_argument("--ledger", default=DEFAULT_LEDGER)
    ap.add_argument(
        "--root", default=".", help="repo root for resolving proof_file paths"
    )
    ap.add_argument(
        "--skip-witnesses",
        action="store_true",
        help="skip C3 (witnesses-resolve) — e.g. when source is not checked out",
    )
    args = ap.parse_args()

    with open(args.manifest, encoding="utf-8") as f:
        entries = json.load(f).get("entries", [])
    ledger_by_id = load_ledger(args.ledger)

    print(
        f"Anchor-worthiness manifest: {len(entries)} declared deliverable(s); "
        f"ledger carries {len(ledger_by_id)} anchors."
    )

    # C1/C2: declared deliverable absent from the ledger = hard fail (no baselining).
    orphans = [e for e in entries if e["anchor_id"] not in ledger_by_id]
    if orphans:
        print(
            "::error::C1/C2 — declared anchor-worthy deliverable(s) are NOT anchored in the "
            "CTH ledger. A declared deliverable MUST ship its anchor (it cannot be baselined "
            "away — FAULT-S4-005). Add the anchor, or remove the manifest entry if declared in "
            "error:"
        )
        for e in orphans:
            print(
                f"  - {e['anchor_id']} (declared_by {e.get('declared_by','?')}, "
                f"{e.get('proof_system','?')})"
            )
        return 1

    # C3: each declared anchor's witnesses must resolve in source (real drift = hard fail).
    if not args.skip_witnesses:
        unresolved = check_witnesses_resolve(entries, ledger_by_id, args.root)
        if unresolved:
            print(
                "::error::C3 — declared anchor witness(es) do not resolve in source (the "
                "proof_file or a witness theorem is missing on this head — a proof anchor "
                "whose witnesses don't exist, #613/#615 class):"
            )
            for aid, reason in unresolved:
                print(f"  - {aid}: {reason}")
            return 1
        print("PASS (C3): every declared anchor's witnesses resolve in source.")

    print(
        "PASS: every declared anchor-worthy deliverable is anchored (C1/C2)"
        + ("" if args.skip_witnesses else " and its witnesses resolve (C3)")
        + "."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
