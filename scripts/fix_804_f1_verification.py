#!/usr/bin/env python3
"""PR #804 Gemini F1 fix (issuecomment-6863989282, oppenheimer seq4811).

encode_housekeeping_batch.py overwrote `verification.verified_at`/`verifier` on
PROOF-eigenratios, PROOF-cl6 and PROOF-3gen when it populated theorems[]/notes.
That erased the original Lean proof-checking provenance. Restores both fields to
their pre-batch values (git show 8d68a09) byte-for-byte; the housekeeping
attribution stays in notes/changelog, where it already is.

Usage: python3 scripts/fix_804_f1_verification.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
NEW_VERSION = "6.23.1"
DATE = "2026-11-15T00:00:00Z"

ORIGINAL_VERIFICATION = {
    "verified_at": "2026-09-02T23:46:49Z",
    "verifier": (
        "lake build + #print axioms, leanprover/lean4:v4.30.0 (qbp-oppenheimer, #621 "
        "FAULT-S4-005 burn-down); encoded by qbp-implementor; pending tier-3 review + §I4"
    ),
}

ANCHORS = ["PROOF-eigenratios", "PROOF-cl6", "PROOF-3gen"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        ids = {a["id"] for a in L["anchors"]}
        for aid in ANCHORS:
            if aid not in ids:
                raise SystemExit(f"F1 fix: anchor missing: {aid}")
            a = ed.record("anchors", aid)
            v = a.get("verification")
            if not isinstance(v, dict):
                raise SystemExit(f"F1 fix: {aid} has no verification object")
            if v.get("verified_at") == ORIGINAL_VERIFICATION["verified_at"]:
                raise SystemExit(f"F1 fix: {aid}.verification already original — no-op")
            v["verified_at"] = ORIGINAL_VERIFICATION["verified_at"]
            v["verifier"] = ORIGINAL_VERIFICATION["verifier"]

        L["version"] = NEW_VERSION
        ed.touch("version")
        L["last_updated"] = DATE
        ed.touch("last_updated")
        L["changelog"].append(
            {
                "version": NEW_VERSION,
                "date": DATE,
                "note": (
                    "PR #804 Gemini F1 fix (issuecomment-6863989282): "
                    "encode_housekeeping_batch.py overwrote `verification.verified_at`/"
                    "`verifier` on PROOF-eigenratios / PROOF-cl6 / PROOF-3gen when it "
                    "populated theorems[]/notes for #465 AC5. Restored both fields to their "
                    "original Lean proof-checking provenance (2026-09-02, #621 FAULT-S4-005) "
                    "byte-for-byte; the housekeeping attribution stays in notes/changelog, "
                    "which already carry it. No other field on these anchors changes."
                ),
            }
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}F1 fix: restored verification on {ANCHORS}; ledger {NEW_VERSION}"
    )


if __name__ == "__main__":
    main()
