#!/usr/bin/env python3
"""QBP#514 AC3 — record the tier-4 clamp outcome on the five web-stream anchors.

#514 AC1 decided (b): the tier domain [1,3] is a schema invariant; the five v5_24-stream
rows that carried `tier: 4` are web-stream convention drift, not real structure, and the
#509 clamp-to-3 was correct (qbp-oppenheimer assessment + cth-implementor schema
concurrence, #514 issuecomment-6503781802). AC3: the five clamped anchors get a note
recording the outcome, in cth's words (seq3940), "so 3 isn't later mistaken for the
stream's native tier."

This appends a single AC3 note to each anchor's existing `notes` free-text — additive,
no schema bump (cth: "a notes line is additive free-text, not laundering"), and NO ledger
version/changelog bump (a pure annotation of a prior ruling, not a new anchor/theorem —
also keeps this collision-free against the in-flight ledger PRs #788/#787). Confined write
via cth_ledger_edit; idempotent-guarded (skips an anchor already annotated).

Usage: python3 scripts/encode_514_tier_notes.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"

ANCHORS = [
    "CONV-cd-tower-in-zeta-moments",
    "CONV-flow-fragmentalism",
    "CONV-spectral-entropy-zeta",
    "CONJ-condensed-math-for-transition-state",
    "INSIGHT-condensed-math-deferred",
]

TAG = "[#514 AC3]"
NOTE = (
    " [#514 AC3, 2026-10-29] Native v5_24-stream tier value 4, clamped to 3 at the #509 "
    "apply as web-stream convention drift per #514 AC1=(b) (qbp-oppenheimer assessment + "
    "cth-implementor schema concurrence, #514 issuecomment-6503781802): the tier domain "
    "[1,3] is a schema invariant and tier 4 is not real structure. Reopen path: if the "
    "4-tier reading earns theory content it graduates through a confluent-trust design "
    "surface under cth schema authority (qbp-oppenheimer co-signs the semantics). Recorded "
    "so 3 is not later mistaken for the stream's native tier."
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        have = {a["id"] for a in ed.ledger["anchors"]}
        for aid in ANCHORS:
            if aid not in have:
                raise SystemExit(f"anchor missing from ledger: {aid}")
            a = ed.record("anchors", aid)
            cur = a.get("notes")
            if not isinstance(cur, str):
                raise SystemExit(
                    f"{aid}: expected an existing free-text `notes` field to append to"
                )
            if TAG in cur:
                raise SystemExit(f"already applied: {aid} notes already carry {TAG}")
            a["notes"] = cur.rstrip() + NOTE

    print(
        f"{'DRY ' if args.dry_run else ''}#514 AC3: appended the clamp-outcome note to "
        f"{len(ANCHORS)} anchors (notes-only; no version/changelog bump)"
    )


if __name__ == "__main__":
    main()
