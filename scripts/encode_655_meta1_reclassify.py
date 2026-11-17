#!/usr/bin/env python3
"""QBP#655 (#654 D6) — reclassify META-1 out of the root population.

Beekeeper-approved writer-lane ask (qbp-implementor). qbp-oppenheimer's theory
ruling (binding, not re-derived here): META-1 ("Change is constant" — "No
framework is guaranteed complete. All knowledge is provisional within its
axiomatic system.") is an epistemic meta-principle about the ledger, not a
physical root. Verified by grep: nothing in the ledger cites META-1 via
`derived_from`/`prediction_chain`/`forced_by`. Disposition: move it OUT of the
root population.

Encoding (writer-lane judgment call, documented for review):
  * `meta_axiom` is a single top-level OBJECT (not a list) holding exactly
    META-1. `scripts/root_audit.py`'s ROOT_LISTS = ("meta_axiom",
    "meta_principles", "axioms", "interpretations") treats it as a one-record
    root population, via its `_as_list()` helper (root_audit.py) / `_records()`
    helper (cth_ledger_edit.py) — both already handle `meta_axiom` absent as
    an empty population (`_as_list(None) == []`; `ledger.get(key, []) or []`
    on an absent key is also `[]`). `anchors[]` is NOT one of the four
    ROOT_LISTS keys, so moving the record there removes it from the root gate
    structurally, no schema change needed for THIS purpose.
  * CHECKED: `meta_axiom` is NOT in `docs/cth/inventory.schema.v0.3.json`'s
    top-level `required` list (only programme/version/axioms/anchors/chains
    are required) — so deleting the `meta_axiom` key entirely is schema-valid,
    least-invasive, and avoids leaving a stale/placeholder object behind.
  * CHECKED: no script other than root_audit.py and cth_ledger_edit.py
    references `meta_axiom` (grepped scripts/, docs/, archive/, and *.go —
    zero Go hits). Both handle an absent key as an empty population already
    (see above) — confirmed by reading root_audit.py's `_as_list` (l.119-122)
    and `kill_routes` (l.263-282, guarded by `isinstance(rec, dict)`).
  * CHECKED: `anchors[]`'s Anchor schema (`$defs.Anchor`) requires
    `id, name, tier, provenance, status, description, prediction_chain` and
    has `additionalProperties: true`. The issue's suggested minimal shape
    (id/name/statement/id_history) is short of the Anchor schema's required
    set, so this record carries BOTH: `description` (required; duplicates the
    original `statement` text so the schema is satisfied) and `statement`
    (additionalProperty; keeps the exact original field name/value for
    provenance/continuity with the pre-move record). `id_history: ["META-1"]`
    records the prior id.
  * New id `WISDOM-change-is-constant`: precedent for a non-proof,
    programme-level-lesson anchor at this minimal shape is
    `WISDOM-algebra-restricts-state-class-not-scalar-field` (id, name, tier,
    status, provenance, provenance_kind, prediction_chain, description — no
    other fields) — this record mirrors that shape plus `statement` +
    `id_history`. `WISDOM-` is not a root prefix (root_audit.py's
    ROOT_PREFIXES = ("AXIOM-", "POST-", "META-", "INTERP-")), so it cannot be
    flagged as a smuggled root.
  * tier 1 / provenance "T" / provenance_kind "theory" / status "coherent":
    matches the two existing non-contested WISDOM-* precedents
    (WISDOM-schema-vs-instance, WISDOM-003-there-is-only-f-u), not the
    contested-hypothesis shape of HYP-*.
  * `prediction_chain: []`: matches both existing non-contested WISDOM-*
    precedents; root_audit.py's D2 chain-termination gate does not apply to a
    WISDOM- id with provenance_kind theory (the gate is scoped to
    derived_principles / DERIV-*/PRED-* / provenance_kind
    derivation/internal-compute — root_audit.py l.52-55).

Register: `docs/cth/root-audit-register.json`'s `open_roots` META-1 entry is
removed in the same PR (shrink-only; direct edit, outside the ledger_edit
confinement — it is not the ledger file).

Version bump 6.24.0 -> 6.25.0 (rebase round, qbp-oppenheimer on live-test
seq 5111: #814 merged first — ledger was at 6.23.0 when this script was
first written, moved to 6.24.0 by #814's merge — so the next free version
is 6.25.0). Confined write via cth_ledger_edit; idempotent-guarded.

Fix round (qbp-architecture Red Team, issuecomment on #812, 2026-11-16): the
first rebase run used DATE = "2026-11-15T00:00:00Z", which is EARLIER than
6.24.0's own last_updated (2026-11-15T17:59:52Z) — a timestamp that goes
backwards. Fixed to 2026-11-16T00:00:00Z (the real day of this re-run,
safely after 6.24.0's).

Fix round 2 (qbp-architecture Red Team, issuecomment on #812, 2026-11-17,
"the committed writer no longer reproduces the committed ledger"): the
previous fix round patched last_updated/the changelog date directly on the
ledger via a one-off script WITHOUT updating this constant, so this script
and the ledger it's supposed to reproduce drifted apart. Fixed by setting
DATE here to the real value (2026-11-16T16:45:00Z) and re-running fresh
from master, rather than patching the ledger again out of band — the
committed encoder and the committed ledger are back in lockstep.

Usage: python3 scripts/encode_655_meta1_reclassify.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"

OLD_ID = "META-1"
NEW_ID = "WISDOM-change-is-constant"
NEW_VERSION = "6.25.0"
DATE = "2026-11-16T16:45:00Z"

NAME = "Change is constant"
STATEMENT = (
    "No framework is guaranteed complete. All knowledge is provisional "
    "within its axiomatic system."
)

NOTES = (
    "QBP#655 (#654 D6): reclassified out of the root population per "
    "qbp-oppenheimer's theory ruling — META-1 is an epistemic meta-principle "
    "about the ledger itself, not a physical root; grepping the ledger "
    "confirms no record cites META-1 via derived_from/prediction_chain/"
    "forced_by. Moved from the single-object `meta_axiom` top-level key "
    "(now removed entirely — not in inventory.schema.v0.3.json's top-level "
    "`required` list) into `anchors[]` under a WISDOM- id: `anchors[]` is "
    "not one of root_audit.py's ROOT_LISTS, so this removes META-1 from the "
    "D1 root gate structurally. `name`/`statement` text unchanged from "
    "META-1 (also carried as `description` to satisfy the Anchor schema's "
    'required field). `id_history: ["META-1"]` preserves the prior id. '
    "Register: docs/cth/root-audit-register.json's open_roots META-1 entry "
    "removed in the same PR (shrink-only)."
)


def new_anchor():
    return {
        "id": NEW_ID,
        "name": NAME,
        "tier": 1,
        "provenance": "T",
        "provenance_kind": "theory",
        "status": "coherent",
        "description": STATEMENT,
        "prediction_chain": [],
        "statement": STATEMENT,
        "id_history": [OLD_ID],
        "last_tested_at": DATE,
        "notes": NOTES,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        if NEW_ID in have:
            raise SystemExit(f"already applied: {NEW_ID} present")
        if "meta_axiom" not in L:
            raise SystemExit("already applied: meta_axiom absent")
        old = L["meta_axiom"]
        if old.get("id") != OLD_ID:
            raise SystemExit(
                f"meta_axiom id is {old.get('id')!r}, expected {OLD_ID!r} — "
                f"refusing to blind-remove an unexpected record"
            )

        del L["meta_axiom"]
        ed.touch("meta_axiom", OLD_ID)
        ed.touch("meta_axiom")

        ed.append("anchors", new_anchor())

        L["version"] = NEW_VERSION
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(
            {
                "version": NEW_VERSION,
                "date": DATE,
                "note": (
                    f"QBP#655 (#654 D6): reclassified {OLD_ID} out of the root "
                    f"population — removed the single-object `meta_axiom` "
                    f"top-level key (not schema-required) and minted {NEW_ID} "
                    f"in `anchors[]` (not a ROOT_LISTS key) carrying the same "
                    f"name/statement text + id_history:[{OLD_ID!r}]. "
                    f"Theory ruling: qbp-oppenheimer (META-1 is an epistemic "
                    f"meta-principle about the ledger, cited by nothing via "
                    f"derived_from/prediction_chain/forced_by). Encoding: "
                    f"qbp-implementor writer lane. "
                    f"docs/cth/root-audit-register.json's open_roots {OLD_ID} "
                    f"entry removed in the same PR (shrink-only)."
                ),
            }
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}reclassified {OLD_ID} -> {NEW_ID} "
        f"(anchors[], tier 1, status coherent); removed meta_axiom key; "
        f"ledger {NEW_VERSION}"
    )


if __name__ == "__main__":
    main()
