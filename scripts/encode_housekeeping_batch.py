#!/usr/bin/env python3
"""Housekeeping close-out batch (oppenheimer seq4276; beekeeper drive-the-gate-to-zero).

ONE Tier-3 ledger PR, confined writer. oppenheimer signs the theory statements; cth
co-signs the schema. Ledger legs here; the root-audit-register.json surgery (#657
open_roots, #656 chain_debt) is a SEPARATE surgical edit (that file is not the ledger).

Legs (ledger `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json`):

 * #465 AC5 — populate `theorems[]` on the three derivation anchors PROOF-eigenratios /
   PROOF-cl6 / PROOF-3gen from qbp-oppenheimer's 2026-10-29 GaugeBosons.lean §A/§B/§C
   locate table (all 12 names verified to resolve on master). Add a caveat `notes` line
   per the header items. proof_file / provenance_kind (derivation) unchanged; source_sha
   at current master. oppenheimer signs the three statements.

 * #657 (#654 D1) — the two root-prefixed `META-*-field` ids in `anchors[]` are ledger
   field-documentation, not physical roots (smuggled roots). Rename out of the root prefix
   space to `DEFN-*` with `id_history`, re-point any citations. (The two matching
   `open_roots` entries are removed from the register in the companion surgical edit.)

--derived-from style guards: every #465 witness must resolve in GaugeBosons.lean; the
rename keeps the record byte-identical except id + id_history; no citation left dangling.

Usage: python3 scripts/encode_housekeeping_batch.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
GAUGE = "proofs/QBP/GaugeBosons.lean"
NEW_VERSION = "6.23.0"
DATE = "2026-11-01T00:00:00Z"

# ---- #465 AC5: theorems[] from oppenheimer's locate table + caveat notes ----
THEOREMS_465 = {
    "PROOF-eigenratios": (
        [
            "eigenvalue_ratios",
            "eigenvalue_ratio_factor",
            "nonzero_eigenspace_dims",
            "hessian_spectrum_moments",
            "hessian_multiplicities_unique",
        ],
        "theorems[] populated per #465 AC5 (oppenheimer locate table, GaugeBosons.lean §A "
        "l.73–140). Caveat: the operator spectrum is inherited from PROOF-hessian as "
        "hypotheses, not re-derived here (GaugeBosons.lean header item 1).",
    ),
    "PROOF-cl6": (
        [
            "charge_spectrum",
            "charge_quantisation",
            "charge_multiplicities",
            "total_state_count",
            "particle_charge_sum_value",
            "anomaly_cancellation",
        ],
        "theorems[] populated per #465 AC5 (oppenheimer locate table, GaugeBosons.lean §B "
        "l.142–212). Caveat: the 1/3-charge-quantisation's rational consequences are proven; "
        "the Cl(6) ⊗ 𝕆 action itself is NOT formalised (GaugeBosons.lean header item 2).",
    ),
    "PROOF-3gen": (
        ["im_quaternion_dim_three"],
        "theorems[] populated per #465 AC5 (oppenheimer locate table, GaugeBosons.lean §C "
        "l.214–235). Caveat: only dim(Im ℍ) = 3 is proven; 'three generations' is an "
        "interpretation (already in the description).",
    ),
}

# ---- #657: META-*-field → DEFN-*-field rename (out of the root prefix space) ----
RENAMES_657 = {
    "META-physical-mapping-status-field": "DEFN-physical-mapping-status-field",
    "META-regime-of-validity-field": "DEFN-regime-of-validity-field",
}


def resolves_in_gauge(name):
    src = (ROOT / GAUGE).read_text(encoding="utf-8")
    return any(
        line.lstrip().startswith(h + name)
        for line in src.splitlines()
        for h in ("theorem ", "lemma ", "def ")
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    # #465 witness-resolution guard
    for _a, (thms, _n) in THEOREMS_465.items():
        for t in thms:
            if not resolves_in_gauge(t):
                raise SystemExit(f"#465 witness does not resolve in {GAUGE}: {t}")

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        ids = {a["id"] for a in L["anchors"]}

        # ---- #465 AC5 ----
        for aid, (thms, caveat) in THEOREMS_465.items():
            if aid not in ids:
                raise SystemExit(f"#465 anchor missing: {aid}")
            a = ed.record("anchors", aid)
            if a.get("theorems"):
                raise SystemExit(f"#465 {aid}: theorems[] already populated")
            a["theorems"] = [{"name": t, "status": "verified"} for t in thms]
            cur = a.get("notes")
            a["notes"] = (
                (cur.rstrip() + " " + caveat) if isinstance(cur, str) else caveat
            )
            v = a.get("verification")
            if isinstance(v, dict):
                v["verified_at"] = DATE
                v["verifier"] = (
                    f"#465 AC5 (qbp-implementor writer lane): theorems[] populated from "
                    f"qbp-oppenheimer's locate table @ current master; all names resolve in "
                    f"{GAUGE}. Theory statements signed by qbp-oppenheimer on the batch PR."
                )

        # ---- #657 rename (remove + re-append with id_history), re-point citations ----
        for old, new in RENAMES_657.items():
            if old not in ids:
                raise SystemExit(f"#657 anchor missing: {old}")
            if new in ids:
                raise SystemExit(f"#657 target id already exists: {new}")
        for old, new in RENAMES_657.items():
            rec = ed.remove("anchors", old)
            rec["id"] = new
            hist = rec.get("id_history") or []
            hist.append(old)
            rec["id_history"] = hist
            ed.append("anchors", rec)
        # re-point any citation of the old ids (prediction_chain / derived edges) across records
        oldset = set(RENAMES_657)
        for key in ("anchors", "derived_principles", "chains", "inputs"):
            for rec in L.get(key, []):
                for field in ("prediction_chain", "derived_from"):
                    chain = rec.get(field)
                    if isinstance(chain, list) and oldset.intersection(chain):
                        rec[field] = [RENAMES_657.get(c, c) for c in chain]
                        ed.record(key, rec["id"])  # declare the citation edit

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
                    "Housekeeping close-out batch (oppenheimer seq4276). "
                    "#465 AC5: theorems[] populated on PROOF-eigenratios / PROOF-cl6 / "
                    "PROOF-3gen from the GaugeBosons.lean §A/§B/§C locate table (all names "
                    "resolve @ master; caveats in notes; derivation anchors, proof_file "
                    "unchanged; theory statements signed by qbp-oppenheimer). "
                    "#657 (#654 D1): META-physical-mapping-status-field / "
                    "META-regime-of-validity-field renamed out of the root prefix space to "
                    "DEFN-* (id_history kept, citations re-pointed) — field-documentation, "
                    "not roots; the two open_roots register entries are removed in the "
                    "companion root-audit-register.json edit (shrink-only). "
                    "cth-implementor schema co-sign on the PR."
                ),
            }
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}batch: #465 theorems[] on 3 anchors; "
        f"#657 renamed {list(RENAMES_657.values())}; ledger {NEW_VERSION}"
    )


if __name__ == "__main__":
    main()
