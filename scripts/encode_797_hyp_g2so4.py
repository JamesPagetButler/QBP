#!/usr/bin/env python3
"""QBP#797 — mint the Kibble–Zurek hypothesis anchor before the qbp-kz-g2 round-3 run.

Beekeeper ruling 2026-10-30: an oppenheimer-spike names and mints the anchor it
discharges before the run; this one is derived, so the director mints via the
qbp-implementor writer lane under the approved-list rule. Physics text signed by
qbp-oppenheimer (live-test seq4057/4061); encoding chosen with cth-implementor
(schema axis, seq4060/4063/4067) and qbp-architecture (ontology, seq4058/4062/4064).

This is the ledger's FIRST `provenance_kind: hypothesis` anchor (clean precedent).

Encoding (convention-consistent with the CONJ- anchors, cth seq4060/4063 — committed
schema reality):
  * integer `tier: 3` (structural anchor-tier, [1,3]; NOT the F-axis).
  * `provenance: "H"` + `provenance_kind: "hypothesis"`.
  * `status: "contested"` — oppenheimer's physics call (seq4061), arch FINAL (seq4064):
    the 4057 statement as-written carries the ramp clause, which rounds 1–2 confronted;
    cth confirms it satisfies the co-sign (seq4067).
  * `prediction_chain: []` — NO substrate anchor carries the G₂/SO(4) associative-3-
    plane-field model (oppenheimer checked, 0/346); don't invent an edge (arch seq4058).
    The round records are evidence rows in notes, not edges.
  * decision_state/kill_condition are typed only on root $defs, UNENFORCED on anchors —
    so the open-question + kill + closure=measurement + discharge QBP#797 go in `notes`
    (convention route), until cth's typed-hypothesis-key schema surface lands.
  * F = research — the two-axis FormalityF has no typed schema field yet (inter#241
    ontology-adopted, not schema-realized); recorded in `notes` + the qbp-compute-unit#94
    qualifier (MDCU is spike code, F capped at research).
  * The confrontation is TWO claims → TWO E rows in notes (arch seq4058, cth seq4063;
    the E-axis has no typed field yet): (i) the rate-scale quasi-static-crossing claim →
    E = falsified @ spike-harness aa04139 (notary VERIFIED, QBP PR#796); (ii) the anchor's
    own equilibrium-continuity claim → E = unconfronted until round 3. Append-only: a
    continuous round-3 reading ADDS a new E row on the dynamics claim, never edits row (i).

cth-implementor schema co-sign on the mint PR (new id). Version bump 6.20.0 → 6.22.0
(collision-free: 6.21.0 is left for oppenheimer's #787/#755 re-run off the same
post-#788 master). Confined write via cth_ledger_edit; idempotent-guarded.

Usage: python3 scripts/encode_797_hyp_g2so4.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"

NEW_ID = "HYP-g2so4-planefield-continuous-transition"
PREV_VERSION = "6.20.0"
NEW_VERSION = (
    "6.22.0"  # 6.21.0 left for oppenheimer's #787/#755 re-run (collision-free)
)
DATE = "2026-10-30T00:00:00Z"  # mint date (pre-round-3)
DISCHARGE_DATE = "2026-10-31T00:00:00Z"  # round-3 equilibrium test confronted it (#801)
HARNESS_SHA = (
    "aa04139"  # qbp-compute-unit spike harness @ rounds 1–2 (oppenheimer seq4061)
)

NEW_NAME = (
    "G₂/SO(4) plane-field continuous-transition hypothesis (Kibble–Zurek premise)"
)

# oppenheimer's seq4057 statement, as-written (status:contested follows it, arch seq4064).
STATEMENT = (
    "The G₂/SO(4) plane-field sigma model (chordal energy, Model-A relaxation, L = 16 "
    "reference lattice) has a continuous ordering transition at its T_c, so a slow "
    "temperature ramp crosses it quasi-statically (the Kibble–Zurek premise)."
)

NOTES = (
    "QBP#797 (qbp-kz-g2 spike; director qbp-oppenheimer, minted via the qbp-implementor "
    "writer lane per the beekeeper's 2026-10-30 approved-list ruling, BEFORE round 3 per "
    "the 'mint the anchor the run discharges before the run' rule). FIRST hypothesis-kind "
    "anchor in the ledger. "
    "F = napkin (qbp-compute-unit#94: every MDCU-derived result is F = napkin — research is "
    "only the ceiling after the engineering path, not the current grade; arch #801 §I4 "
    "seq425). The two-axis FormalityF has no typed schema field yet (inter#241 ontology-"
    "adopted, not schema-realized); migrates to a typed F-field when it lands. "
    "CONFRONTATION — two claims, two E rows (arch seq4058 / cth seq4063; E-axis not yet "
    "schema-typed, recorded as scoped prose): "
    "(i) the quasi-static-crossing claim over τ_Q 1600–12800 → E = falsified, as "
    "implemented in the spike harness at qbp-compute-unit " + HARNESS_SHA + " (notary "
    "VERIFIED, QBP PR#796; rounds 1–2 hysteresis 0.52 → 0.48 of S_max over τ_Q 1600–12800). "
    "(ii) the anchor's own claim (continuous ordering transition in EQUILIBRIUM) → E = "
    "FALSIFIED at round 3 (QBP PR#801, 'H-FO by frozen rule (a)': the pre-registered "
    "equilibrium finite-size test — energy/S histograms + Binder cumulant at L = 8, 12, 16 — "
    "read FIRST-ORDER). This is the claim's first confrontation (unconfronted → falsified), "
    "not an edit of row (i); APPEND-ONLY intact — row (i)'s rounds-1–2 verdicts are "
    "immutable, and because round 3 read first-order (not continuous) the frozen "
    "reclassification branch did NOT fire. "
    "EVIDENCE (rows, not edges): Landau-cubic argument — the projector order parameter ⇒ "
    "tr(Π³) ⇒ first-order a priori (inter#249 wisdom; borne out at round 3); round records "
    "qbp-compute-unit#92/#93 + QBP PR#796 (r1/r2) + QBP PR#801 (r3). "
    'KILL — FIRED (decision settled): the pre-registered question "Is the ordering '
    'transition first-order or continuous in equilibrium (no ramp)?" was answered FIRST-'
    "ORDER by its frozen rule (a) at round 3 ⇒ the hypothesis is FALSIFIED. (The frozen "
    "alternative branch — reads continuous ⇒ rate-scale falsification reclassified as "
    "dynamics, KZ premise restored — did not trigger; it was legitimate only because frozen "
    "before round 3, arch seq4058 point 2.) CLOSURE: the equilibrium finite-size test "
    "(measurement), delivered at #801. DISCHARGE: QBP#797. "
    "SUBSTRATE GAP: no existing anchor carries the G₂/SO(4) associative-3-plane-field model "
    "(oppenheimer checked 0/346) — filed as a substrate-doc item, not minted in passing; "
    "prediction_chain stays [] until one is minted. "
    "Physics signed qbp-oppenheimer; encoding with cth-implementor (schema) + qbp-"
    "architecture (ontology, inter#241); minted contested pre-round-3, discharged to "
    "FALSIFIED on the round-3 record (#801); cth schema co-sign on the PR."
)


def new_anchor():
    return {
        "id": NEW_ID,
        "name": NEW_NAME,
        "tier": 3,
        "provenance": "H",
        "provenance_kind": "hypothesis",
        "status": "falsified",
        "description": STATEMENT,
        "prediction_chain": [],
        "layer_tag": "H",
        "last_tested_at": DISCHARGE_DATE,
        "notes": NOTES,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    rec = new_anchor()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        if NEW_ID in have:
            raise SystemExit(f"already applied: {NEW_ID} present")
        ed.append("anchors", rec)
        L["version"] = NEW_VERSION
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(
            {
                "version": NEW_VERSION,
                "date": DISCHARGE_DATE,
                "note": (
                    f"QBP#797: minted {NEW_ID} — the ledger's first provenance_kind:hypothesis "
                    f"anchor (G₂/SO(4) plane-field continuous-transition / Kibble–Zurek "
                    f"premise). Minted contested BEFORE the qbp-kz-g2 round-3 run (beekeeper "
                    f"'mint before the run' rule); discharged to **status: falsified** on the "
                    f"round-3 record (QBP PR#801, 'H-FO by frozen rule (a)' — the pre-registered "
                    f"equilibrium finite-size test at L=8,12,16 read FIRST-ORDER, firing the "
                    f"kill). tier 3; F=napkin (qbp-compute-unit#94, not research — arch #801 §I4 "
                    f"seq425); two E rows in notes [(i) rate-scale quasi-static-crossing τ_Q "
                    f"1600–12800 = falsified @ harness {HARNESS_SHA}, notary VERIFIED PR#796; "
                    f"(ii) equilibrium-continuity = falsified @ round 3 PR#801 — first "
                    f"confrontation, append-only intact]; kill FIRED / decision settled / "
                    f"discharge QBP#797 in notes (convention route — decision_state/"
                    f"kill_condition unenforced on anchors, cth typed-key surface pending); "
                    f"prediction_chain [] (no substrate anchor carries the G₂/SO(4) associative-"
                    f"3-plane-field model — substrate-doc gap, oppenheimer-filed). Physics qbp-"
                    f"oppenheimer; encoding cth (schema) + arch (ontology inter#241); cth schema "
                    f"co-sign on the PR."
                ),
            }
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}minted {NEW_ID}: tier 3, status FALSIFIED "
        f"(discharged at round 3), prediction_chain []; ledger {NEW_VERSION}"
    )


if __name__ == "__main__":
    main()
