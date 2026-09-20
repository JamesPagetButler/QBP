#!/usr/bin/env python3
"""Migrate the seven open roots' `kill_condition` from array<string> to array<object>
(canonical schema 0.3.4, confluent-trust#104 `KillConditionEntry`), one object per open
question, with a truthful `closure` kind and a `discharge` that names either the resolving
anchor (route EXISTS) or the FLAG-/CONJ- anchor that TRACKS an open route (route OPEN) —
the convention settled on live-test seq 1506–1509 (qbp-implementor gate lane, cth-implementor
schema lane, qbp-architecture coherence): a physics kill is NEVER relabelled `ruling-rescope`
because no route exists yet; an open route is a concrete tracking record, not an absent field.

Text policy: every original string is kept VERBATIM inside `kill`. Where one string carried
arms of different closure kinds it is SPLIT into one object per arm, each arm's own clause
verbatim followed by the shared tail verbatim; a bracketed "[0.3.4 migration: …]" note is
appended ONLY where the v0.7 wording ('Discharge: none') would otherwise contradict the new
fields. Nothing is re-decided: closure kinds follow the entries' own text.

Four FLAG tracking anchors are minted because the routes they track had no anchor to point at
(the FAULT-S4-005 phantom-reference guard requires a real record). They assert nothing beyond
"this route is open, here is where it is tracked". Written through the confined writer.
Usage: python3 scripts/encode_kill_condition_migration.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DATE = "2026-09-20T00:00:00Z"

MIG = "[0.3.4 migration 2026-09-20: closure/discharge carried by this entry's fields; the v0.7 phrase 'Discharge: none' above meant 'no realised route', which the FLAG- discharge now records as route OPEN (tracked).]"


def flag(fid, name, desc, testable, notes, chain):
    return {
        "id": fid,
        "name": name,
        "tier": 2,
        "provenance": "T",
        "status": "marginal",
        "description": desc,
        "prediction_chain": chain,
        "testable_when": testable,
        "notes": notes,
        "provenance_kind": "theory",
        "foundation_batch": "#654-D3-0.3.4-migration",
        "last_tested_at": DATE,
    }


FLAGS = [
    flag(
        "FLAG-rule-flow-open",
        "The rule's flow on StateSphere has no formal existence/uniqueness or omega-limit statement (open route for AXIOM-1 question 1)",
        "The rule (#635) is a postulate: first-order overdamped descent of the potential V in the metric N (the only metric on record; hosting definition §0 table). Its flow is numerical only (`flow_big.py`, #629; endpoint statistics 0.146 quench / ≈1/3 anneal / 1 ℓ-axis). No Lean statement of the flow exists (Hosting.lean states that `potential` is a function, not a gradient field), no normed structure is placed on CDAlg, and no omega-limit map is defined. AXIOM-1's kill (question 1) fires only on such a proven flow whose omega-limit map is non-injective on positive measure; its own text records that first-order semiflows are injective at finite time. Feasibility (2026-09-20, lean-prover read): finite-time injectivity = backward uniqueness via Grönwall (`ODE_solution_unique_of_mem_Icc_left`), size S once the field is defined; the field's definition needs a normed/inner-product transport of CDAlg (M) and the flow itself (M); global existence L. Nothing here is ruled: the flow's FORM is what #635 already states.",
        "When a Lean definition of the rule's vector field on StateSphere exists with local existence/uniqueness; then when its omega-limit map is characterised on the zero-divisor locus.",
        "Tracking anchor only (route OPEN). Discharge target for AXIOM-1 kill_condition[0] (closure derivation). Owners: #635 (rule postulate), #629 (flow numerics), #647 (trigger).",
        ["PROOF-substrate-hosting-definition"],
    ),
    flag(
        "FLAG-encoding-map-open",
        "The bulk-to-boundary encoding map does not exist on record; which octonion encodes a universe is an earned impasse (open route for the boundary-encoding kills)",
        "No map from a universe to its encoding octonion is defined under either reading of INTERP-holographic-boundary (P2 / P2′). The substrate definition conversation (#639; records PR #664; proofs PR #663) closed CONVERGED with Decision 1 exiting as an earned §10 Impasse Record: assuming completeness and stabiliser-transitivity (both open; proof routes in #663), a non-pole universe's candidate encodings form a canonical ℂP²-bundle over the vacuum manifold with no Aut(𝕊)-natural section; selection must come from data outside Aut(𝕊) or the question dissolves via the datum-free bundle ℍ_s^⊥ ≅ ℍ_s³; ρ-equivariance eliminates P2′ and constrains P2 not at all (PROOF-rho-moves-cd-half-as-set, PROOF-quatdouble-rho-invariant-mul-closed). Falsifier: an Aut(𝕊)-equivariant sectioning operator with no manual input. Also tracks the observational arms (an observable requiring information outside any octonionic encoding; an electromagnetic ℂ distinct from the encoding-selected ℂ; an observable distinguishing the readings) — none on record.",
        "When a defining property of the encoding is DERIVED (not stipulated) from an existing anchor, or the encoding map is exhibited or shown not to exist, or an observable distinguishing P2 from P2′ is on record.",
        "Tracking anchor only (route OPEN). Discharge target for POST-boundary-encoding, POST-observation (O⊆), (E), and INTERP-holographic-boundary arms (b), (c). The three-clause kill rewrite drafted by the conversation is NOT encoded here (later PR).",
        ["PROOF-order-three-automorphism-fixes-ell"],
    ),
    flag(
        "FLAG-observer-exclusivity-open",
        "No observer has been exhibited outside an associative subalgebra of 𝕊, and no theorem forbids one (open route for POST-observer-associativity's observational arm)",
        "POST-observer-associativity postulates that every observer is an entity of an associative subalgebra (clause (a), P1′ + D). The observational falsifier — an observer exhibited outside any associative subalgebra — has no measurement on record and no defined observable; the derivational arm (a non-associative subset on which actions compose) is excluded by PROOF-associative-composition-iff's premise set and is a realised route, not this one.",
        "When an observable is defined whose value could locate an observer outside every associative subalgebra, or when a hosted-physics theorem shows observers cannot be so located.",
        "Tracking anchor only (route OPEN). Discharge target for POST-observer-associativity kill arm (a) (closure measurement).",
        ["PROOF-associative-composition-iff"],
    ),
    flag(
        "FLAG-encoding-level-physical-open",
        "No observation bears on whether a universe's encoding is smaller than the last information-preserving level (open route for META-2's physical arm)",
        "META-2's structural arm is excluded by the proved ladders (PROOF-ops-*-ladder; CDLifting.assoc_diag_left) and cannot fire. Its physical arm — a universe's encoding shown to be a smaller algebra than the last information-preserving level (e.g. an observer's algebra with no octonionic completion; the encoding shown to be ℍ) — has no observable on record. DERIV-encoding-level places the encoding at 8 conditionally on META-2, POST-boundary-encoding and AXIOM-1's open scope question.",
        "When an observable is defined that measures the algebraic dimension of a universe's encoding, or when the encoding map exists (FLAG-encoding-map-open) and its image is computed.",
        "Tracking anchor only (route OPEN). Discharge target for META-2 kill_condition physical arm (closure measurement).",
        ["PROOF-ops-alternativity-ladder"],
    ),
]


def obj(kill, closure, discharge=None):
    o = {"kill": kill, "closure": closure}
    if discharge is not None:
        o["discharge"] = discharge
    return o


def split(text, cut):
    """Return (head, tail) with head = text up to and including `cut` marker's preceding clause; both verbatim."""
    i = text.index(cut)
    return text[:i], text[i:]


def migrate(ed, L):
    def rec(list_name, rid):
        return ed.record(list_name, rid)

    # AXIOM-1
    a1 = rec("axioms", "AXIOM-1")
    q1, q2 = a1["kill_condition"]
    a1["kill_condition"] = [
        obj(q1, "derivation", "FLAG-rule-flow-open"),
        obj(q2, "ruling-rescope"),
    ]

    # POST-boundary-encoding — two arms
    pbe = rec("axioms", "POST-boundary-encoding")
    (s,) = pbe["kill_condition"]
    arm_a = "An observable requiring information not representable in any octonionic encoding"
    arm_b = "the encoding map shown not to exist"
    tail = s[s.index(" — none on record") :]
    assert s.startswith(arm_a) and arm_b in s
    pbe["kill_condition"] = [
        obj(arm_a + tail, "measurement", "FLAG-encoding-map-open"),
        obj(
            arm_b[0].upper() + arm_b[1:] + tail, "derivation", "FLAG-encoding-map-open"
        ),
    ]

    # POST-hosting — one arm, derivation; the route exists (the substrate level has V > 0)
    ph = rec("axioms", "POST-hosting")
    (s,) = ph["kill_condition"]
    ph["kill_condition"] = [obj(s, "derivation", "PROOF-substrate-hosting-definition")]

    # POST-observer-associativity — two arms
    poa = rec("axioms", "POST-observer-associativity")
    (s,) = poa["kill_condition"]
    arm_a = "An observer exhibited outside any associative subalgebra of S (exclusivity failing)"
    arm_b = "a non-associative subset of S on which actions compose (contradicting PROOF-associative-composition-iff's premise set)"
    tail = s[s.index(". Discharge: none") :]
    assert s.startswith(arm_a) and arm_b in s
    poa["kill_condition"] = [
        obj(arm_a + tail + " " + MIG, "measurement", "FLAG-observer-exclusivity-open"),
        obj(
            arm_b[0].upper() + arm_b[1:] + tail + " " + MIG,
            "derivation",
            "PROOF-associative-composition-iff",
        ),
    ]

    # POST-observation — (O⊆), (E): both measurement, both tracked by the encoding-map flag
    po = rec("axioms", "POST-observation")
    o_sub, e_arm = po["kill_condition"]
    po["kill_condition"] = [
        obj(o_sub, "measurement", "FLAG-encoding-map-open"),
        obj(e_arm, "measurement", "FLAG-encoding-map-open"),
    ]

    # META-2 — structural arm (derivation; route exists: the ladders) + physical arm (measurement; open)
    m2 = rec("meta_principles", "META-2")
    (s,) = m2["kill_condition"]
    head, rest = split(s, "Physical arm — ")
    tail = rest[rest.index(" — no observable on record") :]
    phys = rest[: rest.index(" — no observable on record")]
    m2["kill_condition"] = [
        obj(head.rstrip(), "derivation", "PROOF-ops-alternativity-ladder"),
        obj(phys + tail, "measurement", "FLAG-encoding-level-physical-open"),
    ]

    # INTERP-holographic-boundary — three arms
    ih = rec("interpretations", "INTERP-holographic-boundary")
    (s,) = ih["kill_condition"]
    lead = "Which copy of O encodes a universe (P2 vs P2'): fired or discharged "
    arm_a = "by a defining property of the encoding stated as an object (a Cayley–Dickson half → P2' is a theorem; contains the observer's algebra → P2 is)"
    arm_b = "by the encoding MAP (a map forces its domain)"
    arm_c = "by an observable distinguishing the readings"
    tail = s[s.index(" — none on record") :]
    assert s.startswith(lead + arm_a) and arm_b in s and arm_c in s
    ih["kill_condition"] = [
        obj(lead + arm_a + tail, "ruling-rescope"),
        obj(lead + arm_b + tail, "derivation", "FLAG-encoding-map-open"),
        obj(lead + arm_c + tail, "measurement", "FLAG-encoding-map-open"),
    ]


CHANGELOG = {
    "version": "6.2.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: vendored schema 0.3.4 sync (confluent-trust#104, merged 2026-09-20) — the seven open "
        "roots' kill_condition migrated array<string> → array<object> KillConditionEntry {kill, closure, discharge}: "
        "13 entries from 9 strings (arms of different closure kind split, text verbatim). Closure kinds follow each "
        "entry's own text; a discharge names the resolving anchor where a route EXISTS (PROOF-substrate-hosting-"
        "definition, PROOF-associative-composition-iff, PROOF-ops-alternativity-ladder) and a FLAG tracking anchor "
        "where the route is OPEN (four minted: FLAG-rule-flow-open, FLAG-encoding-map-open, "
        "FLAG-observer-exclusivity-open, FLAG-encoding-level-physical-open) — per live-test seq 1506–1509; no "
        "physics kill relabelled ruling-rescope. decision_state value 'ruled' → 'settled' (no record affected). "
        "Nothing ruled, nothing forced; no root added or removed."
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        for f in FLAGS:
            if f["id"] in have:
                raise SystemExit(f"already applied: {f['id']}")
            ed.append("anchors", f)
        migrate(ed, L)
        L["version"] = CHANGELOG["version"]
        ed.touch("version")
        if (
            L.get("last_updated") != DATE
        ):  # a declared no-op is refused by the confined writer
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")
    n = sum(
        len(r["kill_condition"])
        for k in ("axioms", "meta_principles", "interpretations")
        for r in L.get(k, [])
        if r.get("decision_state") == "open"
    )
    print(
        f"{'DRY ' if args.dry_run else ''}applied: 4 FLAG trackers; open-root kill entries now {n} objects"
    )


if __name__ == "__main__":
    main()
