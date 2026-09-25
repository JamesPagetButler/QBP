#!/usr/bin/env python3
"""PROOF anchors for the transition-state theorems (PR #679, #473 kill-attack 5) — encode-AFTER-prove.

Three anchors, the theorems Gemini named at 0d09538: (1) the 14-dimensional tangent space of the state
sphere and the 13/14 count of V-neutral directions (the potential's first-order data constrains AT MOST
one direction — exactly one where the tangential gradient is nonzero, none at rest points, crystals AND
the in-flight frozen ridge {V = 1}); (2) adding a V-neutral vector to a rule field leaves V's first-order
data unchanged (every level-set invariant is rule-blind); (3) the hosting identity s·(s·x) = −N(s)·x of
PROOF-crystal-hosts-quaternion fails at every in-flight state. Anchors 1–2 cite
proofs/QBP/Foundations/TransitionState.lean (this PR, 17/17 audited, 0-sorry, `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}); anchor 3 cites the Substrate theorem
`QBP.Substrate.Hosting.inFlight_no_quaternion_closure` (Hosting.lean, #639, already carried by
PROOF-substrate-hosting-definition) — C3 requires each witness to resolve in the anchor's own proof_file,
so anchor 3's proof_file is Hosting.lean and `RuleFlow.potential_normalise_witness` (a different file)
is a CITATION in its description, not a witness. Reviewed: Red Team Tier 3 APPROVE-WITH-CONCERN with
M1–M4 applied at 0d09538; Gemini Tier 3 APPROVE at 0d09538.

NEGATIVE CONSTRAINT (Gemini, binding): no anchor claims that Ext¹ was computed or evaluated to zero
(the pinned Mathlib has no EnoughProjectives for Cond(Ab)); no anchor claims "no 4-dimensional
subalgebra containing {1, s, ℓ} exists in flight" or "the hosting bundle's fibre is empty" — only that
the hosting IDENTITY fails. No root, principle, decision or kill is touched; the CONJ record itself is
#680's. Manifest entries added alongside; then `anchor_inverse_audit.py --update-baseline` records the
anchored growth.
Usage: python3 scripts/encode_transition_state_anchors.py [--dry-run]
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
MANIFEST = ROOT / "docs/cth/anchor-worthy-manifest.json"
LAKE = ROOT / "proofs/lake-manifest.json"
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()
DATE = "2026-09-25T00:00:00Z"
BATCH = "#679-transition-state"
TS = "QBP.Foundations.TransitionState."
HO = "QBP.Substrate.Hosting."
F_TS = "proofs/QBP/Foundations/TransitionState.lean"
F_HO = "proofs/QBP/Substrate/Hosting.lean"
REVIEWS = (
    "PR #679 Red Team Tier 3 APPROVE-WITH-CONCERN at e556473 with M1–M4 applied at 0d09538, "
    "Gemini Tier 3 APPROVE at 0d09538"
)
VERIFIER_TS = (
    "run-bounded 6G 1800 taskset -c 3-5 lake build QBP.Foundations.TransitionState (2952 jobs, exit 0; "
    "TransitionState built in 6.2 s; CI lake build PASS at 0d09538) + #print axioms on all 17 audited "
    "declarations (note §10, verbatim from the build log; qbp-oppenheimer, 2026-09-24; "
    + REVIEWS
    + ")"
)
VERIFIER_HO = (
    "lake build + #print axioms on proofs/QBP/Substrate/Hosting.lean (#639 hosting groundwork, "
    "2026-09-07, carried by PROOF-substrate-hosting-definition); re-attested by CI lake build PASS at "
    "0d09538 (PR #679; the Hosting.lean audit block prints inFlight_no_quaternion_closure); cited and "
    "re-read in "
    + REVIEWS
    + " (Red Team F4 narrowed the gloss to what the theorem states)"
)
NOT_EXT = (
    " NOT claimed: that Ext¹(ℍ_cond, 𝕆_cond) — or any Ext group in Cond(Ab) — was computed or evaluated "
    "(not evaluable in the pinned Mathlib: no EnoughProjectives / no derived-functor Ext for condensed "
    "abelian groups); nothing about the flow's existence, orbits, the crystallisation endpoint ⟨b₀²⟩, "
    "or the condensed category."
)


def _libs():
    m = json.loads(LAKE.read_text())
    return {
        p["name"]: {"ref": p.get("inputRev") or p["rev"], "sha": p["rev"]}
        for p in m["packages"]
        if p["name"] in ("mathlib", "batteries")
    }


def anchor(aid, name, desc, main, companions, chain, proof_file, verifier):
    wits = [main] + companions
    return {
        "id": aid,
        "name": name,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": desc,
        "proof_file": proof_file,
        "proof_language": "lean4",
        "proof_state": "verified",
        "lean_theorem": main,
        "lean_companion_theorems": companions,
        "sorry_count": 0,
        "provenance": "T",
        "prediction_chain": chain,
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": _libs(),
            "verified_at": DATE,
            "verifier": verifier,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": wits,
        },
    }


ANCHORS = [
    anchor(
        "PROOF-in-flight-first-order-data-constrains-at-most-one-direction",
        "At every point of the state sphere the tangent space is 14-dimensional and the potential's first-order data constrains AT MOST one direction: exactly one where the tangential gradient is nonzero (13 V-neutral), none at rest points — crystals AND the in-flight frozen ridge {V = 1} (14)",
        "Foundations/TransitionState.lean (#473 kill-attack 5; pure linear algebra on CDAlg ℝ 4 ≅ ℝ¹⁶, imports "
        "Mathlib + Foundations.{CDDimension, Alternator} only). Hypotheses (note §4.2): s with bil s s = 1 and "
        "s.coord 0 = 0 — i.e. a point of the SET StateSphere (definitionally Hosting.StateSphere via N_eq_bil, "
        "matched but never imported); g ∈ Tangent s with g ≠ 0. `finrank_tangent`: Tangent s := ker(x ↦ (⟪x,s⟫, x₀)) "
        "has finrank 14 at EVERY such s — a linear subspace of ℝ¹⁶ attached to a point of the set StateSphere, NOT "
        "a manifold tangent space T_sΣ (no topology, smooth structure or chart occurs in the file). "
        "`finrank_vNeutral`: VNeutral s g := ker(x ↦ (⟪x,s⟫, x₀, ⟪x,g⟫)) has finrank exactly 13 under those "
        "hypotheses; `vNeutral_eq_tangent_of_gradient_zero`: VNeutral s 0 = Tangent s (14) for every s. The "
        "intended g is the TANGENTIAL gradient of the landscape potential, g = −RuleFlow.ruleField s, NOT the raw "
        "∇V(s): V is quartic-homogeneous (RuleFlow.potential_smul), so Euler gives ⟪∇V(s), s⟫ = 4·V(s) > 0 in "
        "flight and ∇V(s) ∉ Tangent s there. The two bridge theorems `vNeutral_add_normal` "
        "(VNeutral s (a•s + b•1 + g) = VNeutral s g) and `vNeutral_neg` (VNeutral s (−g) = VNeutral s g), with the "
        "CITED RuleFlow.gradV_decomp (∇V(s) = −F(s) + ⟪∇V(s),s⟫•s + (∇V(s))₀•1) and RuleFlow.fderiv_potential_apply "
        "(fderiv ℝ V s v = ⟪∇V s, v⟫), give VNeutral s (∇V s) = VNeutral s (ruleField s) — so on tangent vectors g "
        "carries exactly V's first-order data. Reading: of the 14 directions a rule may point in, V constrains at "
        "most one everywhere; exactly one where ruleField s ≠ 0; NONE at rest points of ruleField — the crystals "
        "(RuleFlow.ruleField_eq_zero_of_isVacuum) AND the in-flight frozen ridge {s ∈ Σ | V s = 1} "
        "(RuleFlow.ruleField_eq_zero_of_potential_eq_one; non-empty by RuleFlow.potential_normalise_witness; "
        "in flight since V = 1 > 0), where the count is 14, not 13. '13 at ANY in-flight state' is FALSE and is "
        "not claimed (Red Team M1). Non-vacuity: `hypotheses_satisfiable` exhibits s = e₁, g = e₂ meeting every "
        "hypothesis. The identification g = −ruleField s is a citation of RuleFlow (Substrate), not a theorem of "
        "this Foundations file." + NOT_EXT,
        TS + "finrank_vNeutral",
        [
            TS + "finrank_tangent",
            TS + "vNeutral_eq_tangent_of_gradient_zero",
            TS + "vNeutral_add_normal",
            TS + "vNeutral_neg",
            TS + "hypotheses_satisfiable",
        ],
        ["PROOF-substrate-hosting-definition"],
        F_TS,
        VERIFIER_TS,
    ),
    anchor(
        "PROOF-level-set-invariants-rule-blind",
        "Adding any V-neutral vector to a candidate rule field leaves V's first-order data unchanged: every level-set invariant sees a rule only through dV(F), so any object built from V's level-set topology alone is constant as the rule varies (quench and anneal give the identical object)",
        "Foundations/TransitionState.lean (#473 kill-attack 5). `add_vNeutral_preserves_data`: for Y ∈ Tangent s and "
        "X ∈ VNeutral s g, Y + X ∈ Tangent s (still on the sphere, still imaginary to first order) and "
        "bil (Y + X) g = bil Y g — the same first-order rate of change of V (bil · g is fderiv V s · by the CITED "
        "RuleFlow.fderiv_potential_apply, with g the tangential gradient −ruleField s per "
        "PROOF-in-flight-first-order-data-constrains-at-most-one-direction). `add_vNeutral_ne`: Y + X ≠ Y whenever "
        "X ≠ 0, and `exists_vNeutral_ne_zero`: a nonzero V-neutral X exists at every state where g is tangential "
        "and nonzero (a fortiori at rest points, where VNeutral = Tangent) — so the deformation is a genuine change "
        "of rule. Inference (note §4.2, an argument from the theorem, not a further theorem): any selection "
        "principle expressible in the data of V's level sets sees a candidate rule F only through dV(F), hence its "
        "solution set is closed under adding an arbitrary V-neutral field; every object that is a functional of "
        "V's level-set topology alone — the in-flight candidates D1 (sublevel filtration / vacuum cofiber), D2 "
        "(zero-divisor pair) and D3 (hosting bundle) of the note — is rule-blind by construction: quench and anneal "
        "yield the identical object, so no such object can supply Prop 13(b)'s missing selection. Kill basis for "
        "conjecture clause (b): rule-blindness plus the ABSENCE of a state/time variable in "
        "Ext¹(ℍ_cond, 𝕆_cond) (a constant of the category, not a clock). NOT claimed: that clause (b) is "
        "'identically zero' — WITHDRAWN (Red Team M3): HH²(ℍ,ℍ) = 0 rigidifies ℍ's PRODUCT, but the embedding "
        "ℍ ↪ 𝕆 has 8-dimensional moduli T(G₂/SO(4)), nonzero and kinematic; NOT claimed: any reversal of Prop 13(b) "
        "or of KILLED-locale-forcing-route." + NOT_EXT,
        TS + "add_vNeutral_preserves_data",
        [TS + "add_vNeutral_ne", TS + "exists_vNeutral_ne_zero"],
        ["PROOF-substrate-hosting-definition"],
        F_TS,
        VERIFIER_TS,
    ),
    anchor(
        "PROOF-hosting-identity-fails-in-flight",
        "At every in-flight state the hosting identity s·(s·x) = −N(s)·x of PROOF-crystal-hosts-quaternion fails: ¬∀x — the crystal-hosting construction has no in-flight instance",
        "Substrate/Hosting.lean (#639; the theorem PR #679's D3-repair kill rests on, re-read under Red Team F4). "
        "`inFlight_no_quaternion_closure`: s ∈ InFlight ⇒ ¬(∀ x, s * (s * x) = (−N s) • x) — the input identity of "
        "PROOF-crystal-hosts-quaternion (CrystalHosting.left_mul_sq_scalar_iff_vacuum read contrapositively) "
        "fails at every in-flight state, so the construction that hosts span{1, u, ℓ, ℓu} ≅ ℍ at a crystal is not "
        "available in flight and there is no candidate local section for a hosting bundle to glue. "
        "`inFlight_no_complex_structure`: the same on the unit sphere (¬∀ x, s·(s·x) = −x); "
        "`mem_universeSpace_iff_complex_structure`: for s ∈ StateSphere, s ∈ UniverseSpace ↔ ∀ x, s·(s·x) = −x — "
        "the two regions separated by an iff; `inFlight_nonempty`: the in-flight region is non-empty (a "
        "normalised zero-divisor witness), so the statement is not vacuous; the in-flight frozen ridge {V = 1} is "
        "also non-empty by the CITED RuleFlow.potential_normalise_witness (RuleFlow.lean, not a witness of this "
        "anchor). NOT claimed: that 'no 4-dimensional subalgebra containing {1, s, ℓ} exists in flight' — a "
        "4-dim subalgebra could in principle exist without s acting as a complex structure on all of 𝕊; NOT "
        "claimed: that 'the hosting bundle's fibre is empty over in-flight points' (both glosses WITHDRAWN from "
        "the note's §3.3 / §5.1 under Red Team F4); only that the specific hosting IDENTITY fails. NOT claimed: "
        "anything about the flow or the crystallisation endpoint." + NOT_EXT,
        HO + "inFlight_no_quaternion_closure",
        [
            HO + "inFlight_no_complex_structure",
            HO + "mem_universeSpace_iff_complex_structure",
            HO + "inFlight_nonempty",
        ],
        ["PROOF-crystal-hosts-quaternion", "PROOF-substrate-hosting-definition"],
        F_HO,
        VERIFIER_HO,
    ),
]

CHANGELOG = {
    "version": "6.8.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the transition-state theorems (PR #679; #473 kill-attack 5 on "
        "CONJ-condensed-math-for-transition-state (a)–(c) / Prop 13(b)) — encode-after-prove, the theorems Gemini "
        "named: at every point of the state sphere the tangent space (a subspace of ℝ¹⁶ over the SET StateSphere, "
        "not a manifold tangent space) is 14-dimensional and V's first-order data constrains AT MOST one direction — "
        "exactly one where the tangential gradient −ruleField s is nonzero (13 V-neutral), none at rest points, "
        "the crystals AND the in-flight frozen ridge {V = 1} (14); adding a V-neutral vector to a rule field leaves "
        "V's first-order data unchanged, so every level-set invariant is rule-blind (quench and anneal give the "
        "identical object); the hosting identity s·(s·x) = −N(s)·x of PROOF-crystal-hosts-quaternion fails at every "
        "in-flight state. Three anchors, all 0-sorry, axiom closure {propext, Classical.choice, Quot.sound} "
        "(TransitionState 17/17 audited; Hosting.lean carried since #639). Negative constraints obeyed in every "
        "anchor: Ext¹ NOT computed or evaluated to zero (no EnoughProjectives in the pinned Mathlib; 'identically "
        "zero' withdrawn — the embedding ℍ ↪ 𝕆 has 8-dim moduli T(G₂/SO(4))); NOT claimed that no 4-dim subalgebra "
        "exists in flight or that the hosting fibre is empty — only that the hosting identity fails. No root, "
        "principle, decision or kill touched; the CONJ record's kill/testable_when belong to #680. (Version 6.8.0: "
        "rebased onto master after #677 landed 6.7.0; #681/#682 renumber on their turn.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        for a in ANCHORS:
            if a["id"] in have:
                raise SystemExit(f"already applied: {a['id']}")
            for dep in a["prediction_chain"]:
                if dep not in have:
                    raise SystemExit(
                        f"prediction_chain target missing on this ledger: {dep}"
                    )
            ed.append("anchors", a)
        L["version"] = CHANGELOG["version"]
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")
    m = json.loads(MANIFEST.read_text())
    ids = {e["anchor_id"] for e in m["entries"]}
    for a in ANCHORS:
        if a["id"] not in ids:
            m["entries"].append(
                {
                    "anchor_id": a["id"],
                    "declared_by": BATCH,
                    "proof_system": "lean4",
                    "witnesses": a["verification"]["witnesses"],
                }
            )
    if not args.dry_run:
        MANIFEST.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n")
    print(
        f"{'DRY ' if args.dry_run else ''}applied: {len(ANCHORS)} anchors; manifest entries {len(m['entries'])}"
    )


if __name__ == "__main__":
    main()
