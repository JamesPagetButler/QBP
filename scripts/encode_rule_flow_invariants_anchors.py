#!/usr/bin/env python3
"""PROOF anchors for the rule-flow invariants (PR #681, #473 target 6(i)) — encode-AFTER-prove.

Four anchors for `proofs/QBP/Substrate/RuleFlowInvariants.lean`: the closed-form ODE system of the
four G₂ × O(2) Gram invariants along the rule; straight-ray motion (collinearity of
(A−½, C−½, P, b₀²) with its initial vector); monotonicity of b₀²; and the CONDITIONAL quench
endpoint closed form. Every anchor cites theorems on this branch, 0-sorry, `#print axioms` ⊆
{propext, Classical.choice, Quot.sound} (93/93 in the file's §8 audit), reviewed (PR #681 Red Team
APPROVE; Gemini APPROVE). No root, principle, decision or kill is touched; FLAG-rule-flow-open stays
open. The review constraint is repeated in EVERY anchor: each theorem ASSUMES an integral curve
(a `HasDerivAt γ (ruleField (γ t)) t` hypothesis) — existence is NOT claimed (#635); the endpoint
anchor additionally ASSUMES V(γ t) → 0 and that the limit L exists — convergence is NOT claimed;
the ensemble mean ⟨b₀²⟩ = 0.1416 of attack 1 is numerical (#675) and is NOT a Lean statement.
Manifest entries added alongside; then `anchor_inverse_audit.py --update-baseline` records the
anchored growth.
Usage: python3 scripts/encode_rule_flow_invariants_anchors.py [--dry-run]
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
BATCH = "#681-rule-flow-invariants"
RI = "QBP.Substrate.RuleFlowInvariants."
F_RI = "proofs/QBP/Substrate/RuleFlowInvariants.lean"
VERIFIER = (
    "run-bounded lake build of the Substrate aggregator (QBP.Substrate.RuleFlowInvariants; 3126 jobs, "
    "exit 0, peak 3.7 GB) + #print axioms on all 93 declarations (82 theorems + 11 defs) of the file's §8 audit "
    "(qbp-oppenheimer, 2026-09-24; PR #681 Red Team APPROVE, Gemini APPROVE)"
)
CHAIN = ["PROOF-rule-gradient-and-tangent-field", "PROOF-substrate-hosting-definition"]
ASSUMES = (
    " ASSUMES an integral curve: every theorem has the shape 'IF γ satisfies HasDerivAt γ (ruleField (γ t)) t "
    "THEN …' and the antecedent is never discharged."
)
NOT_EXIST = (
    " NOT claimed: local or global EXISTENCE of any integral curve of the rule (#635, FLAG-rule-flow-open); "
    "convergence of any curve; any measure, ensemble average or physical claim — the ensemble mean "
    "⟨b₀²⟩ ≈ 0.1416 of attack 1 is numerical (#675) and is not a Lean statement."
)


def _libs():
    m = json.loads(LAKE.read_text())
    return {
        p["name"]: {"ref": p.get("inputRev") or p["rev"], "sha": p["rev"]}
        for p in m["packages"]
        if p["name"] in ("mathlib", "batteries")
    }


def anchor(aid, name, desc, main, companions, chain):
    wits = [main] + companions
    return {
        "id": aid,
        "name": name,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": desc,
        "proof_file": F_RI,
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
            "verifier": VERIFIER,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": wits,
        },
    }


ANCHORS = [
    anchor(
        "PROOF-rule-gram-invariants-ode",
        "Along any integral curve of the rule the four Gram invariants close: Ȧ = 4V(2A−1), Ċ = 4V(2C−1), Ṗ = 8VP, ḃ₀ = 4Vb₀, d(b₀²)/dt = 8Vb₀²; Euler identity ⟪∇V, s⟫ = 4V",
        "Substrate/RuleFlowInvariants.lean: with A = N(Im cdLo s), C = N(Im cdHi s), P = ⟪Im cdLo s, Im cdHi s⟫, "
        "b₀ = (cdHi s)₀ (the ℓ-coefficient, coordinate 8) and V = 4(AC − P²) (`potential_eq_gram`), the rule "
        "closes on these four numbers along ANY integral curve γ' = ruleField(γ): `hasDerivAt_gramA_along_flow` "
        "(Ȧ = 4V(2A−1)), `hasDerivAt_gramC_along_flow` (Ċ = 4V(2C−1)), `hasDerivAt_gramP_along_flow` (Ṗ = 8VP), "
        "`hasDerivAt_ellCoeff_along_flow` (ḃ₀ = 4Vb₀), `hasDerivAt_ellSq_along_flow` (d(b₀²)/dt = 8Vb₀²) — NO "
        "state-sphere hypothesis on any of these; `gram_sum_hasDerivAt_zero` is the consistency check "
        "Ȧ + Ċ + d(b₀²)/dt = 0, the ONLY statement here that uses the sphere (A + C + b₀² = 1). `bil_gradV_self` "
        "is the Euler identity ⟪∇V, s⟫ = 4V (V is homogeneous of degree 4). Off the state sphere `ruleField` is "
        "the postulated polynomial field of RuleFlow.lean read literally, not a normalised projection — the ODEs "
        "hold for it as written." + ASSUMES + NOT_EXIST,
        RI + "hasDerivAt_gramA_along_flow",
        [
            RI + "hasDerivAt_gramC_along_flow",
            RI + "hasDerivAt_gramP_along_flow",
            RI + "hasDerivAt_ellCoeff_along_flow",
            RI + "hasDerivAt_ellSq_along_flow",
            RI + "gram_sum_hasDerivAt_zero",
            RI + "bil_gradV_self",
        ],
        CHAIN,
    ),
    anchor(
        "PROOF-rule-descent-straight-ray",
        "Straight-ray motion in the Gram invariants: along any integral curve every 2×2 minor of (A−½, C−½, P, b₀²)(t) against its initial vector vanishes — the point stays on a line through (½, ½, 0, 0) in any parametrisation",
        "Substrate/RuleFlowInvariants.lean: `IsRayCoord f` = f continuous and d/dt f(γ t) = 8V(γ t)·f(γ t) along "
        "every integral curve; instances `isRayCoord_gramA_sub` (A − ½), `isRayCoord_gramC_sub` (C − ½), "
        "`isRayCoord_gramP` (P), `isRayCoord_ellSq` (b₀²), packaged as `isRayCoord_rayVec` for the vector "
        "`rayVec = (A−½, C−½, P, b₀²) : Fin 4 → ℝ`. `ray_minor_eq_zero`: any two ray coordinates have vanishing "
        "minor f(γ t)·g(γ t₀) − g(γ t)·f(γ t₀) = 0 on [a,b] (Grönwall-type uniqueness for the scalar linear ODE "
        "ẏ = 8V·y; V continuous along γ); `gram_ray` (the three minors against b₀²); `rayVec_collinear` (ALL "
        "pairwise minors, i j : Fin 4). This is the parametrisation-free form of the straight ray seen numerically "
        "in attack 1 §3a: 'ray' means exactly 'all minors against the initial vector vanish' (collinearity). The "
        "ray parameter λ itself is NOT constructed (it would need V > 0 along the curve). NOT claimed here: that "
        "the motion is OUTWARD along the ray — that is the sign statement of PROOF-ell-coefficient-monotone-along-rule, "
        "not a theorem of this anchor." + ASSUMES + NOT_EXIST,
        RI + "rayVec_collinear",
        [
            RI + "ray_minor_eq_zero",
            RI + "gram_ray",
            RI + "isRayCoord_gramA_sub",
            RI + "isRayCoord_gramC_sub",
            RI + "isRayCoord_gramP",
            RI + "isRayCoord_ellSq",
            RI + "isRayCoord_rayVec",
        ],
        CHAIN,
    ),
    anchor(
        "PROOF-ell-coefficient-monotone-along-rule",
        "b₀² is non-decreasing along any integral curve of the rule (d(b₀²)/dt = 8Vb₀² ≥ 0 since V ≥ 0); any limit it has is ≥ its initial value",
        "Substrate/RuleFlowInvariants.lean: `ellSq_monotone_along_flow` — for γ continuous on [a,b] with "
        "HasDerivAt γ (ruleField (γ t)) t on (a,b), t ↦ b₀²(γ t) is MonotoneOn [a,b] (via "
        "`hasDerivAt_ellSq_along_flow` and `Hosting.potential_nonneg`; no state-sphere hypothesis). "
        "`quench_root_ge_initial` (pure algebra): any L ∈ [0,1] solving the quench quadratic with 0 ≤ V₀ and "
        "non-negative discriminant satisfies B₀ ≤ L, because D = √((1−B₀)² − V₀) ≤ 1 − B₀. "
        "`ellSq_limit_ge_initial`: for a curve on all of ℝ through a state-sphere point, IF V(γ t) → 0 AND "
        "b₀²(γ t) → L THEN b₀²(γ t₀) ≤ L — this limit statement ASSUMES V → 0 and ASSUMES the limit exists; "
        "both are hypotheses, neither is proved. This is the sign behind attack 1 §3a's '|b₀| only grows' and "
        "the outward direction of the straight ray (PROOF-rule-descent-straight-ray)."
        + ASSUMES
        + NOT_EXIST,
        RI + "ellSq_monotone_along_flow",
        [RI + "quench_root_ge_initial", RI + "ellSq_limit_ge_initial"],
        CHAIN,
    ),
    anchor(
        "PROOF-quench-endpoint-closed-form-conditional",
        "CONDITIONAL quench endpoint: for an integral curve on ℝ through a state-sphere point, IF V(γ t) → 0 AND b₀²(γ t) → L THEN L = b₀²/(b₀² + √((1−b₀²)² − V₀)) — the attack-1 closed form, with the root selection proved",
        "Substrate/RuleFlowInvariants.lean: `quench_relation` (on [a,b]) and `quench_relation_univ` (on ℝ, via "
        "`stateSphere_invariant_univ`): collinearity plus the sphere constraint A + C + b₀² = 1 at t₀ collapse to the "
        "conserved quadratic V·B₀² = B²(V₀ + 2B₀ − 1) − 2B₀²B + B₀² (B = b₀², B₀ = b₀(t₀)²) at EVERY time, depending "
        "on the initial data only through (V₀, B₀). `quench_root_pick_aux` / `quench_root_pick`: if L ∈ [0,1] "
        "solves the quench quadratic with B₀ ≥ 0 and discriminant (1−B₀)² − V₀ ≥ 0 then L·(B₀ + √((1−B₀)² − V₀)) = B₀ "
        "— the root B₀/(B₀ + D) is PROVED to be the one selected, D = √((1−B₀)² − V₀), by cases: for B₀ + D > 0 the "
        "quantity B₀/(B₀ + D) lies in [0,1]; when the equation is a genuine quadratic with distinct roots (B₀ ≠ 0, "
        "D ≠ 0, B₀ ≠ D) the other root B₀/(B₀ − D) lies outside [0,1] — above 1 for B₀ > D, below 0 for B₀ < D — "
        "so 0 ≤ L ≤ 1 excludes it; at B₀ = D > 0 the leading coefficient vanishes and the linear equation has the "
        "single solution ½; at D = 0 < B₀ or B₀ = 0 < D the roots coincide (1, resp. 0); at B₀ = D = 0 (V₀ = 1, "
        "b₀(t₀) = 0 — the frozen-ridge point) the quadratic is 0 = 0, the division form is undefined, and this is "
        "exactly the point excluded by the `hne` hypothesis of `ellSq_limit_eq_closed_form`, while the division-free "
        "`ellSq_tendsto_closed_form` (L·(B₀ + D) = B₀) holds there trivially. The discriminant is non-negative on the sphere by `potential_le_one_sub_ellSq_sq`. "
        "`ellSq_tendsto_closed_form`: for a curve with HasDerivAt on all of ℝ and γ t₀ ∈ StateSphere, IF "
        "Tendsto V(γ t) atTop (nhds 0) AND Tendsto b₀²(γ t) atTop (nhds L) THEN L·(B₀ + √((1−B₀)² − V₀)) = B₀ "
        "(division-free); `ellSq_limit_eq_closed_form` is the division form L = b₀²/(b₀² + √((1−b₀²)² − V₀)) "
        "under the extra hypothesis that the denominator is non-zero (it vanishes only at b₀(t₀) = 0, V₀ = 1). "
        "This anchor ASSUMES V(γ t) → 0 and ASSUMES the limit L exists: both are HYPOTHESES of the theorem, "
        "neither is proved anywhere (#635, FLAG-rule-flow-open). NOT claimed: that any curve converges; the "
        "ensemble mean ⟨b₀²⟩ ≈ 0.1416 (numerical, #675 — this file proves the per-orbit map the ensemble "
        "integrates, not the integral); an `Ici t₀` (half-line) variant of the limit statement (follow-up)."
        + ASSUMES
        + NOT_EXIST,
        RI + "ellSq_limit_eq_closed_form",
        [
            RI + "ellSq_tendsto_closed_form",
            RI + "quench_relation",
            RI + "quench_relation_univ",
            RI + "quench_root_pick",
            RI + "quench_root_pick_aux",
        ],
        CHAIN,
    ),
]

CHANGELOG = {
    "version": "6.9.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the rule-flow invariants (PR #681; #473 target 6(i)) — "
        "encode-after-prove: along ANY integral curve of the rule the four G₂ × O(2) Gram invariants close "
        "(Ȧ = 4V(2A−1), Ċ = 4V(2C−1), Ṗ = 8VP, ḃ₀ = 4Vb₀); (A−½, C−½, P, b₀²) moves on a straight ray through "
        "(½, ½, 0, 0) (all 2×2 minors against the initial vector vanish); b₀² is non-decreasing; and CONDITIONALLY "
        "on V → 0 and the limit existing, the endpoint is the attack-1 closed form "
        "L = b₀²/(b₀² + √((1−b₀²)² − V₀)) with the root selection proved. Four anchors, all 0-sorry, axiom closure "
        "{propext, Classical.choice, Quot.sound}, chained to PROOF-rule-gradient-and-tangent-field and "
        "PROOF-substrate-hosting-definition. Every anchor states that it ASSUMES an integral curve (HasDerivAt "
        "hypothesis) and, for the endpoint, ASSUMES V → 0 and the limit exists; none claims flow existence, "
        "convergence, or the ensemble mean 0.1416 (numerical, #675). No root, principle, decision or kill touched; "
        "FLAG-rule-flow-open stays open. (Version 6.9.0: rebased onto master after #677 → 6.7.0 and #679 → 6.8.0 landed; "
        "anchor-4 excluded-root wording corrected per Red Team/Gemini M1 at cda3d32 and M1′ at bf64db1 and M2 at 7b90975 (the B₀ = D = 0 point); #682 renumbers on its turn.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        for cid in CHAIN:
            if cid not in have:
                raise SystemExit(f"prediction_chain target missing from ledger: {cid}")
        for a in ANCHORS:
            if a["id"] in have:
                raise SystemExit(f"already applied: {a['id']}")
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
