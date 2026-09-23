#!/usr/bin/env python3
"""PROOF anchors for the rule-flow theorems (PR #667; #635 Phase A + C) — encode-AFTER-prove.

Every anchor cites theorems on this branch, 0-sorry, `#print axioms` ⊆ {propext, Classical.choice,
Quot.sound}, reviewed (Red Team ×2, Gemini ×2, §I4). No root, principle, decision or kill is
touched; the rule stays a POSTULATE (#635) and nothing here derives or changes its form. Every
"NOT proved" caveat of RuleFlow.lean is repeated in its anchor: local/global existence of the flow
is unproved (every dynamical theorem is about integral curves as hypotheses); the renormalised
Euler step is injective only on ‖F‖ level sets; V = N² ⇒ zero divisor (the converse) is unproved
and unused; Łojasiewicz/point convergence unproved; "every rest point is a vacuum" is false.
Manifest entries added alongside; then `anchor_inverse_audit.py --update-baseline`.
Usage: python3 scripts/encode_rule_flow_anchors.py [--dry-run]
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
DATE = "2026-09-20T00:00:00Z"
BATCH = "#635-rule-flow"
RF = "QBP.Substrate.RuleFlow."
F_RF = "proofs/QBP/Substrate/RuleFlow.lean"
VERIFIER = (
    "lake build QBP.Substrate.RuleFlow (3124 jobs, exit 0) + #print axioms on all 183 declarations "
    "(lean-prover agent + qbp-oppenheimer re-run, 2026-09-20; PR #667 Red Team ×2, Gemini ×2, §I4)"
)
EXIST = (
    " NOT proved: local or global EXISTENCE of the flow — every dynamical statement is about integral "
    "curves as hypotheses (FLAG-rule-flow-open tracks it); Łojasiewicz / point convergence."
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
        "proof_file": F_RF,
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
        "PROOF-rule-gradient-and-tangent-field",
        "The rule's descent direction exists everywhere: closed-form gradient of the potential, smooth to every order; the tangent field keeps the state sphere invariant",
        "Substrate/RuleFlow.lean: `gradV` (closed form via two octonion adjoint identities), `hasGradientAt_potential`, "
        "`hasFDerivAt_potential`, `contDiff_potential` (every order); `ruleField s = −(∇V − ⟨∇V,s⟩s − (∇V)₀·1)`, "
        "`ruleField_bil_self`, `ruleField_coord_zero`; `stateSphere_invariant`: an integral curve of the field that is "
        "on StateSphere at one time is on it throughout (two scalar linear ODEs); `gradV_eq_zero_of_isVacuum`, "
        "`ruleField_eq_zero_of_isVacuum` (crystals are rest points); `exists_ruleField_ne_zero` (the field is not "
        "identically zero — witness (e₁+e₂+e₉) normalised; the earlier witness e₁+e₁₀ is a zero divisor and a rest "
        "point). Formalises the postulate #635 as written (first-order overdamped descent of V in the N-metric); "
        "derives and changes nothing about its form." + EXIST,
        RF + "stateSphere_invariant",
        [
            RF + "hasGradientAt_potential",
            RF + "contDiff_potential",
            RF + "ruleField_bil_self",
            RF + "ruleField_coord_zero",
            RF + "gradV_eq_zero_of_isVacuum",
            RF + "ruleField_eq_zero_of_isVacuum",
            RF + "exists_ruleField_ne_zero",
        ],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-rule-euler-step-injective",
        "The un-normalised Euler step of the rule never merges two states for small step size",
        "Substrate/RuleFlow.lean: `exists_lipschitzOnWith_ruleField` (Lipschitz on a compact ball), `eulerStep_injOn` "
        "(s ↦ s + h·F s injective on the sphere for h·K < 1), `normForm_eulerStep`. NOT proved: general injectivity of the "
        "RENORMALISED step the numerical scripts actually run — only on ‖F‖ level sets "
        "(`renormStep_injOn_of_normForm_const`)." + EXIST,
        RF + "eulerStep_injOn",
        [
            RF + "exists_lipschitzOnWith_ruleField",
            RF + "normForm_eulerStep",
            RF + "renormStep_injOn_of_normForm_const",
        ],
        ["PROOF-rule-gradient-and-tangent-field"],
    ),
    anchor(
        "PROOF-rule-flow-finite-time-uniqueness",
        "Two integral curves of the rule that agree at one time agree at every earlier time (backward uniqueness via Grönwall): the continuous rule merges no two states in finite time",
        "Substrate/RuleFlow.lean: `flow_unique_of_mem_Icc`, `flow_unique_of_endpoint` (Mathlib `ODE_solution_unique_of_mem_Icc*`), "
        "corollary `flow_time_map_injective` (backward uniqueness — the name says injectivity of the time-t map where "
        "defined). Presupposition-free: the curves are hypotheses. The only place two states could merge is the "
        "infinite-time limit — AXIOM-1's open question 1 (its kill text: #668)."
        + EXIST,
        RF + "flow_time_map_injective",
        [RF + "flow_unique_of_mem_Icc", RF + "flow_unique_of_endpoint"],
        ["PROOF-rule-gradient-and-tangent-field"],
    ),
    anchor(
        "PROOF-potential-descent-along-rule",
        "Along any integral curve of the rule the potential is monotone non-increasing, with d/dt V = −N(F)",
        "Substrate/RuleFlow.lean: `hasDerivAt_potential_along_flow` (pointwise derivative −N(F(γ t)) ≤ 0), "
        "`potential_nonincreasing_along_flow` (pointwise), `potential_antitone_along_flow` (the MONOTONE form, via the "
        "mean-value theorem), `potential_le_initial_along_flow`. Bench reading: crystallisation is monotone descent. "
        "NOT claimed: that every rest point is a vacuum — false; `exists_rest_point_not_vacuum` exhibits the maximiser."
        + EXIST,
        RF + "potential_antitone_along_flow",
        [
            RF + "hasDerivAt_potential_along_flow",
            RF + "potential_nonincreasing_along_flow",
            RF + "potential_le_initial_along_flow",
            RF + "exists_rest_point_not_vacuum",
        ],
        ["PROOF-rule-gradient-and-tangent-field"],
    ),
    anchor(
        "PROOF-potential-bounded-by-normForm-sq-frozen-max",
        "V(s) = 4(N(Im a)N(Im b) − ⟨Im a, Im b⟩²) for all s; V ≤ N(s)²; on the state sphere V attains its maximum 1, and every point at the maximum is a rest point (the level set V = 1 is frozen)",
        "Substrate/RuleFlow.lean: `potential_eq_cross` (unconditional closed form — the Im-a form of master's "
        "`DeltaLandscape.sedenion_landscape_descends`), `potential_le_normForm_sq` (Cauchy–Schwarz + AM–GM), "
        "`exists_isMaxOn_potential_stateSphere` (compactness; value 1), `ruleField_eq_zero_of_potential_eq_one` "
        "(a constrained maximum has vanishing tangential gradient — no Lagrange multipliers; h(t) = V(s+tv) − N(s+tv)² ≤ 0 "
        "with equality at 0). Bench reading: the level set V = 1 is a set of maxima where nothing moves. NOT proved: "
        "V = N² ⇒ zero divisor (the converse of the next anchor; unused); the dimension of the level set (numerically "
        "11, codimension 3)." + EXIST,
        RF + "ruleField_eq_zero_of_potential_eq_one",
        [
            RF + "potential_eq_cross",
            RF + "potential_le_normForm_sq",
            RF + "exists_isMaxOn_potential_stateSphere",
        ],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-zero-divisors-sit-at-potential-max",
        "|N(s·x) − N(s)N(x)| ≤ √V(s)·N(x) for all s, x (sharp, both-handed); hence every zero divisor has V = N², on the sphere V = 1; nonzero crystals are never zero divisors",
        "Substrate/RuleFlow.lean: `normForm_mul_eq` (NEW identity: N(xy) = N(x)N(y) − 2⟨cdLo x, assoc(conj(cdHi y), cdHi x, "
        "conj(cdLo y))⟩ — all sedenion non-composition is one associator pairing), `abs_normForm_mul_sub_le` and "
        "`abs_normForm_mul_sub_le_right` (Cauchy–Schwarz after Gram–Schmidt on the associator's middle slot; the Gram "
        "determinant is V/4 by `potential_eq_cross`; the constant √V is attained at every basis-sum zero divisor), "
        "`potential_eq_normForm_sq_of_mul_eq_zero` (+ right), `potential_eq_one_of_zeroDivisor` (+ right), "
        "`crystal_not_zeroDivisor` (V = 0 < N²). Bench reading: zero divisors live only at the maximum of the potential. "
        "NOT proved: the converse V = N² ⇒ zero divisor (numerically true, unused)."
        + EXIST,
        RF + "potential_eq_normForm_sq_of_mul_eq_zero",
        [
            RF + "normForm_mul_eq",
            RF + "abs_normForm_mul_sub_le",
            RF + "abs_normForm_mul_sub_le_right",
            RF + "potential_eq_one_of_zeroDivisor",
            RF + "crystal_not_zeroDivisor",
        ],
        [
            "PROOF-ops-norm-composition-ladder",
            "PROOF-42zd",
            "PROOF-potential-bounded-by-normForm-sq-frozen-max",
        ],
    ),
    anchor(
        "PROOF-rule-descent-avoids-zero-divisors",
        "A forward integral curve of the rule starting below the maximum (V < 1) is never a zero divisor, on either side, at any finite time or in its omega-limit set",
        "Substrate/RuleFlow.lean: `not_zeroDivisor_along_flow` (finite time: both-sided injectivity of γ t for every t ≥ 0), "
        "`omega_avoids_locus` (every omega-limit point has V < 1; Mathlib `omegaLimit`), `omega_avoids_zeroDivisors` "
        "(both-sided). Bench reading, for the beekeeper's question: under the rule as written, for any trajectory that "
        "exists, no state reachable from an ordinary state is ever a zero divisor; the infinite-time limit does not land "
        "on the seam either. This is the theorem the #668 rewrite's replacement observable leans on; it decides "
        "nothing about that rewrite (the beekeeper's process call)." + EXIST,
        RF + "omega_avoids_zeroDivisors",
        [RF + "not_zeroDivisor_along_flow", RF + "omega_avoids_locus"],
        [
            "PROOF-zero-divisors-sit-at-potential-max",
            "PROOF-potential-descent-along-rule",
        ],
    ),
]

CHANGELOG = {
    "version": "6.4.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the rule's flow (PR #667; #635 Phase A + C; the beekeeper's "
        "information-deletion question) — encode-after-prove: gradient + tangent field + sphere invariance; un-normalised "
        "Euler step injective; Grönwall finite-time uniqueness; monotone descent; V ≤ N² with the level set V = 1 frozen; "
        "|N(sx) − N s N x| ≤ √V(s) N x (sharp) so every zero divisor sits at the maximum and crystals never are; descent "
        "from below never reaches a zero divisor (finite time and omega-limit). Seven anchors, 0-sorry, axiom closure "
        "{propext, Classical.choice, Quot.sound}. The rule stays a POSTULATE; nothing derives or changes its form; local/"
        "global existence and Łojasiewicz convergence NOT proved; V = N² ⇒ ZD (unused) NOT proved. No root, principle, "
        "decision or kill touched; AXIOM-1's kill-text defect is #668 (separate PR). (Renumbered 6.4.0 at rebase after "
        "#665 → 6.2.0 and #666 → 6.3.0 landed.)"
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
