#!/usr/bin/env python3
"""PROOF anchors for the locale-dynamics theorems (PR #677, #473 ATTACK 3) — encode-AFTER-prove.

Three anchors, the load-bearing theorems Gemini named at 1a575fb: the vacuum nucleus is V-natural
and its fixed frame is Ω({V = 0}); the sublevel infimum is interior{V = 0} (rule-independent); no
V-natural valuation in the model case (ℝ, constant V). Every anchor cites theorems on this branch,
0-sorry, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound} (41/41 attested in
proofs/QBP/Foundations/LocaleDynamics.axioms.txt), reviewed (Red Team APPROVE-WITH-CONCERN, M1–M2
applied; Gemini APPROVE). No root, principle, decision or kill is touched — KILLED-locale-forcing-route
stands. Every "NOT claimed" caveat from the note's §0/§4/§5/§6 is repeated in its anchor: no measure,
no transport, no clock; interior{V=0} = ∅ on S¹⁴ is a hypothesis, not formalised; no lfp-of-an-operator
reading; the valuation result is the model case only (no uniqueness — the end-counting valuation is
invariant; the transfer to the QBP level sets is an open Morse–Bott / extension step, singular strata
excluded). Manifest entries added alongside; then `anchor_inverse_audit.py --update-baseline` records
the anchored growth.
Usage: python3 scripts/encode_locale_dynamics_anchors.py [--dry-run]
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
DATE = "2026-09-24T00:00:00Z"
BATCH = "#677-locale-dynamics"
LD = "QBP.Foundations.LocaleDynamics."
LV = LD + "LocaleValuation."
F_LD = "proofs/QBP/Foundations/LocaleDynamics.lean"
VERIFIER = (
    "run-bounded 6G 1800 taskset -c 0-2 lake build QBP.Foundations.LocaleDynamics (1527 jobs, exit 0; "
    "CI lake build PASS at ac1fcb9) + #print axioms on all 41 theorems "
    "(LocaleDynamics.axioms.txt; qbp-oppenheimer, 2026-09-24; PR #677 Red Team Tier 3 "
    "APPROVE-WITH-CONCERN with M1–M2 applied at 1a575fb, Gemini Tier 3 APPROVE at 1a575fb)"
)
NOT_RULE = (
    " NOT claimed: any reversal of KILLED-locale-forcing-route / Prop 13(b) — the frame supplies neither a "
    "reference measure on a level set nor a transport rule between level sets (both metric data); nothing "
    "here selects quench vs anneal."
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
        "proof_file": F_LD,
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
        "PROOF-vacuum-sublocale-v-natural",
        "For a continuous potential V on a space X, the nucleus U ↦ U ⊔ V⁻¹(ℝ∖{0}) is V-natural and its fixed frame is Ω({V = 0}): the frame supplies the vacuum SUPPORT with its full internal topology, and it separates points inside a level set",
        "Foundations/LocaleDynamics.lean: `vacNucleus_fixed_iff` (the fixed opens of the closed-sublocale nucleus "
        "of {V = 0} are exactly the opens above V⁻¹(ℝ∖{0})), `vacNucleus_natural` (the nucleus commutes with h* for "
        "every V-preserving homeomorphism h — the 'definable from V alone' condition in its equivariance form), "
        "`vacNucleus_trace_surjective` / `vacNucleus_trace_injective` (the fixed frame bijects with Ω({V = 0}), "
        "the opens of the vacuum subspace). Witness on X = ℝ, V(x) = max(x − 1, 0): "
        "`crack_vacNucleus_separates_inside_level_set` (0 and ½ lie in the same level set; a fixed open contains 0 "
        "and not ½) and `crack_vacNucleus_not_defOpens` (the nucleus is not a function of V's values — not in "
        "defOpens V). Bench reading: the sealed position 'a V-natural mechanism moves nothing inside a level set' "
        "is false as stated on all of Ω(X) — locale theory hands over the vacuum sublocale, V-naturally, with its "
        "full internal topology; it presents a frame rather than moving anything. Generic in (X, V): the file "
        "imports Mathlib only (no StateSphere, no potential). NOT claimed: any measure or transport on that "
        "support; any clock — the nucleus is an idempotent projection with no time parameter and no ordering of "
        "states, identical for every V-descending rule (quench and anneal share the vacuum, hence the nucleus)."
        + NOT_RULE,
        LD + "vacNucleus_fixed_iff",
        [
            LD + "vacNucleus_natural",
            LD + "vacNucleus_trace_surjective",
            LD + "vacNucleus_trace_injective",
            LD + "crack_vacNucleus_separates_inside_level_set",
            LD + "crack_vacNucleus_not_defOpens",
        ],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-sublevel-infimum-rule-independent",
        "For V ≥ 0, ⨅_{c>0} {V < c} = interior{V = 0} in Ω(X): the canonical frame-native descent is a function of V alone (identical for quench and anneal) and its Ω(X)-limit is ⊥ when interior{V = 0} = ∅",
        "Foundations/LocaleDynamics.lean: `iInf_sublevel_eq_interior` (for V ≥ 0 the frame infimum of the "
        "sublevel filtration {V < c}, c > 0, is exactly the interior of the vacuum — a frame meet is the interior "
        "of the intersection), `iInf_sublevel_eq_bot_of_interior_eq_empty` (under the hypothesis "
        "interior{V = 0} = ∅ the Ω(X)-limit is ⊥, the empty open). Bench reading, for Prop 12's domain-theory "
        "parenthesis: the sublevel filtration is the canonical 'descend one notch' reading of locales-as-"
        "computation, and it is a function of V alone — every rule that descends V (quench, anneal, any third) "
        "induces the same filtration, so nothing read off it can distinguish them; its open-valued limit selects "
        "no point and no subset of the vacuum. NOT claimed: the hypothesis interior{V = 0} = ∅ on S¹⁴ (true by "
        "the analytic-zero-set argument — V is a non-zero quartic polynomial — but NOT formalised; the Lean "
        "carries it as a hypothesis); any least-fixed-point-of-an-operator reading (no operator is defined in "
        "the Lean whose lfp either limit is, and nothing is proved about this being the only V-definable "
        "descent); that the limit in the sublocale coframe is ⊥ — there the same descent converges to the vacuum "
        "sublocale of PROOF-vacuum-sublocale-v-natural (the support), not to ⊥. Neither limit carries a clock, "
        "an ordering of states, or a measure." + NOT_RULE,
        LD + "iInf_sublevel_eq_interior",
        [LD + "iInf_sublevel_eq_bot_of_interior_eq_empty"],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-no-natural-valuation-model-case",
        "MODEL CASE X = ℝ with a constant potential: every V-natural valuation (Vickers: monotone, modular, ν ⊥ = 0; Scott-continuity NOT assumed) vanishes on every bounded interval — compression under Homeo(ℝ)",
        "Foundations/LocaleDynamics.lean: `natural_valuation_vanishes_of_const` (on ℝ with the constant potential, "
        "a valuation invariant under every V-preserving homeomorphism — here all of Homeo(ℝ) — is 0 on every "
        "open interval (a, b)), via `LocaleValuation.eq_zero_of_compressed` (an open with infinitely many pairwise "
        "disjoint equal-valuation copies has valuation 0) and `LocaleValuation.card_mul_le_top` (n disjoint opens "
        "of equal valuation r give n·r ≤ ν(⊤)); the compressing homeomorphisms are translations, constructed in "
        "Lean. Hypotheses are strictly weaker than Vickers' (no Scott continuity, finite real values), so the "
        "vanishing is strictly stronger. Bench reading: the frame supplies no reference measure on a level set — "
        "the homeomorphism group of a level set is far too big to preserve a measure; the surface measure QBP "
        "uses is invariant only under the isometries of the N-metric (a compact group, Haar), and N is not frame "
        "data. NOT claimed: uniqueness — this is a vanishing result, not a classification: the end-counting "
        "valuation ν(U) = #{ends of ℝ ⊆ U} is Homeo(ℝ)-invariant, monotone, modular, with ν(⊤) = 2; the QBP "
        "level-set case — the transfer needs the RESTRICTION of Homeo_V(S¹⁴) to a level set to be rich enough to "
        "compress (Morse–Bott / local triviality of V near the critical vacuum level on the smooth stratum), "
        "which is classical but NOT formalised, and the singular strata are excluded outright (there fewer "
        "natural symmetries leave more room for a natural valuation — one concentrated on a singular stratum is "
        "singular w.r.t. N's surface measure and reproduces neither basin measure, but the record carries it as "
        "an open step, shared with the FibrewiseTransitive joint of §2); the classical manifold compression lemma "
        "(Homeo(M) preserves no non-zero finite measure, dim M ≥ 1) in general."
        + NOT_RULE,
        LD + "natural_valuation_vanishes_of_const",
        [LV + "eq_zero_of_compressed", LV + "card_mul_le_top"],
        ["PROOF-substrate-hosting-definition"],
    ),
]

CHANGELOG = {
    "version": "6.7.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the locale-dynamics theorems (PR #677; #473 ATTACK 3 on "
        "KILLED-locale-forcing-route, Prop 12's domain-theory loophole / Prop 13(b)) — encode-after-prove, the "
        "three load-bearing theorems Gemini named: the vacuum nucleus U ↦ U ⊔ V⁻¹(ℝ∖{0}) is V-natural and its "
        "fixed frame is Ω({V = 0}) (the frame supplies the vacuum SUPPORT, separating points inside a level set — "
        "the sealed position was false as stated); the sublevel infimum ⨅_{c>0}{V < c} = interior{V = 0} is a "
        "function of V alone, identical for quench and anneal, ⊥ under the empty-interior hypothesis; in the model "
        "case (ℝ, constant V) every V-natural valuation vanishes on every bounded interval. Three anchors, all "
        "0-sorry, axiom closure {propext, Classical.choice, Quot.sound} (41/41 attested), Mathlib-only imports. "
        "Every anchor carries its caveats (no measure, no transport, no clock; interior{V=0} = ∅ on S¹⁴ not "
        "formalised; no lfp-of-an-operator reading; model case only — no uniqueness, end-counting valuation "
        "invariant; transfer to the QBP level sets an open Morse–Bott / extension step, singular strata "
        "excluded). No root, principle, decision or kill touched; the kill stands, Prop 13(b) not reversed — the "
        "missing data are a reference measure and a transport rule, both metric. (Renumbered 6.7.0 at rebase after "
        "#680 landed as 6.6.0.)"
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
                        f"prediction_chain target missing from ledger: {dep}"
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
