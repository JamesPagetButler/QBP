#!/usr/bin/env python3
"""#473 (2026-09-25): encode the beekeeper's ruling after the five attacks on KILLED-locale-forcing-route.

Ruling-rescope, not a physics claim: the "killed" status was not proof-backed and two of its
justifications are refuted; the kill's CONCLUSION was not reversed. The route is reopened as OPEN
research with Prop 13(b) as its kill. Also encodes the record corrections the attacks produced
(quench 0.146 → 0.1416; Cond(Ab) Ext not evaluable in Mathlib) and the transition-state conjecture's
missing testable_when. See docs/foundations/473-ac1-v0.6-addendum-2026-09-25.md.
Written through the confined writer; every record declared. Usage: [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DATE = "2026-09-25T00:00:00Z"
ADD = "docs/foundations/473-ac1-v0.6-addendum-2026-09-25.md"

RULING = (
    " SUPERSEDED BY RULING 2026-09-25 (beekeeper, #473, after five isolated attacks; "
    + ADD
    + "): "
    "the status 'killed' was not proof-backed — the 2026-09-05 ratification rested on an argument (Prop 12) "
    "whose legs were prose (Props 8, 10′), numerical (Props 9, 15, 16(ii)/(iii)) and one half-proved theorem "
    "(addendum §1) — and two SUPPORTING SENTENCES did not survive the attacks, while neither proposition's "
    "conclusion fell: (i) the driver's sealed reasoning behind Prop 12, 'a V-natural mechanism moves nothing "
    "inside a level set', is false (the vacuum sublocale is V-natively available with its full topology, "
    "LocaleDynamics.lean), whereas Prop 12's own claim — nothing in a frame selects the rule — is CONFIRMED "
    "(the nucleus has no clock, identical for quench and anneal); (ii) Prop 10′'s 'the one cover the algebra "
    "supplies' has a wording gap — the algebra also supplies a canonical profinite GROUP (the CD index tower's "
    "dual), which is inert because Aut(𝕊) is a compact Lie group (no small subgroups); Prop 10′'s conclusion "
    "stands. The kill's CONCLUSION — no topological or measure-theoretic mechanism supplies the dynamical rule — "
    "was NOT reversed by any attack. Evidence classes now: attack 3 Lean (42 theorems; scope: for X = ℝ with a "
    "constant potential every V-natural valuation vanishes on bounded intervals — the level-set case is classical, "
    "not formalised — and the least fixed point of the sublevel filtration equals interior{V=0}, hence ⊥ under the "
    "hypothesis interior{V=0} = ∅, which is not discharged in Lean); attack 5 Lean (16 theorems: 13 of 14 in-flight "
    "directions V-neutral); attack 1 NUMERICAL + ARGUMENT, Lean pending (anneal = 1/3 exactly by a Laplace "
    "derivation re-checked in review; closed-form quench endpoint to 10⁻¹¹ by three integrators). Route reopened "
    "as FLAG-locale-forcing-route-reopened. This record is kept as history."
)

NEW_FLAG = {
    "id": "FLAG-locale-forcing-route-reopened",
    "name": "The locale/condensed forcing route is OPEN research again (ruling 2026-09-25): its kill is Prop 13(b) with the honest class — a metric-carrying locale supplying a per-level-set reference measure AND a transport",
    "tier": 3,
    "provenance": "T",
    "provenance_kind": "theory",
    "status": "marginal",
    "description": (
        "Reopens KILLED-locale-forcing-route by beekeeper ruling after the five attacks of 2026-09-24 "
        "("
        + ADD
        + " §2). What is PROVED about the route (all 0-sorry Lean unless marked): (1) the "
        "spatial first link (PROOF-spatial-first-link-condensed-locale); (2) the Gibbs β→∞ anneal on N's "
        "surface measure is EXACTLY uniform on the vacuum S² (⟨b₀²⟩ = 1/3; Laplace factor (8(1−b₀²))⁻³ "
        "cancels the surface element (1−b₀²)³ — derivation + quadrature + MCMC, attack 1; numerical/analytic, "
        "Lean pending); (3) the quench endpoint has the closed form b₀²/(b₀² + √((1−b₀²)² − V₀)) per seed "
        "(three integrators to 10⁻¹¹; exact mean 0.141587; Lean target (i) funded); (4) a V-natural nucleus "
        "gives the vacuum sublocale with its full topology but no measure: in the model case X = ℝ with a "
        "constant potential every V-natural valuation vanishes on bounded intervals (the level-set case is "
        "classical, not formalised), and the least fixed point of the sublevel filtration equals interior{V=0}, "
        "hence ⊥ when the vacuum has empty interior — a hypothesis, not discharged in Lean (LocaleDynamics.lean, "
        "42 theorems, 41 audited); (5) every level-set invariant is rule-blind: at any in-flight state 13 of 14 "
        "tangent directions are V-neutral (TransitionState.lean, 16 theorems); (6) the "
        "CD index tower's dual Cantor group is an algebra-native profinite Galois group acting by sign "
        "automorphisms, and every continuous profinite action by automorphisms on 𝕊 has finite image (attack 4; "
        "Aut(𝕊) is a closed norm-preserving subgroup of GL(16,ℝ), hence a compact Lie group — no small subgroups; "
        "the unformalised Aut(𝕊) = G₂ × S₃ is not used; numerical + argument). NOT proved: that no mechanism outside these classes "
        "exists — which is why the route is OPEN rather than killed or validated."
    ),
    "prediction_chain": ["PROOF-spatial-first-link-condensed-locale"],
    "testable_when": (
        "Kill (Prop 13(b), honest class): a mechanism built from topological or measure-theoretic data "
        "that supplies BOTH a reference measure on each level set of V AND a transport between level "
        "sets — i.e. a metric-carrying (enriched/Lawvere) locale — and whose metric is shown not to be N "
        "re-labelled (Prop 8's relocation test). Discharge if found: the mechanism's PROOF- anchor and the "
        "rule it selects (quench 0.1416 / anneal 1/3 / ℓ-axis 1 / other), then AC2″ on #473. Discharge if "
        "excluded: a theorem that every metric-carrying locale mechanism natural in (V, N) — natural meaning "
        "equivariant under the isometries of (StateSphere, N) that preserve V — carries a metric that is N "
        "re-labelled (Prop 8's relocation test fails), so that its rule is one of the N-metric protocols already "
        "on record (quench 0.1416, anneal 1/3, ℓ-axis 1) rather than new topological data. (The anneal is itself "
        "(V, N)-natural and supplies a measure and a transport — Prop 9 — so 'beyond N's gradient flow' would be "
        "the wrong exclusion; the test is relocation, not existence.)"
    ),
    "notes": (
        "Tracking anchor only (route OPEN; no root, no claim). Ruling text and the audit of the original "
        "kill: "
        + ADD
        + " §0–§1. Funded follow-ups (beekeeper item 6): Lean target (i) integrability of "
        "the quench in the Gram invariants; (ii) the zero-divisor spectrum {2×4, √2×8, 0×4} and ridge-plane "
        "identities. Attack branches research/473-kill-attack-{1..5}."
    ),
    "foundation_batch": "#473-kill-attack",
    "last_tested_at": DATE,
}

CONJ_TESTABLE = (
    "When ALL FOUR prerequisites exist (attack 5, 2026-09-24): (i) the compact-Hausdorff structure of "
    "StateSphere available to the layer that builds the condensed object (proved in Substrate under a "
    "scoped normed instance — RuleFlow.isCompact_stateSphere — so a condensed object over it needs its own "
    "lift); (ii) the vacuum locus {V=0} and the zero-divisor locus {V=1} proved closed; (iii) H^*({V=0}; ℤ) "
    "and the critical values of V computed (nothing on record knows whether the vacuum manifold is "
    "connected, and every invariant of the proposed object is a function of this); (iv) Mathlib acquires "
    "EnoughProjectives for CondensedAb or the compact-Hausdorff comparison RΓ(X_cond, ℤ) = RΓ_sheaf(X, ℤ), "
    "without which no Ext group in Cond(Ab) is evaluable. Note 'Ext¹ groups' is not a unit; no value can "
    "be compared with a measurement until a unit is named."
)

CONJ_NOTES = (
    "Adjudication (attack 5, 2026-09-24; ruling 2026-09-25, "
    + ADD
    + " §4): (a) WITHDRAWN — the limit reading "
    "is vacuous (every subalgebra is the limit of ℍ ↪ 𝕆) and the projection reading is impossible (𝕆 is "
    "simple: no nonzero algebra map 𝕆 → ℍ); the honest object is subalgebra SELECTION, G₂/SO(4), realised as "
    "the hosting bundle over the vacuum manifold (PROOF-crystal-hosts-quaternion). (b) RE-SCOPED to a "
    "descriptor: Ext¹(ℍ_cond, 𝕆_cond) has no state or time variable, reduces in Cond(Ab) to Ext¹(ℝ,ℝ)^32 "
    "(a constant of the category) and is identically zero under the deformation-theoretic repair (ℍ "
    "separable ⇒ rigid as an algebra, HH²(ℍ,ℍ) = 0 — note the EMBEDDING ℍ ↪ 𝕆 is not rigid: its deformations are "
    "T(G₂/SO(4)), i.e. the kinematic hosting bundle of (a), not an obstruction); it cannot parametrise a physical "
    "quantity, at most describe one. (c) WITHDRAWN as a "
    "rule-supplier (closure ruling-rescope): an Ext group carries no clock, a rate needs the rule; and the "
    "substrate has no horizon object. (d) untouched. Prop 13(b) via this route: FIRED — every object the "
    "route can define is a functor of V's level-set topology, hence rule-independent "
    "(TransitionState.finrank_vNeutral). Positive: condensed math is conservative on the spatial inputs "
    "here (Aut(𝕊) compact — a closed norm-preserving subgroup of GL(16,ℝ); Brown's G₂ × S₃ unformalised — ⇒ "
    "orbit space compact Hausdorff); the one genuinely non-Hausdorff object in "
    "reach is the orbit space of the RULE — downstream of it."
)

CHANGELOG = {
    "version": "6.6.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: #473 ruling 2026-09-25 after five isolated attacks on KILLED-locale-forcing-route "
        "(ruling-rescope; nothing physical ruled). KILLED-locale-forcing-route: status killed → marginal, "
        "superseded (not proof-backed; one supporting sentence false and one gapped, neither proposition's "
        "conclusion fell; the kill's conclusion not reversed), kept as history. "
        "NEW FLAG-locale-forcing-route-reopened (route OPEN; kill = Prop 13(b) with the honest class; six "
        "proved/derived legs listed). CONJ-condensed-math-for-transition-state: testable_when added; (a),(c) "
        "withdrawn, (b) re-scoped to a descriptor, (d) untouched. FLAG-rule-flow-open: quench 0.146 → 0.1416 "
        "(+0.0031 Euler bias), anneal = 1/3 exactly. REF-condensed-categorical-foundations-mathlib: Ext in "
        "Cond(Ab) definable, not evaluable. REF-pyknotic-condensed-topos-status: re-verified against the pin. "
        "Records: " + ADD + "."
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        if any(a["id"] == NEW_FLAG["id"] for a in L["anchors"]):
            raise SystemExit("already applied")
        k = ed.record("anchors", "KILLED-locale-forcing-route")
        k["status"] = "marginal"
        k["name"] = "[SUPERSEDED 2026-09-25 by ruling] " + k["name"]
        k["description"] = k["description"] + RULING
        k["killed_note"] = (
            "The 'killed' status was withdrawn by beekeeper ruling 2026-09-25: it was ratified on an argument, not "
            "a proof; the attacks of 2026-09-24 showed one supporting sentence false (the driver's sealed reasoning "
            "behind Prop 12) and one gapped (Prop 10′'s cover wording) while neither proposition's conclusion fell; "
            "the kill's conclusion stands unreversed and the route is reopened as FLAG-locale-forcing-route-reopened."
        )
        # A non-killed record must terminate its chain in a PROOF (root gate): the record's true
        # supports are the proved first link and the Lean half of Prop 16.
        k["prediction_chain"] = [
            "PROOF-spatial-first-link-condensed-locale",
            "PROOF-no-autonomous-algebraic-dynamics",
        ]
        k["last_tested_at"] = DATE
        ed.append("anchors", NEW_FLAG)
        c = ed.record("anchors", "CONJ-condensed-math-for-transition-state")
        c["testable_when"] = CONJ_TESTABLE
        c["predicted_unit"] = (
            "none — Ext groups are not a unit; no comparable quantity until testable_when's prerequisites name one "
            "(replaces 'Ext-1 groups computed in condensed abelian-group category', 2026-09-25)"
        )
        c["notes"] = (c.get("notes", "") + " " if c.get("notes") else "") + CONJ_NOTES
        c["last_tested_at"] = DATE
        f = ed.record("anchors", "FLAG-rule-flow-open")
        f["notes"] = f["notes"] + (
            " CORRECTION 2026-09-25 (#473 attack 1): the quench endpoint is 0.1416 (exact 0.141587, closed form "
            "b₀²/(b₀² + √((1−b₀²)² − V₀)) per seed); the '0.146' carried a +0.0031 renormalised-Euler (h = 0.02) "
            "bias; the anneal is 1/3 EXACTLY (approach 1/3 − 0.554/√β). The two-rules-two-numbers conclusion is "
            "unchanged."
        )
        r = ed.record("anchors", "REF-condensed-categorical-foundations-mathlib")
        r["description"] = r["description"].replace(
            "Makes Ext computations in Cond(Ab) tractable in QBP's Lean environment.",
            "Makes the CATEGORY Cond(Ab) available in QBP's Lean environment (CondensedAb, freeAb, abelian + "
            "AB4/AB5, HasExt via IsGrothendieckAbelian, Sheaf.H); Ext groups are thereby DEFINABLE but not "
            "EVALUABLE — the pinned Mathlib has no EnoughProjectives for CondensedAb, no computed condensed Ext, "
            "and the Liquid Tensor Experiment is not in Mathlib (corrected 2026-09-25, #473 attack 5).",
        )
        assert "DEFINABLE but not" in r["description"], "REF replacement did not land"
        r["last_tested_at"] = DATE
        ic = ed.record("anchors", "INSIGHT-locale-condensed-chain")
        ic["description"] = ic["description"] + (
            " UPDATE 2026-09-25 (#473 ruling): the forcing extension's 'KILLED (Prop 12 ratified)' status above was "
            "WITHDRAWN by beekeeper ruling — not proof-backed; the kill's conclusion unreversed — and the route is "
            "reopened as FLAG-locale-forcing-route-reopened (kill = Prop 13(b), honest class). See "
            + ADD
            + "."
        )
        ic["last_tested_at"] = DATE
        p = ed.record("anchors", "REF-pyknotic-condensed-topos-status")
        p["last_tested_at"] = DATE
        p["notes"] = (p.get("notes", "") + " " if p.get("notes") else "") + (
            "Re-verified 2026-09-24 against the pinned Mathlib (Condensed/Basic.lean states its definition "
            "'more closely resembles Pyknotic objects')."
        )
        L["version"] = CHANGELOG["version"]
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")
    print(
        f"{'DRY ' if args.dry_run else ''}applied: ruling encoded (7 records + 1 new)"
    )


if __name__ == "__main__":
    main()
