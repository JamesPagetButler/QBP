#!/usr/bin/env python3
"""#473 AC1 δ-landscape descent anchors — append the 3 CTH proof anchors that foot
proofs/QBP/Foundations/DeltaLandscape.lean and proofs/QBP/Foundations/SpatialFirstLink.lean (PR #631: Prop 6 descent identity of the
#629 landscape potential, and the Prop 7′ order-3-rotation ⇒ scalar-form step behind
the S₃ reduction of Aut(𝕊)-invariant quadratic forms) into the ledger, plus the matching
manifest entries. Idempotent: re-running removes any prior foundation_batch=="#473-ac1"
anchors/entries first. Same shape as scripts/encode_473_anchors.py (batch "#473").

Evidence bar (C3-FULL): `#print axioms` on all 11 declarations, captured from
`run-bounded 8G 900 lake build QBP.Foundations.DeltaLandscape` on the PR branch:
every one ⊆ {propext, Classical.choice, Quot.sound}; 0 sorry, 0 native_decide, 0 True stubs.

Scope note carried in each description: these anchors are RESEARCH-THREAD evidence
(#473 stays open; the doc is not foundation) — they anchor identities used by the
#629 δ-landscape, not a substrate claim. No file under proofs/QBP/Substrate/.

Usage: python3 scripts/encode_473_ac1_anchors.py   (from the repo root)
"""

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")
PROOF_FILE = "proofs/QBP/Foundations/DeltaLandscape.lean"
NS = "QBP.Foundations.DeltaLandscape."
SPATIAL = {
    "PROOF-spatial-first-link-condensed-locale": (
        "proofs/QBP/Foundations/SpatialFirstLink.lean",
        "QBP.Foundations.SpatialFirstLink.",
    )
}


def pf_ns(aid):
    return SPATIAL.get(aid, (PROOF_FILE, NS))


BATCH = "#473-ac1"
STAMP = "2026-09-04T00:00:00Z"
CLEAN = ["propext", "Classical.choice", "Quot.sound"]
VERIFIER = (
    "lake build QBP.Foundations.DeltaLandscape / .SpatialFirstLink + #print axioms, "
    "leanprover/lean4:v4.30.0 (qbp-oppenheimer, #473 AC1 batch #473-ac1: δ-landscape descent, "
    "rot120 scalar form, spatial first link; PR #631 head ddfdec0+); pending cth §I4"
)
MATHLIB = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
BATTERIES = "32dc18cde3684679f3c003de608743b57498c56f"

# id -> (name, description, [witnesses: primary first])
ANCHORS = {
    "PROOF-delta-landscape-descent": (
        "‖[a,b]‖² = 4(|a|²|Im b|² − ⟨a,Im b⟩²): the δ-landscape descends to the G₂-invariants",
        "#473 AC1 v0.3.1 Prop 6 (PR #631), research-thread evidence anchoring the #629 "
        "δ-landscape. For an imaginary sedenion s ∈ CDAlg ℝ 4 (s.coord 0 = 0) with "
        "Cayley–Dickson octonion components a = cdLo s, b = cdHi s and c = b − b₀•1 = Im b: "
        "N(a·b − b·a) = 4·(N a · N c − (bil a c)²). Hence the landscape potential "
        "V(s) = ‖[a,b]‖² is a function of the three G₂-invariants (|a|², |Im b|², ⟨a,Im b⟩) "
        "only, so the #629 gradient flow descends to the 3-dimensional orbit space S¹⁴/G₂. "
        "Structural proof (no decide): real multiples of 1 are central for the commutator, "
        "[x,y] = 2·(x ×ₙ y), N(2•v) = 4·N v, and the 𝕆 Lagrange identity "
        "CrossProduct.octonion_cross_norm_identity. Workhorse octonion_commutator_norm_im has "
        "the second argument arbitrary (only a imaginary is used). Companions: "
        "V ≥ 0 and the Cauchy–Schwarz consequence ⟨a,Im b⟩² ≤ |a|²|Im b|² on the orbit "
        "space. Numerical counterpart: analysis/473-dirac-probe/orbit_space.py check (3), "
        "residual 7e-16. Not a substrate claim; #473 stays open.",
        [
            "sedenion_landscape_descends",
            "octonion_commutator_norm_im",
            "octonion_commutator_norm",
            "commutator_eq_two_smul_cross",
            "commutator_sub_central",
            "im_coord_zero",
            "sedenion_landscape_nonneg",
            "sedenion_gram_nonneg",
        ],
    ),
    "PROOF-spatial-first-link-condensed-locale": (
        "Ω(X) ≅ Ω(condensedSetToTopCat X̲) for compactly generated X (ℝ included)",
        "#473 AC1 v0.3.1 Prop 1 (PR #631): the spatial first link of the proposed "
        "condensed → locale chain, written out as a composition of Mathlib facts and "
        "type-checked. For X : TopCat.{u+1} compactly generated, `localeIsoOfCondensed X` is "
        "the isomorphism in Locale between the locale of the topological space recovered from "
        "the condensed set X̲ and the locale of X (topToLocale applied to the counit "
        "homeomorphism CondensedSet.compactlyGeneratedAdjunctionCounitHomeo); "
        "`localeFunctorIso` is the natural isomorphism CG → Cond → Top → Loc ≅ CG → Top → Loc "
        "(also obtained by whiskering the invertible counit, `localeFunctorIso'`); "
        "`realLocaleIsoOfCondensed` is the ℝ instance via ULift.{1} ℝ (first countable ⇒ "
        "sequential ⇒ compactly generated). Witness theorems (rfl-level bookkeeping — the mathematical content is in the "
        "noncomputable iso defs, which the audit does not count): localeIsoOfCondensed_hom "
        "(the iso's hom is topToLocale.map of the counit iso's hom) and realTop_locale_eq "
        "(the locale is literally Opens (ULift ℝ)); realOpensOrderIso gives Opens (ULift ℝ) ≃o "
        "Opens ℝ. "
        "Faithfulness of Top → Loc on CompHaus is Mathlib's CompHausToLocale.faithful (cited by "
        "type-check). SCOPE: this shows the ledger's Cantor-set anecdote was never load-bearing "
        "and that set-theoretic forcing (Prop 4) does not deliver the FORCED/PERMITTED-sense "
        "forcing argument AC1 asks for (doc §4). Research-thread evidence; not a substrate "
        "claim; no Substrate/ file; #473 stays open.",
        ["localeIsoOfCondensed_hom", "realTop_locale_eq"],
    ),
    "PROOF-rot120-invariant-form-scalar": (
        "A quadratic form on ℝ² invariant under a 120° rotation is scalar (order 2 is not enough)",
        "#473 AC1 v0.3.1 Prop 7′ (PR #631), the algebraic step of the S₃ reduction: the "
        "G₂-invariant quadratic forms on Im𝕊 = 7 ⊕ 1 ⊕ 7 restricted to the (a, Im b) "
        "multiplicity plane are |a|² + λ|Im b|² + ν⟨a,Im b⟩, i.e. a symmetric form (p q; q r) "
        "on ℝ²; invariance under the order-3 rotation R (entries (−1/2, −√3/2; √3/2, −1/2), "
        "the ±120° rotations in Aut(𝕊) = G₂ × S₃ commuting with G₂) forces q = 0 and p = r, "
        "so the form is scalar (λ = 1, ν = 0) and the Aut-invariant quadratic-form family "
        "collapses to Q_μ = |a|² + |Im b|² + μb₀². Stated with the explicit RᵀQR entries as "
        "hypotheses; proved by linear_combination over √3² = 3. Companions: the ₂₂ invariance "
        "equation is redundant given the ₁₁ one (trace preservation), and `rot180_admits_nonscalar` exhibits (p,q,r) = (1,1,0) satisfying the 180° "
        "conjugation equations with q ≠ 0, p ≠ r (the equations are trivial at 180°, which is "
        "the point: order 2 constrains nothing on the traceless part — the argument is in the "
        "docstring, the theorem is the explicit witness). SCOPE: this is the quadratic-form class only; a general "
        "Aut-invariant measure is any S₃-invariant density on the orbit space (doc Prop 7′ / "
        "Prop 12 crux). Research-thread evidence; #473 stays open.",
        [
            "rot120_invariant_form_scalar",
            "rot120_h22_of_h11",
            "rot180_admits_nonscalar",
        ],
    ),
}


def verification():
    return {
        "toolchain": "leanprover/lean4:v4.30.0",
        "libraries": {
            "mathlib": {"ref": MATHLIB, "sha": MATHLIB},
            "batteries": {"ref": "main", "sha": BATTERIES},
        },
        "verified_at": STAMP,
        "verifier": VERIFIER,
        "result": "verified",
        "axiom_closure": CLEAN,
    }


def build_anchor(aid):
    name, desc, wits = ANCHORS[aid]
    pf, ns = pf_ns(aid)
    return {
        "id": aid,
        "name": name,
        "tier": 1,
        "provenance": "T",
        "status": "coherent",
        "description": desc,
        "prediction_chain": [],
        "provenance_kind": "proof",
        "proof_system": "lean4",
        "proof_language": "lean4",
        "proof_file": pf,
        "sorry_count": 0,
        "proof_state": "verified",
        "lean_theorem": ns + wits[0],
        "lean_companion_theorems": [ns + w for w in wits[1:]],
        "theorems": [{"name": w, "status": "verified"} for w in wits],
        "foundation_batch": BATCH,
        "last_tested_at": STAMP,
        "verification": verification(),
    }


def main():
    missing = []
    for aid, (_, _, wits) in ANCHORS.items():
        pf, _ = pf_ns(aid)
        src = open(os.path.join(ROOT, pf), encoding="utf-8").read()
        missing += [
            f"{pf}:{w}"
            for w in wits
            if f"theorem {w} " not in src
            and f"theorem {w}\n" not in src
            and f"theorem {w} :" not in src
            and f"lemma {w} " not in src
        ]
    if missing:
        sys.exit(f"witnesses not found: {missing}")

    ledger = json.load(open(LEDGER, encoding="utf-8"))
    anchors = ledger["anchors"]
    anchors[:] = [a for a in anchors if a.get("foundation_batch") != BATCH]
    for aid in ANCHORS:
        anchors.append(build_anchor(aid))
    json.dump(ledger, open(LEDGER, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    open(LEDGER, "a", encoding="utf-8").write("\n")

    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    entries = [e for e in manifest["entries"] if e.get("declared_by") != BATCH]
    for aid, (_, _, wits) in ANCHORS.items():
        _, ns = pf_ns(aid)
        entries.append(
            {
                "anchor_id": aid,
                "proof_system": "lean4",
                "declared_by": BATCH,
                "witnesses": [ns + w for w in wits],
            }
        )
    manifest["entries"] = entries
    json.dump(
        manifest, open(MANIFEST, "w", encoding="utf-8"), ensure_ascii=False, indent=2
    )
    open(MANIFEST, "a", encoding="utf-8").write("\n")
    print(
        f"anchors: {len(ANCHORS)} added (ledger now {len(anchors)}); manifest entries {len(entries)}"
    )


if __name__ == "__main__":
    main()
