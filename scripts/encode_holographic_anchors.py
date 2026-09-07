#!/usr/bin/env python3
"""DERIV-holographic, the theorem parts — CTH proof anchors (batch "#473-flag3", idempotent).

Beekeeper 2026-09-07: "prove what we can, then discuss the tail". proofs/QBP/Foundations/HolographicSubalgebra.lean
splits the ledger's derived principle DERIV-holographic ("observers require associativity; the largest associative
subalgebra of 𝕆 is ℍ; the 4D gap is the holographic boundary") into three PROVED parts and leaves the postulate
("observers require associativity") and the interpretation ("holographic boundary") explicitly unclaimed.
Anchors: PROOF-associative-composition-iff (H1), PROOF-quaternion-frame-maximal (H2 + H3 + H3′),
PROOF-quaternion-frame-codim-four (H4). The fully general "every associative subalgebra of 𝕆 has dim ≤ 4" is NOT
claimed (needs an orthonormal pair inside an arbitrary associative subalgebra ⇒ a registered inner-product structure;
architecture ruling 2026-09-07: its own foundational PR when needed). Usage: python3 scripts/encode_holographic_anchors.py
"""

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")
BATCH = "#473-flag3"
STAMP = "2026-09-07T00:00:00Z"
CLEAN = ["propext", "Classical.choice", "Quot.sound"]
MATHLIB = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
BATTERIES = "32dc18cde3684679f3c003de608743b57498c56f"
PF = "proofs/QBP/Foundations/HolographicSubalgebra.lean"
NS = "QBP.Foundations.HolographicSubalgebra."

ANCHORS = {
    "PROOF-associative-composition-iff": (
        "Composition of left-multiplications equals multiplication exactly on associative sets (L_x∘L_y = L_{xy} ⇔ assoc = 0)",
        "DERIV-holographic, theorem part 1 (flag 3). lMul_comp_eq_iff_assoc_forall: for A ⊆ CDAlg R n, "
        "(∀ x y ∈ A, L_x ∘ L_y = L_{x·y} as linear maps) ⇔ (∀ x y ∈ A, ∀ z, assoc x y z = 0); "
        "lMul_comp_eq_iff_assoc_mem: the version restricted to z ∈ A; lMul_comp_of_forall: the one-way bridge. "
        "Non-vacuity: lMul_comp_fails_on_octonions (the law fails on all of 𝕆) and lMul_comp_on_quaternion_frame "
        "(it holds on a quaternion frame). This is the theorem-shaped content of the POSTULATE 'observers require "
        "associativity' (measurements compose as multiplication only in associative substructures); the postulate "
        "itself is NOT proved and NOT claimed.",
        [
            "lMul_comp_eq_iff_assoc_forall",
            "lMul_comp_eq_iff_assoc_mem",
            "lMul_comp_of_forall",
            "lMul_comp_fails_on_octonions",
            "lMul_comp_on_quaternion_frame",
        ],
    ),
    "PROOF-quaternion-frame-maximal": (
        "Quaternion frames span{1,u,v,uv} of 𝕆 are associative subalgebras, and no associative subalgebra properly contains one",
        "DERIV-holographic, theorem part 2 (flag 3): 'the largest associative subalgebra of 𝕆 is ℍ', frame-relative. "
        "For orthonormal imaginary u, v ∈ 𝕆: quaternion_frame_table (u² = v² = (uv)² = −1, vu = −uv, u(uv) = −v, "
        "(uv)u = v, v(uv) = u, (uv)v = −u — general, from imaginary_sq, anticommutation, alternativity, flexibility, "
        "norm composition, no decide); quaternion_frame_subalgebra (span{1,u,v,uv} closed and associative — the Artin "
        "chunks instantiated). assoc_orthogonal_triple: for orthogonal imaginary u, v, w with w ⟂ uv, "
        "assoc u v w = 2·(uv)w, via the left Moufang law; assoc_orthogonal_triple_ne_zero. span4_eq_of_associative / "
        "finrank_eq_four_of_associative / not_associative_of_gt_span4: any associative subalgebra S containing the "
        "frame equals it (dim 4). Concrete cross-check: assoc e₁ e₂ e₄ ≠ 0 by kernel decide (coefficient 2 agrees with "
        "the structural route). quaternion_frame_subalgebra itself carries no orthonormality hypotheses (Artin closure for "
        "any pair); orthonormality enters only through the frame's independence and the maximality theorem, whose primary "
        "witness is span4_eq_of_associative. NOT claimed: the fully general 'every associative subalgebra of 𝕆 has dim ≤ 4' "
        "— DEFERRED, not blocked: closing it needs an orthonormal imaginary pair inside an arbitrary associative subalgebra "
        "of dimension ≥ 3 (a two-step explicit Gram–Schmidt over the existing bil with Real.sqrt; elementary, no Mathlib "
        "InnerProductSpace instance required); deferred per the architecture ruling 2026-09-07 (a registered inner-product "
        "structure on CDAlg, if ever wanted, is its own foundational PR).",
        [
            "span4_eq_of_associative",
            "not_associative_of_gt_span4",
            "finrank_eq_four_of_associative",
            "quaternion_frame_subalgebra",
            "quaternion_frame_table",
            "assoc_orthogonal_triple",
            "assoc_orthogonal_triple_ne_zero",
            "mul_assoc_flip",
            "assoc_e1_e2_e4_ne_zero",
            "assoc_e1_e2_e4_ne_zero_structural",
            "fano_pair_frame",
            "residual_orth_uv",
            "bil_proj4",
        ],
    ),
    "PROOF-quaternion-frame-codim-four": (
        "A quaternion frame is a 4-dimensional subspace of the 8-dimensional 𝕆: codimension 4",
        "DERIV-holographic, theorem part 3 (flag 3): 'the 4D gap' as a number. quaternion_frame_linearIndependent "
        "({1, u, v, uv} independent from pairwise bil-orthogonality + N = 1, proved); finrank_quaternion_frame = 4; "
        "quaternion_frame_codim_four: finrank span + 4 = finrank (CDAlg ℝ 3) = 8 (additive form; the subtraction form "
        "as corollary; uses PROOF-cd-algebra-finrank-2n). The interpretation 'the 4D gap is the holographic boundary' "
        "is NOT claimed — no boundary, holography, spacetime or physics semantics appears in any statement.",
        [
            "quaternion_frame_codim_four",
            "quaternion_frame_codim_four'",
            "finrank_quaternion_frame",
            "quaternion_frame_linearIndependent",
            "gen4_eq_range",
            "bil_u_uv",
            "bil_v_uv",
        ],
    ),
}


def main():
    src = open(os.path.join(ROOT, PF), encoding="utf-8").read()
    for aid, (_, _, wits) in ANCHORS.items():
        missing = [
            w
            for w in wits
            if f"theorem {w} " not in src
            and f"theorem {w}\n" not in src
            and f"theorem {w} :" not in src
        ]
        if missing:
            sys.exit(f"{aid}: witnesses not found: {missing}")
    ledger = json.load(open(LEDGER, encoding="utf-8"))
    anchors = ledger["anchors"]
    anchors[:] = [a for a in anchors if a.get("foundation_batch") != BATCH]
    for aid, (name, desc, wits) in ANCHORS.items():
        anchors.append(
            {
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
                "proof_file": PF,
                "sorry_count": 0,
                "proof_state": "verified",
                "lean_theorem": NS + wits[0],
                "lean_companion_theorems": [NS + w for w in wits[1:]],
                "theorems": [{"name": w, "status": "verified"} for w in wits],
                "foundation_batch": BATCH,
                "last_tested_at": STAMP,
                "verification": {
                    "toolchain": "leanprover/lean4:v4.30.0",
                    "libraries": {
                        "mathlib": {"ref": MATHLIB, "sha": MATHLIB},
                        "batteries": {"ref": "main", "sha": BATTERIES},
                    },
                    "verified_at": STAMP,
                    "verifier": "lake build QBP.Foundations.HolographicSubalgebra (targeted, 2959 jobs) and the QBP.Foundations umbrella (3546 jobs) + #print axioms ×45 (qbp-oppenheimer + lean-prover agent, 2026-09-07); pending cth §I4",
                    "result": "verified",
                    "axiom_closure": CLEAN,
                },
            }
        )
    json.dump(ledger, open(LEDGER, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    open(LEDGER, "a", encoding="utf-8").write("\n")
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    entries = [e for e in manifest["entries"] if e.get("declared_by") != BATCH]
    for aid, (_, _, wits) in ANCHORS.items():
        entries.append(
            {
                "anchor_id": aid,
                "proof_system": "lean4",
                "declared_by": BATCH,
                "witnesses": [NS + w for w in wits],
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
