#!/usr/bin/env python3
"""PROOF anchors for the substrate definition conversation's proved theorems (PR #663, #639).

Encode-AFTER-prove: every anchor below cites theorems that are on this branch, 0-sorry,
`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}, re-verified by the author. No
root, principle, decision or kill is touched — the INTERP-holographic-boundary kill rewrite
is NOT here (open item; a later PR). Written through the confined writer (#654 D7).
Every "NOT claimed" caveat from the file docstrings is repeated in the anchor description.

Also appends the 10 manifest entries (docs/cth/anchor-worthy-manifest.json, C1/C2/C3) —
the ledger and the manifest must move together. Run then:
  python3 scripts/anchor_inverse_audit.py --update-baseline   (records the anchored growth)
  python3 scripts/root_audit.py && python3 scripts/check_anchor_manifest.py \
    && python3 scripts/anchor_inverse_audit.py --check
Usage: python3 scripts/encode_definition_conversation_anchors.py [--dry-run]
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
BATCH = "#639-definition-conversation-proofs"
VERIFIER = (
    "lake build (3587 jobs, exit 0) + #print axioms on every new declaration "
    "(lean-prover agent + qbp-oppenheimer re-run, 2026-09-20; PR #663 Red Team ×2, "
    "Gemini ×2, §I4 statement-vs-claim APPROVE)"
)

CH = "QBP.Foundations.CrystalHosting."
HS = "QBP.Foundations.HolographicSubalgebra."
SH = "QBP.Substrate.Hosting."
F_CH = "proofs/QBP/Foundations/CrystalHosting.lean"
F_HS = "proofs/QBP/Foundations/HolographicSubalgebra.lean"
F_SH = "proofs/QBP/Substrate/Hosting.lean"


def _libs():
    m = json.loads(LAKE.read_text())
    out = {}
    for p in m["packages"]:
        if p["name"] in ("mathlib", "batteries"):
            out[p["name"]] = {"ref": p.get("inputRev") or p["rev"], "sha": p["rev"]}
    return out


def anchor(aid, name, desc, pfile, main, companions, chain):
    wits = [main] + companions
    return {
        "id": aid,
        "name": name,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": desc,
        "proof_file": pfile,
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
        "PROOF-hosted-eq-quatspan-nonpole",
        "A non-pole crystal's hosted algebra IS the quaternion span (equality, not ⊆)",
        "Substrate/Hosting.lean: `Universe.hosted_eq_quatSpan` — for a universe whose crystal is "
        "not a real multiple of ℓ (`Universe.NonPole`, equivalently `nonPole_iff`), there is a unit "
        "imaginary octonion u with U.hosted = {x | InQuatSpan (loOf u) x}; N u = 1 is derived, not "
        "assumed. Upgrades `universe_hosts_quaternion` (⊆ only) to a set equality. Foundations "
        "engine `genByPair_eq_quatSpan_of_param` (hypothesis α² + γ² ≠ 0). `polePlus_not_nonPole` "
        "shows the hypothesis excludes exactly the pole case, where `pole_hosts_complex` gives ℂ "
        "(dim 2). NOT claimed: canonicity of u (`Universe.dir` is a `Classical.choose`; u is "
        "determined only up to sign). Hosts; does not derive.",
        F_SH,
        SH + "Universe.hosted_eq_quatSpan",
        [
            SH + "Universe.nonPole_iff",
            SH + "polePlus_not_nonPole",
            CH + "genByPair_eq_quatSpan_of_param",
            SH + "exists_nonPole_universe",
        ],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-universe-intersection-eq-complex",
        "Two non-pole universes with different hosted algebras share exactly span{1, ℓ}",
        "Substrate/Hosting.lean: `universe_intersection_eq_complex` — if U₁, U₂ are non-pole and "
        "U₁.hosted ≠ U₂.hosted then U₁.hosted ∩ U₂.hosted = {a•1 + b•ℓ}. Foundations form "
        "`quatSpan_inter_eq_complex` takes u₁ ≠ u₂ and u₁ ≠ −u₂ literally; `inQuatSpan_neg_dir` "
        "(ℍ_{−u} = ℍ_u) shows u₁ ≠ ±u₂ IMPLIES the intrinsic hypothesis. NOT claimed: the converse "
        "(needs direction-uniqueness-up-to-sign, not in the tree). The generic pair of universes "
        "therefore interacts, algebraically, only through the plainest two-dimensional arithmetic.",
        F_SH,
        SH + "universe_intersection_eq_complex",
        [CH + "quatSpan_inter_eq_complex", CH + "inQuatSpan_neg_dir"],
        ["PROOF-hosted-eq-quatspan-nonpole"],
    ),
    anchor(
        "PROOF-quatdouble-rho-invariant-mul-closed",
        "Every Cayley–Dickson double ℍ ⊕ ℍ·ℓ of a quaternion span in 𝕆 is a ρ-invariant, "
        "multiplication-closed subset of 𝕊 — a continuum of candidates, not seven",
        "Foundations/HolographicSubalgebra.lean: for EVERY pair p q : 𝕆 (no hypothesis), "
        "`quatDouble p q` = {x | cdLo x, cdHi x ∈ span(gen4 p q)} contains 1 and ℓ, is closed under "
        "+, •, conj and multiplication (`mul_mem_quatDouble`), and is carried onto itself by the "
        "order-3 automorphism (`rotAut3_image_quatDouble`: ρ '' D = D, an equality). Mechanism: "
        "Artin's theorem does NOT apply in 𝕊 (`sedenion_not_alternative`); the proof uses the CD "
        "doubling formula in 𝕊 (`cdLo_mul`/`cdHi_mul`) to reduce to four 𝕆-products, then "
        "`QBP.Foundations.CDAlg.span4_mul_closed` (Artin in 𝕆) with `conj_mem_span_gen4`. Refutes "
        "the definition-conversation dyad's 'exactly 7 ρ-invariant octonion subalgebras' (the seven "
        "Fano doubles are members, not the whole). NOT claimed: that the double is 8-dimensional, "
        "alternative, or a composition algebra; any count of the family.",
        F_HS,
        HS + "rotAut3_image_quatDouble",
        [
            HS + "mul_mem_quatDouble",
            HS + "mem_quatDouble_iff",
            HS + "one_mem_quatDouble",
            HS + "ell_mem_quatDouble",
            HS + "quatDouble_proper",
        ],
        ["PROOF-order-three-automorphism-fixes-ell", "PROOF-quaternion-frame-maximal"],
    ),
    anchor(
        "PROOF-rho-moves-cd-half-as-set",
        "The order-3 automorphism moves the Cayley–Dickson half 𝕆_low as a SET (not only a witness)",
        "Foundations/CrystalHosting.lean: `rho_moves_cd_half` — rotAut3 '' lowHalf ≠ lowHalf, with "
        "`rotAut3_lowHalf_not_subset` and `exists_mem_lowHalf_rotAut3_not_mem`; strengthens "
        "`rotAut3_moves_lowHalf` (a single coordinate witness). Consequence for Decision 1 "
        "(INTERP-holographic-boundary, open): the P2′ reading's encoding half is NOT ρ-invariant, "
        "while every quatDouble is (PROOF-quatdouble-rho-invariant-mul-closed) — ρ-equivariance "
        "eliminates P2′ and constrains P2 not at all. Recorded as a RESULT; nothing ruled.",
        F_CH,
        CH + "rho_moves_cd_half",
        [
            CH + "rotAut3_lowHalf_not_subset",
            CH + "exists_mem_lowHalf_rotAut3_not_mem",
            CH + "mem_lowHalf",
        ],
        ["PROOF-order-three-automorphism-fixes-ell"],
    ),
    anchor(
        "PROOF-vacuum-hessian-transverse-eigenvalue",
        "At a vacuum the second derivative of the potential is 8(1−b₀²)‖P v‖² for every imaginary v "
        "(a genuine Mathlib deriv); zero at the poles; the −b₀ partner exists, so evenness is non-vacuous",
        "Foundations/CrystalHosting.lean §4c + Substrate/Hosting.lean §8b. `potential_taylor_at_vacuum`: "
        "V(s+tv) = N(L)t² + 2⟨L,Q⟩t³ + N(Q)t⁴ (no constant or linear term ⇒ a vacuum is a critical "
        "point of the rule). `deriv2_potential_at_vacuum`: d²/dt²|₀ V(s+tv) = hessQuad s v as a Mathlib "
        "`deriv`, so the Hessian is pinned, not asserted. `hessQuad_closed` from the 7-dim Lagrange "
        "identity; `hessQuad_eq_transverse`: for every imaginary v, hessQuad s v = 8(1−b₀²)·N(transverse "
        "component) — eigenvalue 8(1−b₀²) on the explicit 6-parameter transverse family, 0 on the "
        "9-parameter flat family; `hessQuad_pole_eq_zero`. `finrank_perpIm_eq_six`; an orthonormal "
        "6-frame EXISTS (`exists_orthonormal_perpIm_frame`, via a linear equivalence to Euclidean "
        "space and `bil_eq_inner`, a proved theorem); `hess_trace_transverse_exists`: trace 48(1−b₀²) "
        "with no undischarged hypothesis. Evenness is non-vacuous: `exists_pole_flip_vacuum` "
        "constructs the −b₀ partner; `hessQuad_eigenvalue_even_exists`. Universe level: "
        "see PROOF-vacuum-hessian-universe-level; dim 6 and the transverse trace: see "
        "PROOF-transverse-space-dim-six-trace. NOT claimed: the finrank identity rank = 14 − 8 = 6 for the "
        "full tangent form; the full-tangent-space trace; that b₀² is an automorphism invariant. "
        "Consequence stated in the records: the spectrum separates |b₀| levels only, not same-|b₀| "
        "crystals.",
        F_CH,
        CH + "hessQuad_eq_transverse",
        [
            CH + "potential_taylor_at_vacuum",
            CH + "deriv2_potential_at_vacuum",
            CH + "hessQuad_closed",
            CH + "hessQuad_pole_eq_zero",
            CH + "exists_pole_flip_vacuum",
            CH + "hessQuad_eigenvalue_even_exists",
        ],
        ["PROOF-substrate-hosting-definition"],
    ),
    anchor(
        "PROOF-transverse-space-dim-six-trace",
        "The transverse space u^⊥ ∩ Im𝕆 has dimension 6, carries an orthonormal 6-frame, and the "
        "transverse trace of the vacuum Hessian is 48(1−b₀²) with no undischarged hypothesis",
        "Foundations/HolographicSubalgebra.lean: `finrank_perpIm_eq_six` (rank–nullity for z ↦ (Re z, ⟨u,z⟩)); "
        "`exists_orthonormal_perpIm_frame` (six imaginary, u-orthogonal, unit, pairwise-orthogonal "
        "octonions — via `toEuclid : CDAlg ℝ n ≃ₗ EuclideanSpace` and `bil_eq_inner`, a PROVED theorem, "
        "not a transported axiom; no InnerProductSpace instance is placed on CDAlg); "
        "`transComp_surjOn_perpIm` (the transverse-component map is onto); `hess_trace_transverse` and "
        "`hess_trace_transverse_exists` (Σ Hess over the rescaled frame = 48(1−b₀²), the frame's existence "
        "discharged inside). Companion of PROOF-vacuum-hessian-transverse-eigenvalue. NOT claimed: the "
        "finrank identity rank = 14 − 8 = 6 for the full tangent form; the full-tangent-space trace.",
        F_HS,
        HS + "hess_trace_transverse_exists",
        [
            HS + "finrank_perpIm_eq_six",
            HS + "exists_orthonormal_perpIm_frame",
            HS + "transComp_surjOn_perpIm",
            HS + "hess_trace_transverse",
            HS + "bil_eq_inner",
        ],
        ["PROOF-vacuum-hessian-transverse-eigenvalue"],
    ),
    anchor(
        "PROOF-vacuum-hessian-universe-level",
        "Universe-level restatement: every non-pole universe has a transverse Hessian coefficient "
        "8(1−b₀²) with b₀ pinned to its crystal; two non-pole universes with equal b₀² share it",
        "Substrate/Hosting.lean §8b: `potential_taylor_at_universe`, `deriv2_potential_at_universe`, "
        "`universe_hessian_eigenvalue` (∃ u α γ b₀ with b₀ = U.crystal.coord (hiIdx 0) and, for every "
        "imaginary v, hessQuad U.crystal v = 8(1−b₀²)·N(transverse component)); `polePlus_hessian_eq_zero`; "
        "`universe_hessian_eigenvalue_depends_only_on_b0_sq` — for two non-pole universes with equal b₀², "
        "one λ is the transverse coefficient of BOTH Hessians. Restated after PR #663's Red Team found the "
        "first version a real-number tautology (deleted, not renamed) — the prove-before-encode gate "
        "working. NOT claimed: that b₀² is an automorphism invariant; separation of same-|b₀| crystals "
        "(the spectrum separates |b₀| levels only).",
        F_SH,
        SH + "universe_hessian_eigenvalue",
        [
            SH + "potential_taylor_at_universe",
            SH + "deriv2_potential_at_universe",
            SH + "polePlus_hessian_eq_zero",
            SH + "universe_hessian_eigenvalue_depends_only_on_b0_sq",
        ],
        [
            "PROOF-vacuum-hessian-transverse-eigenvalue",
            "PROOF-hosted-eq-quatspan-nonpole",
        ],
    ),
    anchor(
        "PROOF-encoding-family-constant-along-complex-lines",
        "Around a non-pole crystal, every quatDouble u w (w ⟂ u) contains the hosted algebra and is "
        "ρ-invariant; the family is constant along L_u-complex lines of u^⊥ ∩ Im𝕆, on which L_u² = −Id",
        "Foundations/HolographicSubalgebra.lean: `leftMul_sq_eq_neg` (u·(u·z) = −z for unit imaginary u) "
        "and `perp_stable_under_leftMul` make u^⊥ ∩ Im𝕆 a complex vector space under L_u; "
        "`quatSpan_subset_quatDouble` and `encoding_family_member` (w arbitrary — degenerate w "
        "included; the physical case is unit w ⟂ u); `quatDouble_eq_of_mul_u`: quatDouble u (u·w) = "
        "quatDouble u w. This is the definition conversation's replacement for the refuted claim that "
        "a generic crystal's algebra lies in no ρ-invariant octonion. NOT claimed: a bijection onto "
        "ℂP², the real dimension of the family, or transitivity of the crystal's stabiliser on it.",
        F_HS,
        HS + "quatDouble_eq_of_mul_u",
        [
            HS + "leftMul_sq_eq_neg",
            HS + "perp_stable_under_leftMul",
            HS + "quatSpan_subset_quatDouble",
            HS + "encoding_family_member",
            HS + "span_gen4_u_mul",
        ],
        [
            "PROOF-quatdouble-rho-invariant-mul-closed",
            "PROOF-hosted-eq-quatspan-nonpole",
        ],
    ),
    anchor(
        "PROOF-octonion-perp-module-span4-maximal",
        "In 𝕆, the orthogonal complement of a quaternion subalgebra is a two-sided module over it; "
        "ℍ ⊕ ℍ·z = 𝕆 for any nonzero z ⟂ ℍ; a multiplication-closed submodule containing ℍ is ℍ or 𝕆",
        "Foundations/HolographicSubalgebra.lean: `bil_mul_left_adjoint`/`bil_mul_right_adjoint` "
        "(⟨a·c, d⟩ = ⟨c, ā·d⟩, from the polarised composition identity `octonion_normMap_zero`); "
        "`perp_span4_left_module`, `perp_span4_right_module`; `rMul_injective` (h ↦ h·z injective for "
        "z ≠ 0); `span4_sup_rMul_eq_top`; `span4_maximal`. This is the 𝕆-level half of the "
        "definition conversation's completeness question (does the ℍ′ ⊕ ℍ′ℓ family exhaust the "
        "octonion subalgebras of 𝕊 containing ℍ_s?). NOT claimed: the 𝕊-level statement — 𝕊 is not "
        "a composition algebra, so the adjoint identity is unavailable there; completeness of the "
        "encoding family remains a CONJECTURE (98/98 numerical support in the records).",
        F_HS,
        HS + "span4_maximal",
        [
            HS + "bil_mul_left_adjoint",
            HS + "bil_mul_right_adjoint",
            HS + "perp_span4_left_module",
            HS + "perp_span4_right_module",
            HS + "rMul_injective",
            HS + "span4_sup_rMul_eq_top",
        ],
        ["PROOF-quaternion-frame-maximal"],
    ),
    anchor(
        "PROOF-encoding-family-transitive-of-aut",
        "Reduction: any octonion automorphism fixing u and carrying w₁ to w₂ lifts to an automorphism "
        "of 𝕊 that fixes every crystal of direction u and maps quatDouble u w₁ onto quatDouble u w₂",
        "Foundations/HolographicSubalgebra.lean: `encoding_family_transitive_of_aut` with `autLin_apply` "
        "and `map_span_gen4` — the diagonal Cayley–Dickson lift Ψ = cdLift ψ of ψ : CDAut 3 with ψ u = u, "
        "ψ w₁ = w₂. Reduces the 'no natural section' clause of the definition conversation's exit "
        "(a canonical ℂP²-bundle of encodings over the vacuum manifold) to ONE named input. NOT "
        "claimed: the existence of such ψ — continuous frame-transitivity of Aut(𝕆) is not in the "
        "toolchain (`G2Transitivity` has only the seven discrete signed-basis witnesses); measured "
        "20/20 numerically in the records, unproved.",
        F_HS,
        HS + "encoding_family_transitive_of_aut",
        [HS + "autLin_apply", HS + "map_span_gen4"],
        ["PROOF-encoding-family-constant-along-complex-lines"],
    ),
]

CHANGELOG = {
    "version": "6.1.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the substrate definition conversation's proved theorems "
        "(PR #663; #639) — encode-after-prove: hosted = quatSpan for non-pole crystals (equality); "
        "generic intersection = span{1,ℓ}; every ℍ⊕ℍℓ ρ-invariant and mul-closed (refutes 'exactly 7'); "
        "ρ moves the CD half as a set (ρ eliminates P2′, constrains P2 not at all — a result, nothing "
        "ruled); the vacuum Hessian eigenvalue 8(1−b₀²) via Mathlib deriv, dim 6, trace, evenness "
        "non-vacuous; encoding family constant along L_u-lines; 𝕆-level perp-module/maximality; the "
        "transitivity reduction. Ten anchors, all 0-sorry, axiom closure {propext, Classical.choice, "
        "Quot.sound}. NOT here: the INTERP-holographic-boundary kill rewrite (open; later PR); the false "
        "'generic ℍ_s in no ρ-invariant octonion' (refuted before any prover saw it). Manifest entries "
        "added; inverse-audit baseline updated to the anchored growth."
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
