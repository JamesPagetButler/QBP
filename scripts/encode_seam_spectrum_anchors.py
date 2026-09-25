#!/usr/bin/env python3
"""PROOF anchors for the seam zero-divisor spectrum (PR #682, #473 Lean target 6(ii)) — encode-AFTER-prove.

Four anchors for `proofs/QBP/Foundations/SeamSpectrum.lean`: at the canonical basis-sum zero divisor
z₊ = e₁ + e₁₀ the Gram operator G₊ = L_{z₊}ᵀL_{z₊} = −L_{z₊}² has spectrum exactly {4 (×4), 2 (×8), 0 (×4)}
with the eigenspaces identified as explicit spans; the top plane E₄(G₊) lies on the frozen ridge V = 1
of the state sphere and equals ker L_{z₋}; the right-multiplication Gram operator equals G₊ on the nose
(sign-table identity, NOT alternativity); and the uniform, pair-generic facts (spectrum ⊆ [0,4];
E₄ = ker L_{z₋}; E₀ = ker L_z) for EVERY basis pair. Every anchor cites theorems on this branch,
0-sorry, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound} (153/153 in the file's §7 audit:
150 × the full triple + 3 × {propext}), reviewed (PR #682 Red Team APPROVE at 74ed74c; Gemini
APPROVE). No root, principle, decision or kill is touched; FLAG-locale-forcing-route-reopened is not
touched. Gemini's four negative constraints go verbatim into EVERY anchor's NOT-claimed clause: no
multiplicity claim for the other 83 basis-sum zero divisors; nothing about ad_z or a generic unforced t;
no bearing on the flow / orbits / endpoint / Prop 13(b) / the FLAG; NoAutonomousDynamics.lean's caveat
is DERIVED only for L_z and R_z at the canonical generator pair and the anchored file was not edited.
Manifest entries added alongside; then `anchor_inverse_audit.py --update-baseline` records the
anchored growth.
Usage: python3 scripts/encode_seam_spectrum_anchors.py [--dry-run]
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
BATCH = "#682-seam-spectrum"
SS = "QBP.Foundations.SeamSpectrum."
F_SS = "proofs/QBP/Foundations/SeamSpectrum.lean"
VERIFIER = (
    "run-bounded lake build QBP.Foundations.SeamSpectrum (3021 jobs, exit 0) + fresh `lake env lean` "
    "elaboration (0 errors) + #print axioms on all 153 declarations of the file's audit block: "
    "150 × {propext, Classical.choice, Quot.sound} + 3 × {propext} (midIdx, midIdx_spec, seam_xor_idx) "
    "(qbp-oppenheimer, 2026-09-25; PR #682 Red Team APPROVE at 74ed74c, Gemini APPROVE)"
)
# #666's seam-kernel anchor (ker L_{z₊} = the 4-space at e₁ + e₁₀) and the #473-ac2 no-autonomous-dynamics
# anchor whose caveat §3 of the note scopes.
CHAIN = ["PROOF-seam-zd-witness-kernel-four", "PROOF-no-autonomous-algebraic-dynamics"]
NOT_CLAIMED = (
    " NOT claimed: the 4/8/4 multiplicities for any of the other 83 basis-sum zero divisors (multiplicity "
    "is proved only at the canonical pair {1,10}; the uniform theorems fix no multiplicity); anything about "
    "ad_z = L_z − R_z or a generic unforced t (attack 2 measures 4/6/6 for ad_z; observed-only); any bearing "
    "on the flow, orbits, the crystallisation endpoint, Prop 13(b), or the status of "
    "FLAG-locale-forcing-route-reopened; that NoAutonomousDynamics.lean's caveat is closed — it is DERIVED "
    "only for L_z and R_z at the canonical generator pair, and the anchored file was not edited."
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
        "proof_file": F_SS,
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
        "PROOF-seam-zd-gram-spectrum-4-8-4",
        "At the canonical zero divisor z₊ = e₁ + e₁₀ the Gram operator G₊ = L_{z₊}ᵀL_{z₊} = −L_{z₊}² has spectrum exactly {4 (×4), 2 (×8), 0 (×4)}: G(G−2)(G−4) = 0, eigenspaces exact as explicit spans, the three eigen-projectors sum to id",
        "Foundations/SeamSpectrum.lean: at the canonical pair {1,10} (z₊ = e₁ + e₁₀, `seamX`) the "
        "left-multiplication Gram operator G₊ := −L_{z₊}² (`seamG`) is the Gram operator of L_{z₊} for the "
        "coordinate bilinear form, ⟪L y, L w⟫ = ⟪y, G w⟫ (`seamGram_eq`), and satisfies the cubic "
        "G(G−2)(G−4) = 0 (`seamG_cubic`, the main theorem). The eigenspaces are identified EXACTLY as explicit "
        "spans: E₄ = topSpan (`seamEig_four_eq`), E₂ = midSpan (`seamEig_two_eq`), E₀ = seamKerSpan, the #666 "
        "kernel of L_{z₊} (`seamEig_zero_eq`), with finranks 4 / 8 / 4 (`finrank_seamEig_four`, "
        "`finrank_seamEig_two`, `finrank_seamEig_zero`). The three eigen-projectors sum to the identity "
        "(`proj_decomp`), so G₊ is diagonalised over ℝ; completeness is over the REAL spectrum — G₊ is "
        "self-adjoint for the coordinate form (`seamG_self_adjoint`) and the three eigenspaces exhaust 𝕊 as "
        "submodules, M ⊔ T ⊔ K = ⊤ (`midSpan_sup_topSpan_sup_seamKerSpan`), so the complexified operator is "
        "diagonal with the same entries and no complex eigenvalue can hide. This is the 4/8/4 decomposition "
        "attack 2 measured numerically at the witness, now a theorem at the witness."
        + NOT_CLAIMED,
        SS + "seamG_cubic",
        [
            SS + "seamGram_eq",
            SS + "seamEig_four_eq",
            SS + "seamEig_two_eq",
            SS + "seamEig_zero_eq",
            SS + "finrank_seamEig_four",
            SS + "finrank_seamEig_two",
            SS + "finrank_seamEig_zero",
            SS + "proj_decomp",
            SS + "seamG_self_adjoint",
            SS + "midSpan_sup_topSpan_sup_seamKerSpan",
        ],
        CHAIN,
    ),
    anchor(
        "PROOF-seam-top-plane-on-frozen-ridge",
        "Every unit vector of the top eigenspace E₄(G₊) at z₊ = e₁ + e₁₀ lies on the frozen ridge V = 1 of the state sphere; E₄(G₊) = ker L_{z₋}; z₊·x = 0 ⇔ x ∈ E₀(G₊)",
        "Foundations/SeamSpectrum.lean: `top_plane_on_ridge_mem` (the main theorem) — for every t in the top "
        "eigenspace T = E₄(G₊) = topSpan of PROOF-seam-zd-gram-spectrum-4-8-4, V(t) = N(t)² (`potV`, the "
        "sedenion potential), i.e. every unit vector of T has V = 1 and lies on the frozen ridge of the state "
        "sphere — the observed [1.0000, 1.0000] of attack 2 §3 DERIVED for the entire 4-plane, not sampled. "
        "`top_plane_zero_divisor`: every nonzero t ∈ T is a two-sided zero divisor against z₋ = e₁ − e₁₀ "
        "(`seamXm`): z₋·t = 0 and t·z₋ = 0, so T is a 4-dimensional ridge plane inside the 42-plane system. "
        "`seamLm_ker_eq`: ker L_{z₋} = topSpan, i.e. E₄(G₊) = ker L_{z₋} — the first ridge identity, the "
        "companion of E₀(G₊) = ker L_{z₊}: z₊·x = 0 ⇔ x ∈ E₀(G₊) = seamKerSpan (`seamEig_zero_eq` of the "
        "spectrum anchor; the #666 kernel), so the two eigenspaces at the ends of the spectrum are exactly the "
        "two kernels of the paired zero divisors z₊, z₋." + NOT_CLAIMED,
        SS + "top_plane_on_ridge_mem",
        [SS + "top_plane_zero_divisor", SS + "seamLm_ker_eq"],
        CHAIN,
    ),
    anchor(
        "PROOF-seam-right-gram-equals-left",
        "At z₊ = e₁ + e₁₀ the right-multiplication Gram operator R_{z₊}ᵀR_{z₊} EQUALS G₊ = L_{z₊}ᵀL_{z₊} on the nose, via the sign-table identity (x·z)·z = z·(z·x) — NOT via alternativity, which fails in 𝕊 — so R_{z₊} shares the spectrum and eigenspaces",
        "Foundations/SeamSpectrum.lean: `seamGR_eq_seamG` (the main theorem) — the right Gram operator "
        "G_R := −R_{z₊}² (`seamGR`) equals G₊ = −L_{z₊}² as linear maps. The route is the sign-table identity "
        "`seam_gram_lr`: (x·z₊)·z₊ = z₊·(z₊·x) for every sedenion x, proved from the Cayley–Dickson sign table "
        "at the {1,10} block — NOT from alternativity, which FAILS in 𝕊 (no (x·z)·z = x·(z·z) is used or true). "
        "`seamRGram_eq`: ⟪R y, R w⟫ = ⟪y, G₊ w⟫, so G₊ is also the Gram operator of R_{z₊}; hence R_{z₊} has "
        "the SAME spectrum {4 (×4), 2 (×8), 0 (×4)} on the SAME subspaces T, M, K, and every singular value "
        "and top-space statement of PROOF-seam-top-plane-on-frozen-ridge transfers to right multiplication. "
        "`seamRm_ker_eq`: ker R_{z₋} = topSpan, the right-multiplication ridge identity (with #666's "
        "kernels-coincide: the left and right kernels of z₊ agree, so E₀ is two-sided as well). This is the "
        "'if cheap' item of the note's §1 and it was cheap: one sign-table identity."
        + NOT_CLAIMED,
        SS + "seamGR_eq_seamG",
        [SS + "seam_gram_lr", SS + "seamRGram_eq", SS + "seamRm_ker_eq"],
        CHAIN,
    ),
    anchor(
        "PROOF-basis-pair-gram-uniform-bounds",
        "For EVERY basis pair a, b ≠ 0 and sign s = ±1, z = e_a + s·e_b: any real eigenvalue of G_z = L_zᵀL_z on a nonzero eigenvector lies in [0,4]; E₄(G₊) = ker L_{z₋}; E₀(G_z) = ker L_z — uniform, pair-generic, NO multiplicity fixed",
        "Foundations/SeamSpectrum.lean: for every a, b : Fin 16 with a, b ≠ 0 and s ∈ {1, −1}, z = sbp a b s = "
        "e_a + s·e_b, with `sbpL a b s` = L_z, `sbpG a b s` = −L_z² and `sbpEig a b s c` the c-eigenspace: "
        "`sbpG_eigenvalue_mem_Icc` (the main theorem) — any real c with a NONZERO x ∈ sbpEig a b s c satisfies "
        "c ∈ [0, 4]; `sbpEig_four_eq` — sbpEig a b 1 4 = ker (sbpL a b (−1)), i.e. E₄(G₊) = ker L_{z₋} for every "
        "pair; `sbpEig_zero_eq` — sbpEig a b s 0 = ker (sbpL a b s), i.e. E₀(G_z) = ker L_z for every pair and "
        "sign. The tools: `sbpGram_eq` (sbpG really is L_zᵀL_z: ⟪L_z y, L_z w⟫ = ⟪y, G_z w⟫, so G_z is "
        "self-adjoint and no complex eigenvalue can escape [0,4]), `sbpG_rayleigh` (the Rayleigh quotient "
        "⟪y, G_z y⟫ = N(z·y)), `N_basisPair_split` (N(z₊·x) + N(z₋·x) = 4·N(x) for every pair, a, b unrestricted) "
        "and `N_basisPair_le_neg` (N(z₋·x) ≤ 4·N(x)), `basisPair_sq_split` (L_{z₊}² + L_{z₋}² = −4·id, i.e. "
        "G₊ + G₋ = 4·id), `sbp_sq_eq_zero_iff` (z·(z·x) = 0 ⇔ z·x = 0, so E₀(G_z) is exactly the kernel). NO "
        "multiplicity is fixed by any of these — they bound the spectrum and name two eigenspaces, nothing more. "
        "Anti-vacuity: the {1,10} instance is the §4 witness operator — `sbpL_seam` (sbpL 1 10 1 = seamL, by rfl), "
        "`sbpG_seam` (sbpG 1 10 1 = seamG), `sbpEig_seam` (sbpEig 1 10 1 c = seamEig c), so at the canonical pair "
        "these specialise to the 4/8/4 statements of PROOF-seam-zd-gram-spectrum-4-8-4 with E₄ of finrank 4. "
        "(`N_basisPair_split` quantifies over all a, b : Fin 16, including a = b and 0 — true but vacuous "
        "cases; the 84 basis-sum zero divisors are a strict subset of what is quantified.)"
        + NOT_CLAIMED,
        SS + "sbpG_eigenvalue_mem_Icc",
        [
            SS + "sbpEig_four_eq",
            SS + "sbpEig_zero_eq",
            SS + "sbpGram_eq",
            SS + "sbpG_rayleigh",
            SS + "N_basisPair_split",
            SS + "N_basisPair_le_neg",
            SS + "basisPair_sq_split",
            SS + "sbp_sq_eq_zero_iff",
            SS + "sbpL_seam",
            SS + "sbpG_seam",
            SS + "sbpEig_seam",
        ],
        CHAIN,
    ),
]

CHANGELOG = {
    "version": "6.10.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the seam zero-divisor spectrum (PR #682; #473 Lean target 6(ii)) — "
        "encode-after-prove: at the canonical basis-sum zero divisor z₊ = e₁ + e₁₀ the Gram operator "
        "G₊ = L_{z₊}ᵀL_{z₊} = −L_{z₊}² has spectrum exactly {4 (×4), 2 (×8), 0 (×4)} (G(G−2)(G−4) = 0, eigenspaces "
        "exact as explicit spans, projectors sum to id, completeness over the real spectrum); every unit vector of "
        "the top plane E₄(G₊) lies on the frozen ridge V = 1 and E₄(G₊) = ker L_{z₋}, E₀(G₊) = ker L_{z₊}; the "
        "right Gram operator R_{z₊}ᵀR_{z₊} equals G₊ on the nose via the sign-table identity (x·z)·z = z·(z·x) "
        "(not alternativity); and for EVERY basis pair and sign the spectrum of G_z lies in [0,4] with "
        "E₄(G₊) = ker L_{z₋} and E₀(G_z) = ker L_z (no multiplicity fixed). Four anchors, all 0-sorry, axiom "
        "closure {propext, Classical.choice, Quot.sound} (153/153 audited: 150 × the triple + 3 × {propext}), "
        "chained to PROOF-seam-zd-witness-kernel-four (#666) and PROOF-no-autonomous-algebraic-dynamics. Every "
        "anchor carries Gemini's four negative constraints verbatim: no multiplicity claim for the other 83 "
        "basis-sum zero divisors; nothing about ad_z = L_z − R_z or a generic unforced t (observed-only, 4/6/6 for "
        "ad_z); no bearing on the flow, orbits, the crystallisation endpoint, Prop 13(b) or "
        "FLAG-locale-forcing-route-reopened; NoAutonomousDynamics.lean's caveat is DERIVED only for L_z and R_z "
        "at the canonical generator pair and the anchored file was not edited. No root, principle, decision or "
        "kill touched. (Version 6.10.0: encoded on master 6.9.0/335 after #681 landed; the earlier 6.10.0 claim on base 6.8.0 was re-encoded here, records unchanged.); #681 claims 6.9.0 — this PR "
        "renumbers and re-encodes after #681 lands.)"
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
