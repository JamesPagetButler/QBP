#!/usr/bin/env python3
"""PROOF anchors for the seam zero-divisor kernel theorems (PR #666) — encode-AFTER-prove.

Every anchor cites theorems on this branch, 0-sorry, `#print axioms` ⊆ {propext, Classical.choice,
Quot.sound}, reviewed (Red Team ×2, Gemini ×2). No root, principle, decision or kill is touched.
Every "NOT proved" caveat from SeamKernel.lean's docstring is repeated in its anchor: the kernel
facts are for the single witness x = e₁ + e₁₀; the converse "only cross-copy elements annihilate"
is not proved; the singular values (2 ×4, √2 ×8, 0 ×4) are numerical; nothing says multiplication
is the seam's physical operation; nothing about the flow. Manifest entries added alongside; then
`anchor_inverse_audit.py --update-baseline` records the anchored growth.
Usage: python3 scripts/encode_seam_kernel_anchors.py [--dry-run]
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
BATCH = "#666-seam-zero-divisor-kernel"
SK = "QBP.Foundations.SeamKernel."
F_SK = "proofs/QBP/Foundations/SeamKernel.lean"
VERIFIER = (
    "lake build (3020 jobs, exit 0) + #print axioms on all 65 declarations (lean-prover agent + "
    "qbp-oppenheimer re-run, 2026-09-20; PR #666 Red Team ×2, Gemini ×2)"
)
NOT_PHYS = (
    " NOT claimed: that multiplication is the seam's physical operation (the dynamics is the rule, #635; "
    "nothing on the ledger says a seam crossing is computed by a product); anything about the flow."
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
        "proof_file": F_SK,
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
        "PROOF-seam-zd-witness-kernel-four",
        "At the zero divisor x = e₁ + e₁₀, left multiplication has kernel exactly span{e₇+e₁₂, e₆−e₁₃, e₅+e₁₄, e₄−e₁₅}, dimension 4, rank 12",
        "Foundations/SeamKernel.lean: `seamL_ker_eq` (both inclusions — the kernel IS the span of the four explicit "
        "signed basis sums), `seam_finrank_ker_eq_four` (finrank 4), `seam_finrank_range_eq_twelve` (rank 12 by "
        "rank–nullity), packaged as `zd_witness_left_kernel_four`. Bench reading: multiplying by this zero divisor "
        "drops exactly 4 of 16 real components and passes 12 — a rank-12 linear map, not annihilation. Witness "
        "x·kᵢ = 0 for the four kernel vectors by coordinates (`seamX_mul_k1`…`k4`). NOT claimed: the same for the "
        "other 83 basis-sum zero divisors (PROOF-42zd's 42 planes) or for the zero-divisor locus — witness only "
        "(numerically all 84 have nullity 4; unproved)." + NOT_PHYS,
        SK + "zd_witness_left_kernel_four",
        [
            SK + "seamL_ker_eq",
            SK + "seam_finrank_ker_eq_four",
            SK + "seam_finrank_range_eq_twelve",
            SK + "seamX_mul_k1",
            SK + "seamX_mul_k2",
            SK + "seamX_mul_k3",
            SK + "seamX_mul_k4",
        ],
        ["PROOF-42zd"],
    ),
    anchor(
        "PROOF-seam-zd-witness-kernels-coincide",
        "At x = e₁ + e₁₀ the left and right kernels are EQUAL: the four erased directions are erased from both sides",
        "Foundations/SeamKernel.lean: `zd_witness_kernels_coincide` — kᵢ·x = 0 for the four vectors, ker L_x = ker R_x "
        "(an equality, `seamR_ker_eq` computes the right kernel independently), finrank of the right kernel 4. Bench "
        "reading: the component that left multiplication erases is not recoverable from right multiplication — it "
        "is erased there too. This is what makes 're-encoding into the kernel' (inter#119) fail as worded: the "
        "kernel is the set of erased directions, not a store. NOT claimed: recoverability from the seam's actual "
        "scattering (FLAG-seam-dynamics-open remains open) — this anchor speaks only of the two multiplications."
        + NOT_PHYS,
        SK + "zd_witness_kernels_coincide",
        [
            SK + "seamR_ker_eq",
            SK + "k1_mul_seamX",
            SK + "k2_mul_seamX",
            SK + "k3_mul_seamX",
            SK + "k4_mul_seamX",
        ],
        ["PROOF-seam-zd-witness-kernel-four"],
    ),
    anchor(
        "PROOF-seam-zd-witness-kernel-not-subalgebra",
        "The erased 4-space at x = e₁ + e₁₀ is not closed under the product: k₁·k₁ = −2·1 and (k₁·k₃).coord 2 = −2 leave the span",
        "Foundations/SeamKernel.lean: `zd_witness_kernel_not_subalgebra` (two witnesses), `k1_sq` (k₁·k₁ = (−2)•1 — the "
        "escaped product lands on the real scalar line), `k1_mul_k3_coord2`. Bench reading: the kernel has no "
        "arithmetic of its own; it is not a hidden sub-universe. NOT claimed: the full value k₁·k₃ = −2(e₂+e₉) "
        "(only coordinate 2 is proved; the rest is numerical)." + NOT_PHYS,
        SK + "zd_witness_kernel_not_subalgebra",
        [SK + "k1_sq", SK + "k1_mul_k3_coord2"],
        ["PROOF-seam-zd-witness-kernel-four"],
    ),
    anchor(
        "PROOF-frobenius-basis-sum-general",
        "For every sedenion x, Σ_j N(x·e_j) = 16·N(x): the Frobenius norm of left multiplication is that of a norm-preserving map — norm conservation is not information conservation",
        "Foundations/SeamKernel.lean: `sum_N_mul_basis_eq` (all x; a re-export of the fully general "
        "`NoAutonomousDynamics.sum_N_mul_basis`), instantiated at the witness as `zd_witness_frobenius_preserved` "
        "(= 16·N(x) = 32 while 4 directions are killed). Bench reading: a test that only checks total norm passes at "
        "a zero divisor where information is lost — so a seam theorem must test reversibility, not size. NOT claimed: "
        "how the surviving directions are scaled (numerically the singular values are 2 ×4, √2 ×8, 0 ×4 — four "
        "amplified, eight unchanged, four killed; unproved)." + NOT_PHYS,
        SK + "sum_N_mul_basis_eq",
        [SK + "zd_witness_frobenius_preserved", SK + "N_seamX"],
        ["PROOF-42zd"],
    ),
    anchor(
        "PROOF-encoding-copy-mul-injective",
        "Nonzero elements of the encoding octonion copy never annihilate under left or right multiplication in 𝕊",
        "Foundations/SeamKernel.lean: `octonion_copy_mul_injective` and `octonion_copy_mul_injective_right` — for "
        "x with cdHi x = 0 and x ≠ 0, y ↦ x·y and y ↦ y·x are injective on CDAlg ℝ 4 (via the Cayley–Dickson product "
        "formula with a zero high part, `cdLo_mul_of_lo`/`cdHi_mul_of_lo` and their right twins, and octonion norm "
        "composition). `seamX_not_in_octonion_copy`: the zero-divisor witness is not in the copy. Bench reading: "
        "information deletion by multiplication, if it happens at all, lives strictly at the seam (cross-copy "
        "elements). NOT claimed: the converse — that ONLY cross-copy elements can annihilate (the cdLo x = 0 mirror "
        "case is uncovered; non-alternativity blocks the easy argument)." + NOT_PHYS,
        SK + "octonion_copy_mul_injective",
        [
            SK + "octonion_copy_mul_injective_right",
            SK + "octonion_copy_mul_eq_zero_imp",
            SK + "octonion_copy_mul_eq_zero_imp_right",
            SK + "seamX_not_in_octonion_copy",
        ],
        ["PROOF-ops-norm-composition-ladder", "PROOF-42zd"],
    ),
]

CHANGELOG = {
    "version": "6.3.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the seam zero-divisor kernel theorems (PR #666; the beekeeper's "
        "information-deletion question of 2026-09-19/20) — encode-after-prove: at the witness e₁+e₁₀, left "
        "multiplication has an explicit 4-dim kernel and rank 12; left and right kernels coincide; the kernel is not a "
        "subalgebra; the Frobenius identity Σ N(x e_j) = 16 N(x) holds for every x (norm conservation ≠ information "
        "conservation); nonzero encoding-copy elements are injective on both sides. Five anchors, all 0-sorry, axiom "
        "closure {propext, Classical.choice, Quot.sound}. Every anchor carries its caveats (witness-only; converse "
        "unproved; singular values numerical; multiplication not shown to be the seam's operation). No root, "
        "principle, decision or kill touched; FLAG-seam-dynamics-open stays open. (Renumbered 6.3.0 at rebase after "
        "PR #665 landed as 6.2.0.)"
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
