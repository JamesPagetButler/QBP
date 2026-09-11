#!/usr/bin/env python3
"""P2′ lemmas + the order-3 element of Aut(𝕊)'s S₃ factor — CTH proof anchors (batch "#649-p2-lean", idempotent).

PR #649 (the P2 vs P2′ rigor audit) owed three Lean items: (i) ℍ_u ∩ 𝕆_low = ℂ_u; (ii) ℍ_u = ℂ_u ⊕ ℂ_u·ℓ;
(iii) the ℓ-fixing order-3 automorphism ρ of 𝕊 as a CDAut 4, with hosting-equivariance under it (hosting AC(e)).
All three are on branch research/p2-lean-followups (CrystalHosting.lean §2/§3, Hosting.lean §9).
Anchors: PROOF-hosted-algebra-meets-cell-in-complex-line ((i)+(ii)); PROOF-order-three-automorphism-fixes-ell ((iii)).
NOT claimed: Brown's Aut(𝕊) = G₂ × S₃; that gradeAut and ρ generate the S₃ factor. Usage: python3 scripts/encode_p2_lean_anchors.py
"""

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")
BATCH = "#649-p2-lean"
STAMP = "2026-09-10T00:00:00Z"
CLEAN = ["propext", "Classical.choice", "Quot.sound"]
MATHLIB = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
BATTERIES = "32dc18cde3684679f3c003de608743b57498c56f"
CH = ("proofs/QBP/Foundations/CrystalHosting.lean", "QBP.Foundations.CrystalHosting.")
HO = ("proofs/QBP/Substrate/Hosting.lean", "QBP.Substrate.Hosting.")

ANCHORS = {
    "PROOF-hosted-algebra-meets-cell-in-complex-line": (
        CH,
        "The hosted quaternion algebra ℍ_u meets the Cayley–Dickson low half in exactly ℂ_u = span{1, U}, and equals the CD double of that ℂ by ℓ",
        "P2′ lemmas (PR #649 §6 item 2). quatSpan_inter_lowHalf: for a unit imaginary octonion direction u, "
        "InQuatSpan (loOf u) x ∧ cdHi x = 0 ⇔ ∃ a c, x = a•1 + c•loOf u — the hosted algebra span{1, ℓ, U, ℓU} meets the "
        "low-half octonions in exactly the complex line ℂ_u. quatSpan_eq_cd_double: InQuatSpan (loOf u) x ⇔ "
        "∃ a c b d, x = (a•1 + c•U) + (b•1 + d•U)·ℓ — ℍ_u = ℂ_u ⊕ ℂ_u·ℓ, the Cayley–Dickson double of ℂ_u by ℓ. "
        "These are the whole mathematical content of the P2′ reading (the encoding octonion as a CD half): the "
        "observer's algebra straddles the halves and the half sees one ℂ of it. Both directions of both iffs proved. "
        "NOT claimed: which reading (P2 or P2′) AXIOM-2 means — that is the beekeeper's ruling (ruling bundle, PR #652).",
        [
            "quatSpan_inter_lowHalf",
            "quatSpan_eq_cd_double",
            "inQuatSpan_ell_right",
            "crystal_quatSpan_independent",
        ],
    ),
    "PROOF-order-three-automorphism-fixes-ell": (
        CH,
        "An ℓ-fixing order-3 automorphism ρ of 𝕊 (the order-3 element of the S₃ factor under Brown 1967, not claimed here), as a CDAut 4: ρ³ = id, ρ(ℓ) = ℓ, ρ ≠ id, multiplicative — and hosting is equivariant under it",
        "PR #649 confirmer finding 1 / #639 (e). rotMap3 rotates each plane (e_k, e_k·ℓ), k = 1..7, by 2π/3 with 1 and ℓ "
        "fixed (c = cos(2π/3) = −1/2, s = sin(2π/3) = √3/2). rotMap3_mul (via rot_lo_mul / rot_hi_mul through the CD "
        "doubling formula, reCoord_mul and mul_swap_eq from ArtinTrace; the nine coefficient identities close under "
        "c = −1/2, s² = 3/4 — i.e. at θ = ±2π/3 — Lean proves sufficiency; that other angles fail is numerical, aut_s3.py): ρ(xy) = ρx·ρy. "
        "rotAut3 : CDAut 4 (linear, multiplicative, bijective); rotAut3_ell: ρ ℓ = ℓ; rotAut3_pow_three: ρ³ = id; "
        "rotAut3_ne_id: ρ(loOf e₁) ≠ loOf e₁ (order exactly 3); rotMap3_loOf / rotMap3_loOf_mul_ell: the action on U and "
        "U·ℓ (sign convention checked against loOf_mul_ell, e_k·ℓ = +e_{k+8}). Consequences: rotAut3_hosting_equivariant "
        "(aut_hosting_equivariant applies since ρ fixes ℓ) and Substrate.Hosting.hosting_equivariant_rot3 — crystal-"
        "covariance across the order-3 elements of S₃, which the master docstrings had wrongly recorded as 'moving ℓ' "
        "(they fix ℓ; the reflections, gradeAut among them, move it — aut_s3.py). Consequence for P2′: ρ carries the CD "
        "low half out of itself — rotAut3_moves_lowHalf (Lean: cdHi (ρ (loOf e₁)) ≠ 0), so ρ(𝕆_low) ⊄ 𝕆_low; that the three halves form a ℤ/3-torsor is asserted numerically in p2_cell_torsor_check.py — so "
        "'the cell' is a discrete choice, not canonical. NOT claimed: Brown's Aut(𝕊) = G₂ × S₃; that gradeAut and ρ "
        "generate the S₃ factor.",
        [
            "rotAut3_hosting_equivariant",
            "rotAut3_moves_lowHalf",
            "rotMap3_mul",
            "rot_lo_mul",
            "rot_hi_mul",
            "rotAut3_ell",
            "rotAut3_pow_three",
            "rotAut3_ne_id",
            "rotMap3_loOf",
            "rotMap3_loOf_mul_ell",
            "rotMap3_cube",
            "reCoord_mul",
            "mul_swap_eq",
        ],
    ),
    "PROOF-hosting-equivariant-under-order-three": (
        HO,
        "Universe-level restatement: a universe's crystal, membership and hosted algebra are carried along by the order-3 automorphism ρ",
        "Substrate/Hosting.lean §9: hosting_equivariant_rot3 restates CrystalHosting.rotAut3_hosting_equivariant on the "
        "Universe structure (IsVacuum (ρ crystal) ∧ ρ crystal ∈ StateSphere ∧ ∀ x ∈ hosted, ρ x ∈ (map ρ).hosted). With "
        "hosting_equivariant (G₂ side) and hosting_equivariant_grade (the ℤ/2), crystal-covariance now holds for every "
        "generator of the S₃ factor that is constructed; the residue owned by #639 (e) is Brown's Aut(𝕊) = G₂ × S₃ and "
        "that these generate the S₃. Hosts; does not derive.",
        [
            "hosting_equivariant_rot3",
            "hosting_equivariant",
            "hosting_equivariant_grade",
        ],
    ),
}


CHAINS = {
    "PROOF-hosted-algebra-meets-cell-in-complex-line": [
        "PROOF-crystal-hosts-quaternion",
        "AXIOM-2",
    ],
    "PROOF-order-three-automorphism-fixes-ell": [
        "PROOF-crystal-hosts-quaternion",
        "PROOF-alternator-vanishes-iff-commute",
    ],
    "PROOF-hosting-equivariant-under-order-three": [
        "PROOF-order-three-automorphism-fixes-ell",
        "PROOF-substrate-hosting-definition",
    ],
}


def verification(pf):
    return {
        "toolchain": "leanprover/lean4:v4.30.0",
        "libraries": {
            "mathlib": {"ref": MATHLIB, "sha": MATHLIB},
            "batteries": {"ref": "main", "sha": BATTERIES},
        },
        "verified_at": STAMP,
        "verifier": f"lake build QBP.Foundations QBP.Substrate (3549 jobs) + #print axioms on {pf} (lean-prover agent + qbp-oppenheimer, 2026-09-10); pending cth §I4",
        "result": "verified",
        "axiom_closure": CLEAN,
    }


def main():
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
        src = open(os.path.join(ROOT, pf), encoding="utf-8").read()
        missing = [
            w
            for w in wits
            if f"theorem {w.split('.')[-1]} " not in src
            and f"theorem {w.split('.')[-1]}\n" not in src
            and f"theorem {w.split('.')[-1]} :" not in src
            and f"def {w.split('.')[-1]} " not in src
        ]
        if missing:
            print(f"ERROR: {aid}: witnesses not found in {pf}: {missing}")
            sys.exit(1)
    with open(LEDGER, encoding="utf-8") as f:
        ledger = json.load(f)
    anchors = ledger["anchors"]
    anchors[:] = [a for a in anchors if a.get("foundation_batch") != BATCH]
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
        anchors.append(
            {
                "id": aid,
                "name": name,
                "tier": 1,
                "layer_tag": "T",
                "status": "coherent",
                "provenance_kind": "proof",
                "description": desc,
                "proof_file": pf,
                "proof_language": "lean4",
                "proof_state": "verified",
                "lean_theorem": ns + wits[0],
                "lean_companion_theorems": [ns + w for w in wits[1:]],
                "sorry_count": 0,
                "provenance": "T",
                "prediction_chain": CHAINS[aid],
                "foundation_batch": BATCH,
                "last_tested_at": STAMP,
                "verification": {
                    **verification(pf),
                    "witnesses": [ns + w for w in wits],
                },
            }
        )
    ledger["last_updated"] = STAMP
    ledger["update_provenance"] = (
        f"qbp-oppenheimer 2026-09-10: {BATCH} — P2′ lemmas + the order-3 automorphism (3 proof anchors)"
    )
    with open(LEDGER, "w", encoding="utf-8") as f:
        json.dump(ledger, f, ensure_ascii=False, indent=2)
        f.write("\n")
    with open(MANIFEST, encoding="utf-8") as f:
        manifest = json.load(f)
    entries = [e for e in manifest["entries"] if e.get("declared_by") != BATCH]
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
        entries.append(
            {
                "anchor_id": aid,
                "declared_by": BATCH,
                "proof_system": "lean4",
                "witnesses": [ns + w for w in wits],
            }
        )
    manifest["entries"] = entries
    with open(MANIFEST, "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=2)
        f.write("\n")
    print(
        f"anchors: {len(ANCHORS)} added (ledger now {len(anchors)}); manifest entries {len(entries)}"
    )


if __name__ == "__main__":
    main()
