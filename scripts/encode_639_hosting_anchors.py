#!/usr/bin/env python3
"""#639 hosting groundwork + the first Substrate/ file — CTH proof anchors (batch "#639-hosting", idempotent).

  PROOF-vacuum-parametrisation          — Prop 15 (#634 AC3): IsVacuum s ⇔ cdLo s = α u, cdHi s = b₀ + γ u.
  PROOF-crystal-hosts-quaternion        — every vacuum's generated algebra with ℓ lies in a quaternion subalgebra
                                          span{1,u,ℓ,ℓu} (4-dim, proper); poles host ℂ; ℓ-fixing automorphisms act
                                          equivariantly (CDAut, map_N derived; gradeAut / cdLift witnesses).
  PROOF-local-spectrum-at-crystal       — #634 AC4: −L_s² = N(s)·id exactly ⇔ vacuum; N(s) the unique eigenvalue;
                                          first-order alternator expansion off a vacuum.
  PROOF-substrate-hosting-definition    — proofs/QBP/Substrate/Hosting.lean (beekeeper lift 2026-09-07): the hosting
                                          objects and their coherence theorems.
Descriptions state what is NOT claimed (no observer reading — flag 3; no boundary/holography semantics; hosting, not
deriving). Usage: python3 scripts/encode_639_hosting_anchors.py (repo root).
"""

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")
BATCH = "#639-hosting"
STAMP = "2026-09-07T00:00:00Z"
CLEAN = ["propext", "Classical.choice", "Quot.sound"]
MATHLIB = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
BATTERIES = "32dc18cde3684679f3c003de608743b57498c56f"
CH = ("proofs/QBP/Foundations/CrystalHosting.lean", "QBP.Foundations.CrystalHosting.")
HO = ("proofs/QBP/Substrate/Hosting.lean", "QBP.Substrate.Hosting.")

ANCHORS = {
    "PROOF-vacuum-parametrisation": (
        CH,
        "Prop 15 / #634 AC3: a vacuum of the δ-landscape is a + (b₀ + γu)ℓ with a = αu — parametrised, poles included",
        "#639 hosting groundwork (#634 AC3). IsVacuum s := s imaginary ∧ cdLo s · cdHi s = cdHi s · cdLo s, proved equivalent "
        "to alternator-flatness (isVacuum_iff_alternator_flat, via PROOF-alternator-vanishes-iff-commute). "
        "vacuum_iff_parametrised: IsVacuum s ⇔ ∃ u α γ b₀, u imaginary, (N u = 1 ∨ u = 0), cdLo s = α•u, "
        "cdHi s = b₀•1 + γ•u; vacuum_norm_parametrised: N s = α² + γ² + b₀²; the poles u = 0 are s = b₀•ℓ "
        "(vacuum_pole_of_dir_zero). Non-vacuity: sAll_isVacuum, ell_isVacuum; sedWitX_not_isVacuum. The topology "
        "(suspension of ℝP¹ ≅ S²) is NOT formalised — numerical (orbit_space.py, lmaps_check.py). Research-thread "
        "evidence; hosting, not deriving.",
        [
            "vacuum_iff_parametrised",
            "vacuum_norm_parametrised",
            "isVacuum_iff_alternator_flat",
            "vacuum_pole_of_dir_zero",
            "sAll_isVacuum",
            "ell_isVacuum",
            "sedWitX_not_isVacuum",
            "eq_of_halves",
            "split_lo_hi",
        ],
    ),
    "PROOF-crystal-hosts-quaternion": (
        CH,
        "Every crystal generates, with ℓ, a quaternion subalgebra span{1,u,ℓ,ℓu} of 𝕊 (4-dim, proper); ℓ-fixing automorphisms act equivariantly",
        "#639 hosting groundwork (T1/T2). vacuum_hosts_quaternion: for a vacuum s there is a direction u with every word "
        "in {1, s, ℓ} lying in span{1, u, ℓ, ℓu} (InQuatSpan (loOf u)); crystal_quaternion_table: the ℍ relations "
        "(ℓ² = u² = (ℓu)² = −1, uℓ = −ℓu, u(ℓu) = ℓ, (ℓu)u = −ℓ, ℓ(ℓu) = −u); crystal_quatSpan_independent: exactly "
        "4-dimensional; quatSpan_dir_proper: a proper part of 𝕊 for every u; inQuatSpan_ell_right: k = ℓu and k = uℓ "
        "span the same 4-space (orientation is NOT fixed by the landscape — a theory convention). Equivariance: "
        "structure CDAut (linear bijection, map_mul) with map_one / map_re / map_N / map_conj DERIVED (map_re_and_N "
        "via cdAlg_sq_eq + injectivity); aut_map_isVacuum; aut_genByPair; aut_image_quatSpan (onto) and "
        "aut_hosting_equivariant for ℓ-fixing φ (the G₂ side). Witnesses: gradeAut (ℓ ↦ −ℓ, the S₃ side, ≠ id) and "
        "the half-wise lift cdLift with cdLift gradeAut3 ≠ id, cdLift_ell. Aut(𝕊) = G₂ × S₃ is NOT claimed. The "
        'interpretation of this ℍ as "the observer\'s" (DERIV-holographic, flag 3) is NOT claimed.',
        [
            "vacuum_hosts_quaternion",
            "crystal_quaternion_table",
            "crystal_quatSpan_independent",
            "quatSpan_dir_proper",
            "inQuatSpan_of_dir",
            "inQuatSpan_ell_right",
            "aut_hosting_equivariant",
            "aut_image_quatSpan",
            "aut_genByPair",
            "aut_map_isVacuum",
            "aut_alternator_flat",
            "map_re_and_N",
            "map_conj",
            "map_assoc",
            "gradeAut_ell",
            "gradeAut_ne_id",
            "cdLift_ell",
            "cdLift_gradeAut3_ne_id",
            "cdLiftFun_mul",
            "cdLiftFun_bijective",
            "gradeMap_mul",
            "gradeMap_involutive",
        ],
    ),
    "PROOF-local-spectrum-at-crystal": (
        CH,
        "At a crystal −L_s² = N(s)·id exactly, and this characterises crystals; N(s) is the unique eigenvalue; off a crystal the alternator is first order",
        "#639 hosting groundwork / #634 AC4. left_mul_sq_at_vacuum: s(sx) = −N(s)•x for every x at a vacuum; "
        'left_mul_sq_scalar_iff_vacuum: (∀x, s(sx) = −N(s)•x) ⇔ IsVacuum s (for imaginary s) — "not yet crystallised" '
        "is the theorem that the scalar spectrum fails; vacuum_eigenvalue_unique: if −s(sx) = λ•x with x ≠ 0 then "
        "λ = N s; alternator_expansion_off_vacuum: assoc (v + εw) (v + εw) x = ε•laMap v w x + ε²•assoc w w x "
        "(exact, no constant term). The transverse Hessian of V and the {1−δ, 1, 1+δ} multiplicities are NOT "
        "formalised (PROOF-left-mul-sq-alternator scope).",
        [
            "left_mul_sq_at_vacuum",
            "neg_left_mul_sq_at_vacuum",
            "left_mul_sq_scalar_iff_vacuum",
            "vacuum_eigenvalue_unique",
            "alternator_expansion_off_vacuum",
        ],
    ),
    "PROOF-substrate-hosting-definition": (
        HO,
        "The hosting definition (first Substrate/ file): state sphere, potential, universes vs in-flight region, a universe's hosted algebra — and their coherence theorems",
        "#473 AC1 (hosting) / #639; beekeeper lift of the empty-Substrate rule 2026-09-07 (#473 issuecomment-5574256922), "
        "scope AC1-hosting only. Definitions: StateSphere = imaginary unit sedenions; potential s = ‖[cdLo s, cdHi s]‖² "
        "(= V); UniverseSpace = StateSphere ∩ {V = 0}; InFlight = StateSphere ∩ {V > 0}; structure Universe (crystal + "
        "membership); Universe.hosted = the algebra the crystal generates with ℓ. Theorems: potential_eq_zero_iff_isVacuum; "
        "the partition (stateSphere_partition, universeSpace_inFlight_disjoint, universeSpace_union_inFlight); "
        "universe_hosts_quaternion (hosted ⊆ a quaternion subalgebra) and universe_hosted_proper; pole_hosts_complex "
        "(the poles ±ℓ host exactly span{1, ℓ} ≅ ℂ — an equality); local_spectrum_at_universe (s(sx) = −x on the sphere); "
        "hosting_equivariant (ℓ-fixing automorphisms preserve the sphere, vacua and hosted algebras); "
        "inFlight_no_quaternion_closure ⇔ mem_universeSpace_iff_complex_structure (the two regions separated by an "
        "iff); non-vacuity: universeSpace_nonpole (not only the ℂ-poles), inFlight_nonempty, universeSpace_ne_stateSphere. "
        "NOT in this file (owners named in its §11): the initial ensemble (beekeeper ruling, horn 1), the rule/flow (#635), "
        "the Agda S³ transport (#639 (c)), S₃-side covariance (#639 (e)), the boundary of a universe, the pointless "
        "in-flight description (#636/#639), our universe's b₀ (#637). Hosts; does not derive (KILLED-locale-forcing-route). "
        "No observer reading (flag 3).",
        [
            "potential_eq_zero_iff_isVacuum",
            "potential_descends",
            "stateSphere_partition",
            "universeSpace_inFlight_disjoint",
            "universeSpace_union_inFlight",
            "mem_universeSpace_iff_potential",
            "mem_inFlight_iff_potential",
            "universe_hosts_quaternion",
            "universe_hosted_proper",
            "universe_quaternion_table",
            "smul_ell_hosted_eq_complex",
            "pole_hosts_complex",
            "polePlus_hosted_eq_complex",
            "local_spectrum_at_universe",
            "local_spectrum_at_universe_smul",
            "universe_eigenvalue_unique",
            "hosting_equivariant",
            "stateSphere_map_mem",
            "inFlight_no_quaternion_closure",
            "mem_universeSpace_iff_complex_structure",
            "universeSpace_nonempty",
            "universeSpace_nonpole",
            "inFlight_nonempty",
            "universeSpace_ne_stateSphere",
            "normalise_mem_stateSphere",
            "isVacuum_smul_iff",
        ],
    ),
}


def verification(pf):
    return {
        "toolchain": "leanprover/lean4:v4.30.0",
        "libraries": {
            "mathlib": {"ref": MATHLIB, "sha": MATHLIB},
            "batteries": {"ref": "main", "sha": BATTERIES},
        },
        "verified_at": STAMP,
        "verifier": f"lake build + #print axioms on {pf} (qbp-oppenheimer + lean-prover agent, #639 hosting groundwork, 2026-09-07); pending cth §I4",
        "result": "verified",
        "axiom_closure": CLEAN,
    }


def main():
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
        src = open(os.path.join(ROOT, pf), encoding="utf-8").read()
        missing = [
            w
            for w in wits
            if f"theorem {w} " not in src
            and f"theorem {w}\n" not in src
            and f"theorem {w} :" not in src
        ]
        if missing:
            sys.exit(f"{aid}: witnesses not found in {pf}: {missing}")
    ledger = json.load(open(LEDGER, encoding="utf-8"))
    anchors = ledger["anchors"]
    anchors[:] = [a for a in anchors if a.get("foundation_batch") != BATCH]
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
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
                "proof_file": pf,
                "sorry_count": 0,
                "proof_state": "verified",
                "lean_theorem": ns + wits[0],
                "lean_companion_theorems": [ns + w for w in wits[1:]],
                "theorems": [{"name": w, "status": "verified"} for w in wits],
                "foundation_batch": BATCH,
                "last_tested_at": STAMP,
                "verification": verification(pf),
            }
        )
    json.dump(ledger, open(LEDGER, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    open(LEDGER, "a", encoding="utf-8").write("\n")
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    entries = [e for e in manifest["entries"] if e.get("declared_by") != BATCH]
    for aid, ((pf, ns), name, desc, wits) in ANCHORS.items():
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
