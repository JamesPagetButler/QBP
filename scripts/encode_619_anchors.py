#!/usr/bin/env python3
"""#619 orphan-recovery encoder — programmatically append the 35 new + fold/update
2 existing CTH anchors that recover already-proven Lean work into the ledger, plus the
matching C1/C2 manifest entries. Idempotent: re-running removes any prior #619 anchors
(foundation_batch=="#619" among the new ids, plus the tracked updates) before re-adding.

Inputs (scratchpad, produced by resolve2.py + the #print axioms capture):
  witmap.json           deliverable -> [{bare,qualified,file,module,proof_file}]
  per_anchor_closure.json deliverable -> captured axiom_closure (union over witnesses)

Evidence bar (C3-FULL): every witness closure was captured via `#print axioms` through a
scratch importer under `run-bounded 10G 400 lake env lean`; all 202 ⊆ {propext,
Classical.choice, Quot.sound}; every proof_file is source-hole-free. See the #619 report.
"""

import json, os

ROOT = "/home/prime/Documents/QBP/.claude/worktrees/agent-a8618428d18c8f79d"
SCRATCH = "/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad"
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")

WM = json.load(open(os.path.join(SCRATCH, "witmap.json")))
CLOS = json.load(open(os.path.join(SCRATCH, "per_anchor_closure.json")))

VERIFIER = (
    "lake build + #print axioms, leanprover/lean4:v4.30.0 "
    "(qbp-oppenheimer, #619 orphan-anchoring); pending cth §I4"
)
SHA = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
STAMP = "2026-09-03T00:00:00Z"


def verification(closure):
    return {
        "toolchain": "leanprover/lean4:v4.30.0",
        "libraries": {"mathlib": {"ref": SHA, "sha": SHA}},
        "verified_at": STAMP,
        "verifier": VERIFIER,
        "result": "verified",
        "axiom_closure": closure,
    }


# deliverable -> (name, provenance_kind, description). Order of witnesses in witmap sets
# the PRIMARY (first) = lean_theorem; the rest = lean_companion_theorems.
META = {
    "PROOF-ops-order-ladder": (
        "Operations matrix: linear-order breakdown ℝ→𝕊",
        "proof",
        "#474 operations matrix (order row): ℂ/ℍ/𝕆/𝕊 admit no compatible linear order (the tower loses orderability past ℝ). Kernel-verified counterexamples in Breakdown.lean. See also PROOF-normed-division-tower-existence, PROOF-42zd.",
    ),
    "PROOF-ops-commutativity-ladder": (
        "Operations matrix: commutativity ✓ℝℂ ✗ℍ𝕆𝕊",
        "proof",
        "#474 operations matrix (commutativity row): mul is commutative for ℝ,ℂ (TowerLaws) and fails for ℍ,𝕆,𝕊 (witnessed counterexamples, Breakdown). Kernel-verified.",
    ),
    "PROOF-ops-associativity-ladder": (
        "Operations matrix: associativity ✓ℝℂℍ ✗𝕆𝕊",
        "proof",
        "#474 operations matrix (associativity row): mul is associative for ℝ,ℂ,ℍ (TowerLaws) and fails for 𝕆,𝕊 (Breakdown). octonion_not_associative overlaps the fact anchored as octonion_non_associative in PROOF-fano-genesis (distinct theorem/file) — see also PROOF-fano-genesis. Kernel-verified.",
    ),
    "PROOF-ops-alternativity-ladder": (
        "Operations matrix: alternativity ✓ℝℂℍ𝕆 ✗𝕊",
        "proof",
        "#474 operations matrix (alternativity row): the algebra is alternative through 𝕆 (TowerLaws + CDLifting.octonion_alternative) and first fails at 𝕊 (Breakdown.sedenion_not_alternative). Kernel-verified.",
    ),
    "PROOF-ops-norm-composition-ladder": (
        "Operations matrix: norm composition (Hurwitz) ✓ℝℂℍ𝕆 ✗𝕊",
        "proof",
        "#474 operations matrix (norm-composition / Hurwitz row): N(xy)=N(x)N(y) holds through 𝕆 (TowerLaws + OctonionLaws.octonion_norm_composition) and fails at 𝕊 (Breakdown.sedenion_norm_not_multiplicative). This is the per-level ℝ/ℂ/ℍ/𝕆 cell view; the tower-existence pair octonion_norm_multiplicative/sedenion_not_composition is anchored separately — see also PROOF-normed-division-tower-existence (distinct theorems/files). Kernel-verified. FLAG for cth: intentional content overlap, cross-referenced not suppressed.",
    ),
    "PROOF-ops-division-ladder": (
        "Operations matrix: division algebra ✓ℝℂℍ𝕆 ✗𝕊",
        "proof",
        "#474 operations matrix (division row): ℝ,ℂ,ℍ are division algebras (TowerLaws); 𝕊 has zero divisors (Breakdown.sedenion_zero_divisors). See also PROOF-42zd (the 42-plane count of 𝕊 zero divisors) and PROOF-normed-division-tower-existence. Kernel-verified.",
    ),
    "PROOF-ops-flexibility-ladder": (
        "Operations matrix: flexibility ✓ all levels",
        "proof",
        "#474 operations matrix (flexibility row): x(yx)=(xy)x holds at every level ℝ,ℂ,ℍ,𝕆,𝕊 (TowerLaws + OctonionLaws). Flexibility is the one identity that survives the whole Cayley-Dickson tower. Kernel-verified.",
    ),
    "PROOF-sedenion-42-plane-structure": None,  # folded into PROOF-42zd, no new anchor
    "PROOF-sedenion-zero-divisor-witnesses": (
        "Seven witnessed failing sedenion hyperplanes",
        "proof",
        "Seven explicit basis-normal sedenion hyperplanes (normal9..15) carrying zero-divisor pairs — the witnessed failures behind the 8/15 alternative-hyperplane split. Kernel-verified (SedenionOctonionCount.lean). See also PROOF-42zd, PROOF-sedenion-alternative-hyperplane-count.",
    ),
    "PROOF-octonion-moufang": (
        "Octonion Moufang identities (left/right/middle)",
        "proof",
        "The three Moufang identities hold in 𝕆 — the alternative-algebra substitute for associativity. Kernel-verified (OctonionLaws.lean).",
    ),
    "PROOF-power-associativity": (
        "Power-associativity of 𝕆 and 𝕊 (deg 3 and 4)",
        "proof",
        "𝕆 and 𝕊 are power-associative at degrees 3 and 4: x(xx)=(xx)x and the degree-4 associations agree, even though 𝕊 is neither alternative nor a division algebra. Kernel-verified (OctonionLaws.lean).",
    ),
    "PROOF-octonion-cross-product": (
        "7D / G₂ octonion cross product laws",
        "proof",
        "The 7-dimensional cross product from Im 𝕆 (the G₂ structure): reCoord vanishing, antisymmetry, self-annihilation, orthogonality (both sides, ℍ and 𝕆), the norm identity, and the non-existence of a composition cross product on 𝕊. Kernel-verified (CrossProduct.lean). Cross-ref Breakdown.sedenion_norm_not_multiplicative.",
    ),
    "PROOF-artin-theorem": (
        "Artin's theorem for octonions",
        "proof",
        "Artin: any subalgebra of 𝕆 generated by two elements is associative (octonion_artin), with the associativity and generation witnesses. Kernel-verified (Artin.lean).",
    ),
    "PROOF-cd-product-formula": (
        "General-n Cayley-Dickson product formula",
        "proof",
        "The general-level Cayley-Dickson basis product e_i*e_j (mulCoeff), its basis expansion, coefficient properties, and the square law. The computational core of the CD construction. Kernel-verified (CDAlg.lean).",
    ),
    "PROOF-cd-structure-constant-tables": (
        "Cayley-Dickson structure-constant tables (F3/F4) + orientation",
        "proof",
        "The level-3/4 CD structure-constant tables and their Fano-orientation provenance: mulCoeff_three_eq_fano, mulCoeff_four_eq_sgnTable (CDAlg), and the FanoOrientationF3 pins (fanoTableF4_eq_cayleyDickson, cayleyDickson8_sq_neg_one, cayleyDickson8_alternative_on_basis, fanoTriples_oriented, archiveTable_disagrees_cd). cayleyDickson8_sq_neg_one is a distinct theorem from PROOF-fano-genesis.imaginary_units_square_neg_one — see also PROOF-fano-genesis. Kernel-verified.",
    ),
    "PROOF-cd-associativity-level2": (
        "Cayley-Dickson level-2 (ℍ) associativity over any CommRing",
        "proof",
        "CDAlg R 2 (the quaternion level) is associative over any commutative ring, with the unit laws. Kernel-verified (CDBridge.lean).",
    ),
    "PROOF-cd-associator-formula": (
        "General-level Cayley-Dickson associator formula",
        "proof",
        "The closed-form associator for the Cayley-Dickson doubling at general level (assoc_e). Kernel-verified (CDLifting.lean).",
    ),
    "PROOF-octonion-sedenion-exp-log": (
        "exp/log on 𝕆 and 𝕊: Euler, one-parameter group, inverses",
        "proof",
        "The exponential/logarithm theory on 𝕆 and 𝕊: Euler's formula on a unit axis, the one-parameter group law, exp(-x)exp(x)=1, the norm law N(exp x), and exp/log inverse pairs, plus the ℍ reduction and the per-algebra 𝕆/𝕊 cells. Kernel-verified (Exp.lean).",
    ),
    "PROOF-norm-form-bilinear": (
        "Norm form and polar bilinear form (Euclidean signature)",
        "proof",
        "The polar/bilinear form of the CD norm: bil = reCoord(x * conj y), symmetry, the 𝕆/𝕊 bilinear forms, non-negativity, N(x)=0 iff x=0 (Euclidean signature, D10), and composition holding for 𝕆 but not 𝕊. Kernel-verified (NormForm.lean). Cross-ref PROOF-ops-norm-composition-ladder.",
    ),
    "PROOF-sedenion-alternative-hyperplane-count": (
        "O1a: 8 of 15 sedenion basis hyperplanes are alternative",
        "proof",
        "Exactly 8 of the 15 basis-normal sedenion hyperplanes are alternative (alternative_hyperplane_count_eq_eight), with the pass/fail discriminators. Kernel-verified (SedenionOctonionCount.lean). See also PROOF-sedenion-zero-divisor-witnesses.",
    ),
    "PROOF-octonion-32dim-alternative-count": (
        "D3: 50 of 155 alternative subspaces; 42=35+7, 50=8+42",
        "proof",
        "The 32-dimensional (𝕊) alternative-subspace count k(5)=50 of 155, with the arithmetic bridges 42=35+7 and 50=8+42 and the base-copies / crossing discriminator lemmas. Kernel-verified (Octonion32Count.lean).",
    ),
    "PROOF-su2-lie": None,  # UPDATE to existing anchor
    "PROOF-bpm-si-round-trip": (
        "BPM↔SI conversion round-trip invertibility",
        "proof",
        "Position and energy convert BPM↔SI invertibly (round-trip identities) — a dimensionless correctness fact about the scale-factor maps, independent of the chosen numeric constants. Kernel-verified (ScaleFactors.lean).",
    ),
    "PROOF-doubleslit-quaternion-algebra": (
        "Double-slit quaternion algebra identities",
        "proof",
        "Pure quaternion algebra behind the double-slit model: qJ², j·complex commutation, the coupling decomposition and its cancellation, and normSq of the symplectic form. Model-independent ℝ/ℍ identities. Kernel-verified (DoubleSlit.lean).",
    ),
    "PROOF-doubleslit-visibility-bounds": (
        "Double-slit visibility real-analysis bounds 0≤V≤1",
        "proof",
        "Real-analysis bounds on the double-slit visibility and quaternionic fraction: 0≤η≤1, 0≤V≤1, the endpoint values, and monotone correlation. Bounds on the defined quantities, not a physics claim. Kernel-verified (DoubleSlit.lean).",
    ),
    "PROOF-fraunhofer-optics": (
        "Fraunhofer diffraction intensity facts",
        "proof",
        "Diffraction-intensity facts for the Fraunhofer model: value at maxima/minima, fringe-spacing linearity in λ and L and inverse in d, and the full single-slit envelope factorisation with its bounds. Real-analysis facts about the defined intensity. Kernel-verified (Fraunhofer.lean).",
    ),
    "DERIV-sterngerlach-qbp": (
        "Stern-Gerlach x-in-z predictions (QBP Born ansatz)",
        "derivation",
        "GATING PREMISE: the QBP Born/measurement ansatz (probUp/expectationValue defs). Given that ansatz, an x-prepared spin measured along z gives ⟨x⟩=0 and P(up)=P(down)=1/2. True GIVEN the QBP ansatz — NOT a model-independent result. Lean backbone kernel-verified (SternGerlach.lean).",
    ),
    "DERIV-angle-dependent-qbp": (
        "Angle-dependent spin predictions (QBP ansatz)",
        "derivation",
        "GATING PREMISE: the QBP measurement ansatz. Given it, the angle-dependent expectation and P(up)=cos²(θ/2), P(down)=sin²(θ/2), with the θ=0,π,π/2 special cases. True GIVEN the QBP ansatz, not model-independent. Lean backbone kernel-verified (AngleDependent.lean).",
    ),
    "DERIV-general3d-qbp": (
        "General-3D spin predictions (QBP ansatz)",
        "derivation",
        "GATING PREMISE: the QBP measurement ansatz. Given it, the general-direction expectation and probabilities, same-direction and axis special cases, and azimuthal invariance. True GIVEN the QBP ansatz, not model-independent. Lean backbone kernel-verified (General3D.lean).",
    ),
    "DERIV-doubleslit-visibility-model": (
        "Double-slit visibility law V=1−η (Model A)",
        "derivation",
        "GATING PREMISE: Model A, visibility = 1 − quaternionic-fraction. Given that model, V = 1−η and V is antitone in the background. True GIVEN Model A; the model choice itself is open (#387). Lean backbone kernel-verified (DoubleSlit.lean). See also PROOF-doubleslit-visibility-bounds (model-independent bounds).",
    ),
    "DERIV-measurement-ansatz-basic": (
        "QBP measurement ansatz basic identities",
        "derivation",
        "GATING PREMISE: the QBP measurement ansatz (probUp / expectationValue definitions). Given the ansatz, orthogonal expectation is 0 and P(up)=1/2. True GIVEN the ansatz definitions, not a model-independent theorem. Lean backbone kernel-verified (Basic.lean).",
    ),
    "DERIV-code-si-constants": (
        "BPM code / SI constant positivity facts",
        "derivation",
        "GATING PREMISE: the chosen BPM code-unit and SI numeric constants. Given those constant choices, v_z=40 and the positivity of the SI/code constants hold. True GIVEN the chosen constants (definitional), not physical predictions. Lean backbone kernel-verified (Constants.lean).",
    ),
    "DERIV-kitaev-model": (
        "Kitaev honeycomb / α-RuCl₃ model facts (chosen model)",
        "derivation",
        "GATING PREMISE: the Kitaev honeycomb Hamiltonian plus α-RuCl₃ material constants. Given that model, plaquette ℤ₂ flux, triple-product orderings, Clifford anticommutation and collapse to quaternions, non-abelian braiding, the Ru/Cl screening and SOC/j_eff regime checks hold. True GIVEN the Kitaev model + constants, not a model-independent claim. K7/K8 numerology excluded as auxiliary. Lean backbone kernel-verified (Kitaev.lean).",
    ),
    "DERIV-graphene-model": (
        "Graphene honeycomb / moiré model facts (chosen model)",
        "derivation",
        "GATING PREMISE: the honeycomb / moiré tight-binding model. Given it, honeycomb ℤ₃ cyclicity and chirality, C2z momentum reversal, Dirac helicity, moiré fragile topology, and α≈ 1/√3 hold. True GIVEN the model, not model-independent. mott_from_hessian (G11) left as auxiliary (file-anchored). Lean backbone kernel-verified (Graphene.lean).",
    ),
    "DERIV-bi2se3-ti": (
        "Bi₂Se₃ topological-insulator model facts (measured constants)",
        "derivation",
        "GATING PREMISE: Bi₂Se₃ measured material constants. Given them, Bi/Se screening validity, the Slater checks, and band inversion hold. True GIVEN the measured constants, not a first-principles prediction. Lean backbone kernel-verified (Bi2Se3.lean).",
    ),
    "DERIV-crystallisation-spectral-moments": (
        "Crystallisation spectral-moment law (chosen model)",
        "derivation",
        "GATING PREMISE: the spectral-action moment law. Given it, the moment-scaling hierarchy, convergence ordering, variation correlation and growth enhancement hold. True GIVEN the spectral-action model, not model-independent. Lean backbone kernel-verified (Crystallisation.lean).",
    ),
    "DERIV-quaternion-physics-kramers": (
        "Kramers degeneracy from quaternion structure (physical identification)",
        "derivation",
        "GATING PREMISE: the physical identification of the quaternionic structure with time-reversal. Given it, Kramers orthogonality and degeneracy and the eigenspace gauge match hold. True GIVEN that identification, not model-independent. The quaternion-algebra basics used here are SEE-ALSO the Foundations anchors (PROOF-ops-* ladders, PROOF-42zd) — not re-anchored. Lean backbone kernel-verified (Quaternion.lean).",
    ),
}


def build_anchor(deliv):
    rows = WM[deliv]
    name, kind, desc = META[deliv]
    primary = rows[0]
    proof_file = primary["proof_file"]  # relative to repo root, e.g. proofs/...
    companions = [r["qualified"] for r in rows[1:]]
    thms = [{"name": r["bare"], "status": "verified"} for r in rows]
    a = {
        "id": deliv,
        "name": name,
        "tier": 1,
        "provenance": "T",
        "status": "coherent",
        "description": desc,
        "prediction_chain": [],
        "provenance_kind": kind,
        "proof_system": "lean4",
        "proof_language": "lean4",
        "proof_file": proof_file,
        "sorry_count": 0,
        "proof_state": "verified",
        "lean_theorem": primary["qualified"],
        "lean_companion_theorems": companions,
        "theorems": thms,
        "foundation_batch": "#619",
        "last_tested_at": STAMP,
        "verification": verification(CLOS[deliv]),
    }
    return a


def main():
    ledger = json.load(open(LEDGER, encoding="utf-8"))
    anchors = ledger["anchors"]
    by_id = {a["id"]: a for a in anchors}

    new_ids = [d for d in WM if META.get(d) is not None]

    # idempotency: drop previously-added #619 new anchors
    anchors[:] = [
        a
        for a in anchors
        if not (a.get("foundation_batch") == "#619" and a["id"] in new_ids)
    ]
    by_id = {a["id"]: a for a in anchors}

    # 1) append the new anchors
    added = []
    for deliv in WM:
        if META.get(deliv) is None:
            continue
        anchors.append(build_anchor(deliv))
        added.append(deliv)

    # 2) fold deliverable 8 into PROOF-42zd (companions + theorems[] + description)
    d8 = WM["PROOF-sedenion-42-plane-structure"]
    a42 = by_id["PROOF-42zd"]
    comp = a42.get("lean_companion_theorems", [])
    existing_comp = set(comp)
    for r in d8:
        if r["qualified"] not in existing_comp:
            comp.append(r["qualified"])
    a42["lean_companion_theorems"] = comp
    thms = a42.get("theorems", [])
    have = {t["name"] for t in thms if isinstance(t, dict)}
    for r in d8:
        if r["bare"] not in have:
            thms.append({"name": r["bare"], "status": "verified"})
    a42["theorems"] = thms
    if "distinct Breakdown/CDAlg construction" not in a42["description"]:
        a42["description"] += (
            " #619: the same 42 planes are also witnessed by a distinct "
            "Breakdown/CDAlg construction — sedenion_basis_zero_divisor_plane_count_eq_42 and "
            "prodIsZero_iff_cdAlg_mul_eq_zero (proofs/QBP/Foundations/Breakdown.lean), folded here "
            "as companions rather than a separate anchor."
        )

    # 3) update PROOF-su2-lie: theory -> proof, add the two witnesses + evidence
    su2 = by_id["PROOF-su2-lie"]
    rows22 = WM["PROOF-su2-lie"]
    su2["provenance_kind"] = "proof"
    su2["proof_system"] = "lean4"
    su2["proof_language"] = "lean4"
    su2["proof_file"] = rows22[0]["proof_file"]
    su2["sorry_count"] = 0
    su2["proof_state"] = "verified"
    su2["lean_theorem"] = rows22[0]["qualified"]
    su2["lean_companion_theorems"] = [r["qualified"] for r in rows22[1:]]
    su2["theorems"] = [{"name": r["bare"], "status": "verified"} for r in rows22]
    su2["foundation_batch"] = "#619"
    su2["last_tested_at"] = STAMP
    su2["verification"] = verification(CLOS["PROOF-su2-lie"])
    su2["description"] = (
        "Lean Q3-Q4: [eᵢ,eⱼ]=2εᵢⱼₖeₖ verified for all cyclic permutations "
        "(imH_structure_constants), and the Casimir e₁²+e₂²+e₃²=−3e₀ verified (imH_casimir, "
        "LieAlgebraIso.lean). The Hessian λ=8 eigenspace IS the su(2) algebra. #619: the Casimir "
        "over-claim (previously asserted with no witness) is now witnessed and the anchor promoted "
        "theory→proof with a captured axiom_closure."
    )

    json.dump(ledger, open(LEDGER, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    open(LEDGER, "a", encoding="utf-8").write("\n")

    # 4) manifest entries: one per new anchor + PROOF-su2-lie. Witnesses = ONLY those whose
    #    short-name lives in the anchor's proof_file (C3 checks each against that one file).
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    # idempotency: strip any prior #619 entries, then append fresh.
    entries = [e for e in manifest["entries"] if e.get("declared_by") != "#619"]
    n_added = 0
    for deliv in list(added) + ["PROOF-su2-lie"]:
        rows = WM[deliv]
        pf = rows[0]["proof_file"]
        wit = [r["qualified"] for r in rows if r["proof_file"] == pf]
        entries.append(
            {
                "anchor_id": deliv,
                "proof_system": "lean4",
                "declared_by": "#619",
                "witnesses": wit,
            }
        )
        n_added += 1
    manifest["entries"] = entries
    json.dump(
        manifest, open(MANIFEST, "w", encoding="utf-8"), ensure_ascii=False, indent=2
    )
    open(MANIFEST, "a", encoding="utf-8").write("\n")

    print(f"new anchors added: {len(added)}")
    print(f"folded into PROOF-42zd: {[r['bare'] for r in d8]}")
    print(f"updated PROOF-su2-lie -> proof")
    print(f"manifest entries now: {len(entries)} (added {n_added} #619)")


if __name__ == "__main__":
    main()
