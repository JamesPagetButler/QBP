# Migration report: archive/cth-inventory/confluent-trust-inventory-v5_3.json → archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json

**Generated:** 2026-05-29T18:21:48 UTC by cth migrate v0.3-impl-2

## Summary

- Total anchors: 141
- Mechanically translated: 141
- Decisions applied (from --decisions): 33
- Decisions still needed: 74
- Warnings: 10

## Decisions still needed

The following anchors carry `provenance: "T"` (theoretical) and need
human classification as either `theory` (programme-internal argument)
or `theory-external` (external published theorem invoked as proof).

Create a decisions JSON file and pass it via `--decisions <path>`:

```json
{
  "anchors": [
    { "id": "PRED-gw-em", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-lambda", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-no-gup", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-born-exact", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "MEAS-mult-threshold", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "MEAS-proton-stable", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-proton-decay-null", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-revival-exact", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-gamma-universality", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "OBS-cmb-314", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-quat-closure", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-su2-lie", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-kramers", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-hurwitz-quat", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-z2-cover", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "OBS-tenfold-division", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PROOF-z3-cyclic", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-c2zt-square", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-helicity-obstruction", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "OBS-mott-parallel", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-plaquette-z2", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-clifford-majorana", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-nonabelian-braid", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-majorana-charge", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-bond-complete", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "MEAS-kitaev-z2gauge", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "OBS-thermal-hall-half", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-no-dm-particle", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "FLAG-inflation", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PARTIAL-qgp", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-correlated-alpha-G", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "FLAG-profile-underdetermined", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "OBS-finsler-gravity", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "OBS-big-crunch", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-conformal-profile", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-holographic-boundary-gravity", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-H-equals-Mdot-over-M", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-cosmic-birefringence", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "INSIGHT-info-paradox-resolution", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-koide-phase-2-over-9", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-wolfenstein-A-sqrt-Q", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-ckm-cp-phase-arctan-sqrt7", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "REF-jido-eta-prime-chiral-2012", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-eta-prime-mass-shift-1-over-24", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "Q27-TOV-limit-from-Fano", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-TOV-limit-sqrt-7-over-3", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-chiral-restoration-3rho0", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-conformal-sound-speed-1-over-3", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-peak-sound-speed-Q", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "INSIGHT-iron-handoff-nuclear-to-magnetic", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-proton-fraction-1-over-8", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-magnetar-energy-fraction-1-over-3", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "INSIGHT-urca-threshold-dim-O", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-urca-onset-3rho0", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-interpolation-function-derived", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PROOF-M-proportional-to-a", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-lambda-as-cross-term", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-w-not-minus-1", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "INSIGHT-entropy-cone-division-algebra-inversion", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-fano-associativity-7beam", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-division-algebra-entropy-cone-mapping", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "INSIGHT-branch-A-hypergraph-boundary", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "INSIGHT-bcc-iron-fano-cube", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "INSIGHT-fano-cube-universal-compute-cell", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PROOF-beta-function-3-times-7", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "Q28-alpha-GUT-from-stabiliser", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "WISDOM-schema-vs-instance", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "PRED-f4-zero-vacuum-energy", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "WISDOM-003-there-is-only-f-u", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-profile-function-f0-f2-ratio", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "PRED-inv-alpha-GUT-16pi", "provenance_kind": "theory", "theory_citation": "" },
    { "id": "CONV-spectral-entropy-zeta", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "CONV-cd-tower-in-zeta-moments", "provenance_kind": "theory-external", "theory_citation": "" },
    { "id": "KILLED-f4-info-theoretic-justification", "provenance_kind": "theory-external", "theory_citation": "" }
  ]
}
```

### PRED-gw-em

- **Name:** GW-EM temporal correlation pulse-for-pulse
- **Description:** For consumption events, GW and EM signals share internal temporal structure because both are projections of the same seam formation dynamics.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-lambda

- **Name:** Cosmological constant from ZD basin geometry
- **Description:** Lambda proportional to ZD access rate x seam fluctuation frequency x seams per cell. Should give ~10^-122 in Planck units.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-no-gup

- **Name:** No generalised uncertainty principle corrections
- **Description:** hbar is fixed per Gamma-step, not a running parameter. No Planck-scale modifications to uncertainty principle.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-born-exact

- **Name:** Born rule holds exactly at all energies
- **Description:** P=|psi|^2 is a property of the H norm, not of the physics. No regime within our universe should show violations.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### MEAS-mult-threshold

- **Name:** Hessian multiplicities predict threshold correction pattern
- **Description:** Multiplicities (4,8,4) predict delta_1 = delta_3 (since mult(4)=mult(12)=4). Verified to 9.4%. One-parameter fit chi2=0.006, all other models chi2>7. First test of Hessian MULTIPLICITIES against ex...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### MEAS-proton-stable

- **Name:** Proton effectively stable (NCG Pati-Salam forbids d=5,6 decay)
- **Description:** NCG Pati-Salam (Chamseddine-Connes-van Suijlekom 2013) forbids d=6 proton decay (no diquark vertex in SU(4) leptoquark) and d=5 decay (NCG forbids diquark scalars, Aydemir et al. 2018). First allow...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

### PRED-proton-decay-null

- **Name:** Hyper-K and DUNE will NOT observe proton decay
- **Description:** NCG Pati-Salam predicts proton is effectively stable. Hyper-K (2027+) will improve bounds by ~10x. DUNE sensitive to p->K+nubar channel. QBP predicts null result in BOTH.
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-revival-exact

- **Name:** Rotational quantum revival time exact (no collapse)
- **Description:** T_rev = 2*pi*I/hbar exact at all mass scales. Born rule P=|psi|^2 from Hurwitz (unique quaternion norm). No objective collapse. Distinguishable from CSL (fidelity ~ m^-2) and Diosi-Penrose (fidelit...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-gamma-universality

- **Name:** Gamma-reparameterisation reduces decoherence variance
- **Description:** Cooling curves from 6 different nanorotors (dumbbells, trimers, clusters) should show REDUCED variance when parameterised by Gamma(t) instead of clock time t. Test statistic R = Var(Gamma)/Var(t) p...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### OBS-cmb-314

- **Name:** G2 ratio 3/14 = 0.214 vs Planck birefringence 0.342 (1.4 sigma)
- **Description:** The ratio of parity-violating broken G2 generators to total (3/14 = 0.214) is within 1.4 sigma of the Planck cosmic birefringence angle (0.342 +/- 0.094 degrees). No other parameter-free algebraic ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-quat-closure

- **Name:** Quaternion subalgebra ℍ ⊂ 𝕊 is closed + Hamilton table verified
- **Description:** Lean Q1-Q2: {e₀,e₁,e₂,e₃} closed under sedenion multiplication. Hamilton's ij=k, jk=i, ki=j verified against multiplication table. Machine-verified, zero sorry.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-su2-lie

- **Name:** su(2) Lie algebra from imaginary quaternion commutators
- **Description:** Lean Q3-Q4: [eᵢ,eⱼ] = 2εᵢⱼₖeₖ verified for all cyclic permutations. Casimir e₁²+e₂²+e₃² = -3e₀ verified. The Hessian λ=8 eigenspace IS the su(2) algebra.
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-kramers

- **Name:** Kramers theorem: T²=-1, orthogonality, degeneracy (algebraic)
- **Description:** Lean Q5-Q7: Pure imaginary unit quaternions square to -1 (T²=-1). ⟨ψ|Tψ⟩ = 0 for all basis states and all T choices (orthogonality). Tψ ≠ ψ for all states (degeneracy). This is the algeb...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-hurwitz-quat

- **Name:** Hurwitz norm multiplicativity in ℍ (Berry phase = π, Born rule)
- **Description:** Lean Q8: |ab|² = |a|²|b|² verified for ALL quaternion basis sums. This is the algebraic fact underlying both the Born rule (P=|ψ|²) and the Berry phase (π) of topological surface states. Q9 p...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-z2-cover

- **Name:** SU(2)/Z₂ = SO(3) double cover → Z₂ topological invariant
- **Description:** Lean Q10: Conjugation by u and -u produce the same inner automorphism. This is the Z₂ kernel of SU(2)→SO(3), which is the topological invariant classifying band insulators. Combined with Kramer...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### OBS-tenfold-division

- **Name:** Altland-Zirnbauer tenfold way maps to division algebra hierarchy
- **Description:** The 10 symmetry classes of free-fermion topological phases map to ℝ (T²=+1: classes AI, D, BDI), ℂ (no T or C: classes A, AIII), and ℍ (T²=-1: classes AII, C, CII, DIII, CI). This is the SA...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PROOF-z3-cyclic

- **Name:** Honeycomb Z₃ cyclic symmetry from quaternion product e₁e₂=e₃
- **Description:** Lean G1-G3: The three imaginary quaternion units satisfy e₁e₂=e₃, e₂e₃=e₁, e₃e₁=e₂ (Z₃ cycle) and anti-cyclic products give opposite signs (Z₂ chirality). This Z₃×Z₂ = th...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-c2zt-square

- **Name:** (C₂zT)² = +1 distinguishes fragile from robust topology
- **Description:** Lean G6-G7: C₂z²=-1 (spinor, from e₁²=-1) × T²=-1 gives (C₂zT)²=+1. This squares to PLUS one, not minus one like pure T. Consequence: MATBG has fragile Z topology (real class AI), Bi₂S...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-helicity-obstruction

- **Name:** Nonzero total helicity → Wannier obstruction (fragile topology)
- **Description:** Lean G8-G9: Dirac cone helicity = sign of quaternion cyclic product. K valley: sign(e₁e₂)=+1, K' valley: sign(e₂e₁)=-1. Two same-valley cones in moiré BZ: total helicity = +1+1 = 2 ≠ 0 �...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### OBS-mott-parallel

- **Name:** MATBG and REBCO share Mott physics structure (U/t from same Hessian)
- **Description:** Both MATBG and REBCO are Mott systems where U/t>>1 produces correlated insulators and SC upon doping. U derives from α_em (Hessian λ=4, U(1)), t derives from orbital overlap (λ=8, SU(2)). Both c...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-plaquette-z2

- **Name:** Quaternion triple product e₁e₂e₃ = -e₀ → Z₂ gauge structure
- **Description:** Lean K1-K3: The triple product e₁e₂e₃ = -e₀ is the Kitaev plaquette flux W_p = σ_xσ_yσ_z. W_p² = +1 → eigenvalues ±1 → Z₂ gauge group. All six orderings yield ±e₀ with signs d...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-clifford-majorana

- **Name:** Clifford Cl(0,3) anticommutation = Majorana fermion algebra
- **Description:** Lean K4-K5: {eᵢ,eⱼ} = -2δᵢⱼe₀ verified for all 9 pairs. Bivectors = vectors (e₁e₂=e₃, e₂e₃=e₁, e₃e₁=e₂) proves Cl(0,3) ≅ ℍ⊕ℍ. The Kitaev Majorana decomposition ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-nonabelian-braid

- **Name:** Non-abelian anyons from quaternion non-commutativity
- **Description:** Lean K6: e₁e₂ = +e₃ ≠ e₂e₁ = -e₃ verified for all three pairs. Braiding Kitaev anyons in opposite orders gives different results because quaternion multiplication doesn't commute. The...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-majorana-charge

- **Name:** Majorana central charge c=1/2 from dim(ℝ)/dim(ℂ)
- **Description:** Lean K7: dim(ℝ)=1, dim(ℂ)=2, ratio=1/2. A Majorana fermion (real, 1 DOF per mode) has half the degrees of freedom of a Dirac fermion (complex, 2 DOF). The half-quantized thermal Hall conductivi...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-bond-complete

- **Name:** Three Kitaev bond types exhaust spin-1/2 observables (dim Im ℍ = 3)
- **Description:** Lean K8: dim(Im ℍ) = 3 = number of independent spin-1/2 operators = number of Kitaev bond types. The Kitaev model is the MOST GENERAL bond-dependent Ising interaction on a honeycomb — there is ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### MEAS-kitaev-z2gauge

- **Name:** Kitaev model Z₂ gauge structure confirmed (exact solution)
- **Description:** The Kitaev honeycomb model is exactly solvable (Kitaev 2006). The exact solution confirms: Z₂ gauge structure with conserved plaquette flux W_p = ±1, Majorana fermion excitations, and non-abelia...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

### OBS-thermal-hall-half

- **Name:** Half-quantized thermal Hall = dim(ℝ)/dim(ℂ) = 1/2 (Majorana edge)
- **Description:** The half-quantized thermal Hall conductivity κ_xy/T = (π²k_B²/6ℏ)×(1/2) has been reported in α-RuCl₃ under applied field (Kasahara et al. Nature 2018, Yokoi et al. Science 2021). The 1/2 ...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-no-dm-particle

- **Name:** No dark matter particle: SM is complete, gravity corrections explain rotation curves
- **Description:** Neither the standard spectral triple (C⊕H⊕M₃(C)) nor the Pati-Salam extension (H⊕H⊕M₄(C)) produces a viable dark matter candidate. Right-handed neutrinos are too heavy and unstable; lep...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### FLAG-inflation

- **Name:** Inflation tension: spectral action ξ_eff = 0.07, Starobinsky needs ξ ~ 10⁴
- **Description:** Pure quartic σ-field inflation from the spectral action is EXCLUDED by Planck (n_s=0.950 vs measured 0.965, r=0.267 vs bound <0.11). Starobinsky R² inflation recovers Planck-compatible prediction...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PARTIAL-qgp

- **Name:** QGP deconfinement: SU(3) structure proven, dynamics beyond perturbative expansion
- **Description:** QBP proves the SU(3) gauge structure (Hessian λ=12, Lean verified) and asymptotic freedom follows from the standard beta function. Confinement and deconfinement are properties of this gauge struct...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-correlated-alpha-G

- **Name:** α and G variations must be correlated (both moments of same f(u))
- **Description:** In the crystallisation model, α comes from f(0) and G comes from f(2). Both are moments of the same function f(u). Therefore their variations CANNOT be independent — they must be correlated with...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### FLAG-profile-underdetermined

- **Name:** Crystallisation profile f(u) shape before completion is underdetermined
- **Description:** Computation (v3.5): The direction of G evolution (stronger or weaker at high z) depends on the assumed shape of f(u) BEFORE crystallisation. A width-only model (Gaussian narrowing) gives G(z=14) ~ ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### OBS-finsler-gravity

- **Name:** Finsler gravity explains cosmic acceleration without dark energy (ZARM 2026)
- **Description:** Pfeifer, Voicu et al. (2025, JCAP): Finsler gravity extension of GR uses a broader spacetime geometry to describe gravitational behaviour of gases more precisely. Can explain cosmic acceleration wi...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### OBS-big-crunch

- **Name:** Cornell: universe may end in big crunch ~20 Gyr from now if DE weakens
- **Description:** Luu, Qiu & Tye (2025, JCAP): Using DESI + other DE data, calculate that if dark energy continues weakening, the universe reaches maximum size in ~11 Gyr then collapses in a big crunch ~20 Gyr from ...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-conformal-profile

- **Name:** Conformal gravity density profile: core → isothermal → PLATEAU → sharp cutoff
- **Description:** Applying Wagner's probability framework to conformal gravity (Φ = -GM/r + γ*c²r/2 - κc²r²) instead of Newtonian gravity produces a FOUR-REGION density profile distinct from NFW: (1) Core (r <...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-holographic-boundary-gravity

- **Name:** Holographic boundary gravity: a₀ = κ_BH (parent BH surface gravity), MOND as holographic effect
- **Description:** INSIGHT (Session 12): The gravitational anomaly is the holographic boundary condition of the parent black hole becoming visible at low accelerations. The parent BH surface gravity κ = c⁴/(4GM_un...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-H-equals-Mdot-over-M

- **Name:** H = Ṁ/M: Hubble parameter is the fractional accretion rate of the parent BH
- **Description:** INSIGHT (Session 12): If the observable universe is the holographic interior of a parent BH growing by accretion in Universe 1, then the Hubble parameter H = Ṁ/M (fractional mass accretion rate)....
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-cosmic-birefringence

- **Name:** G₂→SU(3) breaking predicts parity-violating CMB polarisation (cosmic birefringence)
- **Description:** The G₂→SU(3) crystallisation breaks 14 generators into 8⊕3⊕3̄. The triplet (3) follows the quaternionic multiplication cycle (ij=k, jk=i, ki=j) and carries a definite chirality. The anti-t...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### INSIGHT-info-paradox-resolution

- **Name:** BH information paradox resolved: information goes into daughter universe, not Hawking radiation
- **Description:** In the genesis model, the black hole information paradox has a natural resolution: the information encoded on the parent BH's horizon does NOT return in the Hawking radiation. It goes into the daug...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-koide-phase-2-over-9

- **Name:** Koide phase δ_fund = Q/dim(Im ℍ) = 2/9: lepton mass ratios from algebra
- **Description:** FINDING (Session 12): The Koide phase in the fundamental domain of the Z₃ symmetry is δ_fund = δ mod (2π/3) = 2/9 to within 0.0005%. This decomposes as 2/9 = (2/3) × (1/3) = Q × (1/dim(Im �...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-wolfenstein-A-sqrt-Q

- **Name:** Wolfenstein A = √Q = √(2/3): CKM hierarchy from Koide ratio
- **Description:** CONJECTURE (Session 12): The Wolfenstein parameter A = √(2/3) = √Q, linking the CKM hierarchy directly to the Koide ratio. With λ = sin(π/14) from Fano and A = √(2/3), the predicted θ₂�...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-ckm-cp-phase-arctan-sqrt7

- **Name:** CKM CP phase δ_CP = arctan(√7) ≈ 69.3° from octonion dimensionality
- **Description:** CONJECTURE (Session 12): sin²(δ_CP) = dim(Im 𝕆)/dim(𝕆) = 7/8, giving δ_CP = arctan(√7) ≈ 69.3°. Measured: 68° ± 2° (PDG global fit), within 0.6σ. The algebraic identity sin²(δ) ...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### REF-jido-eta-prime-chiral-2012

- **Name:** Jido et al.: η′ mass reduction ~100 MeV from 30% chiral restoration
- **Description:** Jido, Nagahiro & Hirenzaki (2011/2012, Kyoto/Nara) showed that the U(1)_A anomaly causes the η′-η mass splitting NECESSARILY through chiral symmetry breaking. At nuclear saturation density ρ�...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-eta-prime-mass-shift-1-over-24

- **Name:** η′ mass shift = m_η′/|Stab| = 957.8/24 = 39.9 MeV at ρ₀
- **Description:** QBP PREDICTION (Session 12): The fractional η′ mass shift at nuclear saturation density is Δm/m = 1/|Stab(Fano line)| = 1/24, giving Δm_η′ = 957.78/24 = 39.9 MeV. MEASURED (CBELSA/TAPS opti...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### Q27-TOV-limit-from-Fano

- **Name:** Q27: Derive the TOV limit from the Fano plane geometry
- **Description:** OPEN QUESTION (Session 12): The Tolman-Oppenheimer-Volkoff limit (~2.0-2.4 M☉) is the maximum neutron star mass — the boundary between stable neutron star (State 2) and collapse to black hole (...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-TOV-limit-sqrt-7-over-3

- **Name:** TOV limit = M_Ch × √(7/3) = 2.20 M☉ from Fano plane dimensions
- **Description:** QBP PREDICTION (Session 12): M_TOV = M_Ch × √(dim(Im 𝕆)/dim(Im ℍ)) = 1.44 × √(7/3) = 2.200 M☉. Observed: 2.0-2.4 M☉ (central ~2.2). Match: <0.1%. PHYSICAL MEANING: The Chandrasekhar ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-chiral-restoration-3rho0

- **Name:** Full chiral restoration at dim(Im ℍ)·ρ₀ = 3ρ₀: crystallisation onion model
- **Description:** QBP PREDICTION: The chiral condensate follows ⟨q̄q⟩_ρ/⟨q̄q⟩_0 = 1 - ρ/(dim(Im ℍ)·ρ₀) = 1 - ρ/(3ρ₀), vanishing at ρ = 3ρ₀. At ρ₀: 33% reduction (matches pionic atom data...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-conformal-sound-speed-1-over-3

- **Name:** Conformal sound speed c_s² = 1/dim(Im ℍ) = 1/3 at full chiral restoration
- **Description:** The conformal limit of the speed of sound in QCD matter — c_s² = 1/3 for massless quarks — IS 1/dim(Im ℍ). This known QCD result acquires algebraic meaning in QBP: when the crystallisation f...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-peak-sound-speed-Q

- **Name:** Peak sound speed c_s²(peak) ≈ Q = 2/3 at partial crystallisation density
- **Description:** QBP CONJECTURE: The peak speed of sound in neutron star matter occurs at the density where the crystallisation is partially melted, and c_s²(peak) ≈ Q = 2/3. The crystallisation adds stiffness b...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### INSIGHT-iron-handoff-nuclear-to-magnetic

- **Name:** Iron as the energy handoff point: nuclear harmonics → gravitational collapse → magnetic storage
- **Description:** INSIGHT (Session 12): Iron-56 is simultaneously (a) the nuclear binding energy peak (where strong force and EM reach equilibrium), (b) the strongest ferromagnet (maximal classical EM coherence), an...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-proton-fraction-1-over-8

- **Name:** NS proton fraction x_p ≈ 1/dim(𝕆) = 1/8 = cos²(δ_CP) at ρ₀
- **Description:** REVISED (Session 12): COMPUTATION SHOWS x_p ≈ 0.04-0.05 at ρ₀, NOT 1/8. The proton fraction x_p = 1/dim(𝕆) = 1/8 = 0.125 is reached at ρ ≈ 3.8ρ₀ (for E_sym = 31.6 MeV, L = 58.9 MeV). ...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-magnetar-energy-fraction-1-over-3

- **Name:** Magnetar energy fraction E_B/E_grav = 1/dim(Im ℍ) = 1/3
- **Description:** QBP CONJECTURE: The maximum fraction of gravitational binding energy stored in the magnetic field of a magnetar is 1/dim(Im ℍ) = 1/3. One generation's worth of the gravitational energy goes magne...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

### INSIGHT-urca-threshold-dim-O

- **Name:** Direct URCA threshold x_p = 1/(1+dim(𝕆)) = 1/9: kinematic origin
- **Description:** The direct URCA threshold for neutron star cooling (x_p ≥ 1/9) has an algebraic decomposition: the momentum conservation condition k_F(n) ≤ 2k_F(p) cubes to (1-x_p) ≤ 8x_p = dim(𝕆)·x_p, g...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-urca-onset-3rho0

- **Name:** Direct URCA onset at ρ = dim(Im ℍ)·ρ₀ = 3ρ₀: cooling transition at crystallisation melting point
- **Description:** COMPUTED (Session 12): β-equilibrium calculation with standard nuclear symmetry energy (E_sym = 31.6 MeV, L = 58.9 MeV) shows the proton fraction x_p reaches the direct URCA threshold (x_p > 1/9 �...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-interpolation-function-derived

- **Name:** MOND interpolation ν(y) = [1+√(1+4/y)]/2 derived from holographic boundary thermodynamics
- **Description:** DERIVED (Session 12): The Milgrom interpolation function is derived from four premises with zero free parameters: (P1) universe is holographic interior of parent BH with surface gravity κ = a₀, ...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PROOF-M-proportional-to-a

- **Name:** Parent BH mass proportional to scale factor: M(a) = M₀a, model-independent
- **Description:** DERIVED (Session 12): From H = Ṁ/M and H = ȧ/a, it follows that dM/da = M/a → M ∝ a = 1/(1+z). The parent BH mass is proportional to the scale factor. This is INDEPENDENT of the accretion mo...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-lambda-as-cross-term

- **Name:** Effective Λ as cross-term 2AB between early and late accretion modes
- **Description:** DERIVED (Session 12): With Ṁ = Ṁ₀ + βM² (constant + Bondi), the boundary Hubble rate is H_B = A(1+z) + B/(1+z) where A = Ṁ₀/M₀, B = βM₀. H_B² = A²(1+z)² + 2AB + B²(1+z)⁻². T...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-w-not-minus-1

- **Name:** Dark energy w(z) ≠ -1: accretion model predicts dynamical DE
- **Description:** PREDICTION (Session 12): The accretion model gives w_eff(z) that varies: w ≈ -1 at z_t ≈ 0.7 (where the cross-term dominates), w > -1 at z < z_t (quintessence-like), w < -1 at z > z_t (phantom-...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### INSIGHT-entropy-cone-division-algebra-inversion

- **Name:** Entropy cone hierarchy inversely maps to division algebra hierarchy
- **Description:** FINDING (Session 12, OQ-1 evaluation): The entropy cone hierarchy (Holographic ⊂ Hypergraph ≈ Stabiliser ⊆ Quantum) inversely maps to the division algebra hierarchy (ℝ ⊂ ℂ ⊂ ℍ ⊂ �...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-fano-associativity-7beam

- **Name:** 7-beam holographic experiment: Fano-line recordings are order-independent, non-Fano are order-dependent
- **Description:** QBP PREDICTION (Session 12, OQ-3 evaluation): In a 7-beam holographic system (one beam per imaginary octonion unit), exactly 7 of 35 possible 3-beam subsets (the Fano lines) produce associative int...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-division-algebra-entropy-cone-mapping

- **Name:** Division algebra hierarchy maps onto entropy cone hierarchy: ℂ→holographic, ℍ→hypergraph, 𝕆→quantum
- **Description:** DERIVED (Session 12, OQ-1 response): The Cayley-Dickson division algebra hierarchy maps onto the quantum information entropy cone hierarchy: ℝ → Shannon ⊂ ℂ → Holographic(graph) ⊂ ℍ �...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### INSIGHT-branch-A-hypergraph-boundary

- **Name:** Branch A fix: parent BH boundary is a HYPERGRAPH (ℍ-weighted), not a hologram (ℂ-weighted)
- **Description:** INSIGHT (Session 12): The Branch A CMB failure (COMP-branch-A-cmb-boundary-analysis, incoherent: ν-1 ∝ 1/√k gives wrong scale dependence for CDM replacement) assumed a GRAPH-level (ℂ-weighte...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### INSIGHT-bcc-iron-fano-cube

- **Name:** BCC iron coordination 8 = dim(𝕆): Fano cube geometry in the nuclear binding peak element
- **Description:** INSIGHT (Session 12): BCC α-iron has coordination number 8 = dim(𝕆). The Fano cube (standard 3D mnemonic for octonion multiplication) uses the 7 non-zero vertices of F₂³ for the imaginary oc...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### INSIGHT-fano-cube-universal-compute-cell

- **Name:** Fano cube as universal compute cell: Locale, BMA, holographic hypergraph, QBP compute unit converge on same geometry
- **Description:** INSIGHT (Session 12): The Fano cube (7 vertices of F₂³ minus origin = 7 imaginary octonion units) is the natural compute cell for four QBP programmes simultaneously: (1) Locale: 3 spatial coordi...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PROOF-beta-function-3-times-7

- **Name:** SU(3) β-function numerator 21 = dim(Im ℍ) × dim(Im 𝕆) = 3×7: algebraic origin of the hierarchy
- **Description:** IDENTIFIED (Session 12): The 1-loop β-function coefficient for SU(3) with 3 generations of quarks has numerator 11×3 - 2×6 = 21 = 3×7 = dim(Im ℍ) × dim(Im 𝕆). The 3 comes from n_gen = dim...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### Q28-alpha-GUT-from-stabiliser

- **Name:** Q28: Is α_GUT = 1/(|Stab|+1) = 1/25? The missing link for deriving G
- **Description:** KILLED BY COMPUTATION (Session 12): Full 2-loop SM RG running from measured α₃(M_Z) = 0.1179 gives 1/α₃(M_Pl) = 52.7, NOT 25. The candidate α_GUT = 1/(|Stab|+1) = 1/25 is WRONG by a factor o...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### WISDOM-schema-vs-instance

- **Name:** WISDOM: The algebra is the schema, the boundary is the instance. G is contingent, not necessary.
- **Description:** WISDOM (Session 12): Every successful QBP prediction is a DIMENSIONLESS RATIO — Q=2/3, δ=2/9, sin(π/14), arctan(√7), √(7/3), 1/24. No dimensional quantities (masses in GeV, G in m³/kg/s²)...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### PRED-f4-zero-vacuum-energy

- **Name:** Spectral action vacuum energy f₄ = 0: information-theoretic argument from Axiom 1
- **Description:** DERIVED (Session 12): The spectral action's cosmological constant term f₄Λ⁴ must vanish (f₄ = 0) for two independent reasons: (1) CONSISTENCY: QBP explains 'dark energy' as accretion cross-t...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### WISDOM-003-there-is-only-f-u

- **Name:** W-003: Forces are moments of a spectrum. The spectrum is the crystallisation. There is only f(u).
- **Description:** WISDOM (Session 12): The classical separation of physics into four forces is an artifact of the low-energy expansion. The spectral action says there is ONE object: the Dirac operator D. Its profile...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-profile-function-f0-f2-ratio

- **Name:** Profile function f₀/f₂ = 1/dim(Im ℍ) = 1/3: gravity-gauge ratio from the Fano plane
- **Description:** DERIVED (Session 12): The spectral action profile f(u) = A(1 + 7u - 2.5u²)exp(-u) has f₀/f₂ = 1/3 = 1/dim(Im ℍ) and f₄ = 0. The linear coefficient 7 = dim(Im 𝕆). With the CCM (DLM 2014)...
- **Suggestion:** `theory-external`
- **Rationale:** citation-year pattern detected in description/notes; may cite external work

### PRED-inv-alpha-GUT-16pi

- **Name:** 1/α_GUT ≈ 16π = 50.3: candidate algebraic expression (2.9% from computed 48.9)
- **Description:** CANDIDATE (Session 12): The unified gauge coupling from the spectral action with f₀/f₂ = 1/3 and CCM normalization gives 1/α_GUT = 48.87. The closest algebraic expression is 16π = 50.27 (2.9%...
- **Suggestion:** `theory`
- **Rationale:** no citation pattern detected → safe default

### CONV-spectral-entropy-zeta

- **Name:** MATHEMATICS: Chamseddine-Connes-van Suijlekom 2018 derives universal profile function from entropy/Riemann zeta - candidate convergence with QBP f(u)
- **Description:** External mathematical result by the originators of the spectral action: the von Neumann entropy of the fermionic second quantization of a spectral triple equals the spectral action for a SPECIFIC u...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

### CONV-cd-tower-in-zeta-moments

- **Name:** MATHEMATICS: Even-level Cayley-Dickson tower (dim Im H, S, chingons, ...) embedded as dim-Im factors in CCvS entropy-function coefficients
- **Description:** The CCvS 2018 closed form gamma(-a) = (2^(2a) - 1)/(a*2^(2a)) * (2a+1)!/(a-1)! * zeta(2a+1) for positive integer a contains the numerator factor 2^(2a) - 1, which is exactly dim(Im A_(2a)) where A_...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

### KILLED-f4-info-theoretic-justification

- **Name:** KILLED: 'f_4 = 0 follows from Axiom 1 (information preserved)' — contradicted by direct entropy computation
- **Description:** QBP Theory v3.0 §7.3 argued that f_4 = 0 follows from Axiom 1 (information preserved) on the grounds that 'the vacuum is informationally empty' and 'an optimal encoding (Axiom 2) allocates no curv...
- **Suggestion:** `theory-external`
- **Rationale:** description references external authority + citation pattern detected

## Decisions applied

- MEAS-alpha
- MEAS-sin2tw
- MEAS-alphas
- MEAS-koide
- MEAS-udd
- MEAS-delta
- MEAS-jd
- MEAS-tolfac
- FLAG-J
- FLAG-Tc
- FLAG-xi
- FLAG-Hc2
- FLAG-postd-IE
- PRED-3episode
- PRED-willow-j
- OBS-f0-2alpha
- OBS-cbt-koide
- CONSTRAINT-ynu
- MEAS-bi2se3-topo
- MEAS-matbg-fragile
- OBS-alpha-invsqrt3
- MEAS-rucl3-jeff
- INST-ckm
- OBS-desi-4thirds
- EXT-dm-particle-mass
- EXT-dm-cross-section
- PROOF-stelle-no-linear
- REF-algebraic-crystallisation-paper
- CONV-flow-fragmentalism
- COMP-cmb-power-spectrum-accretion
- COMP-branch-A-cmb-boundary-analysis
- PRED-cutoff-scale-0p04-Planck
- COMP-sm-non-unification-at-1loop

## Warnings

- anchor PROOF-hurwitz: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-42zd: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-hessian: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-eigenratios: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-g2: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-fano: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-cl6: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-3gen: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-born: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state
- anchor PROOF-shells: proof_state set to "written" (not "verified"); run cth lean-link (CTH #54) to populate verification record and advance proof_state

## Re-run command

```
cth migrate archive/cth-inventory/confluent-trust-inventory-v5_3.json --decisions <decisions.json> -o <output.json>
```
