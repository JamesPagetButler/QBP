# #559 — The generator→DOF map: 𝕆→ℍ, where do e₄…e₇ go?

**Status:** WORKING — verified math + interpretation under adversarial test · **Issue:** #559 · **Date:** 2026-06-13
**Predecessor:** `docs/foundations/substrate-foundational-concerns-resolution-2026-06-13.md` §4 (the keystone the adversarial gate exposed).
**Discipline:** verify the rigorous object *first*; attack the interpretation *before* adopting it; predict a dimensionless number or the mechanism dies (f(0)/#535).

---

## 1. The verified result (AC1) — SOLID

**Claim (computationally verified, not asserted).** When 𝕆 crystallises to a quaternion subalgebra ℍ ⊂ 𝕆:
- the automorphism symmetry **G₂ = Aut(𝕆) breaks to SO(4) = (SU(2)_a × SU(2)_b)/ℤ₂**, the stabilizer of ℍ, realised by the explicit map **γ(a,b): x + y·e₄ ↦ a·x·a\* + (b·y·a\*)·e₄** (a,b unit quaternions);
- the seven imaginary octonions branch as

$$\mathbf{7} \;=\; (\mathbf{3},\mathbf{1}) \,\oplus\, (\mathbf{2},\mathbf{2})$$

  - **retained** {e₁,e₂,e₃} = Im(ℍ) = **(3,1)**: an SU(2)_a triplet (spin-1), SU(2)_b singlet → the **unbroken SU(2)**;
  - **lost** {e₄,e₅,e₆,e₇} = ℍ^⊥ = ℍ·e₄ = **(2,2)**: an irreducible bi-doublet.

**Verification** (`verify_g2_so4_branching.py`, output in `verification_output.txt`), from the raw octonion structure constants (Cayley–Dickson doubling), all checks pass:
- γ(a,b) is a genuine octonion automorphism — 2000 random trials, γ(uv)=γ(u)γ(v). ✓
- {e₁,e₂,e₃} and {e₄,e₅,e₆,e₇} are each SO(4)-invariant subspaces. ✓
- {e₁,e₂,e₃}: SU(2)_b acts trivially, SU(2)_a acts as SO(3) (orthogonal, det +1) ⇒ spin-1 triplet (3,1). ✓
- {e₄,e₅,e₆,e₇}: both SU(2)s act non-trivially; orbit-span rank 4 ⇒ irreducible (2,2). ✓

Cross-checks standard literature (Conway–Smith *On Quaternions and Octonions*; Baez *The Octonions* §4.1; LiE/Slansky G₂⊃SU(2)×SU(2) branching).

**∴ The map is precise and non-arbitrary:** the lost generators are a **(2,2) bi-doublet**, full stop. That part is not interpretation — it is the representation content.

## 2. Fork 1 (internal vs KK) — NOT resolved by the kinematics (corrected)

My first-pass claim that the (2,2) is "internal, therefore spacetime stays 4D" **does not survive the adversarial pass.** The (2,2) of SU(2)_a×SU(2)_b ≅ SO(4) is precisely the **vector representation of SO(4)** — it transforms like a 4-vector xᵘ. So the algebra does **not** dictate internal-vs-spacetime; declaring it internal was an assumption, not a derivation.

**The QBP-specific wrinkle (honest):** in QBP, spacetime is *already* the quaternion worldline ℍ (Γ + i,j,k), and the retained triplet {e₁,e₂,e₃} = i,j,k *are* the spatial directions. So SU(2)_a (which acts on {e₁,e₂,e₃} as SO(3)) **is literally spatial rotation**, and the (2,2) complement carries **spatial-rotation charge** — it is *not* a scalar. The (2,2) cannot be "the same" spacetime (we already have ℍ), but it also cannot be a simple internal scalar (it's an SO(4)-vector under the spatial SU(2)). **Its nature is undecided by the algebra and awaits the dynamics (§3).** Fork 1 stays OPEN.

## 3. The interpretation (Higgs / ρ=1) — ❌ KILLED by the adversarial pass (numerology)

> The first-pass interpretation — lost generators = custodial-SU(2) Higgs, predicting ρ=1 — was run through the adversarial Gemini gate (Furey/Feynman) and **failed on all three claims.** Recorded as kill-history; **not adopted.**

| Claim | Verdict | Why (Furey/Feynman) |
|---|---|---|
| A — (2,2) is internal DOF | ❌ FAILS | (2,2) ≅ SO(4)-vector = transforms like xᵘ; "internal" is assumed, not derived |
| B — (2,2) is the custodial Higgs | ❌ FAILS | γ(a,b) asymmetry ⇒ SU(2)_a = spatial rotation; the (2,2) carries spatial-rotation charge, so it is **not a Lorentz scalar** → cannot be the Higgs; identifying it with weak isospin couples weak charge to orientation (Coleman–Mandula) |
| C — predicts ρ = 1 | ❌ FAILS | ρ=1 needs a VEV from a **potential**; the algebra has no Lagrangian/potential. SU(2)_diag being an available subgroup ≠ the algebra *predicting* the breaking. Steals the SM Mexican-hat answer |

**The numerology test (failed):** stripped of labels, all that is established is "an 8-dim algebra breaks to a 4-dim subalgebra; the complement is an SO(4)-vector ℝ⁴." Matching "4" and "SU(2)" to the Higgs is dimension-counting, not physics.

**The sharpened keystone (the adversary's mandate — now the real #559 sub-target):** cross from **kinematics to dynamics**. Derive an **action / potential V(φ) directly from the octonion structure** (candidate routes: a **norm-squared action** N(x)=xx̄, an **algebraic trace**, or a **geometric volume form**; the **non-associativity / associator** [x,y,z] is the only structure rich enough to plausibly source a non-trivial — non-single-well — potential). Until a symmetry-breaking potential emerges *from the algebra*, there is no VEV, no mass, no ρ. Plus: **untangle the spatial SU(2)_a from any internal SU(2)** before any gauge identification.

## 4. Fork 2 (Γ discrete vs continuous) — NOT resolved by this map

The generator→DOF map fixes *which* DOF, not the nature of Γ. AC3 remains open; nothing here forces discrete or continuous Γ. Flagged honestly — this map does not close Fork 2.

## 4b. The dynamics probe — there is NO Mexican hat in the algebra (rigorous)

Taking the adversary's mandate directly: *does the octonion algebra source a symmetry-breaking potential V(y) for the (2,2) complement?* (`dynamics_probe.py`). **Answer: no.**

- **(A) Rep-theory no-go (exact):** the only SO(4)-invariant polynomials of a single (2,2)-vector y are polynomials in |y|². So any SO(4)-invariant self-potential is V(|y|²) — and any *positive* algebra-norm gives a **single well** (minimum at y=0). SSB needs a wrong-sign mass term the positive norm cannot supply.
- **(B) Associator-squared action:** the natural non-associativity action Σ|[g_i, y·e₄, g_j]|² is an **isotropic positive** quadratic form (eigenvalues all = 96) → single-well, no tachyon.
- **(C) No tachyon anywhere:** every |associator|² form is a sum of squares ⇒ positive-semidefinite ⇒ never sign-indefinite. No algebra-natural quadratic destabilises y=0.

**∴ The octonion algebra alone provides no spontaneous-symmetry-breaking potential.** The Mexican hat the adversary (correctly) demanded for an SSB story is *not in the multiplication table*.

### Why this is a result, not a dead end — convergence with #548
- **#548** proved the 7 quaternionic subalgebras form **one G₂ orbit** → "which ℍ" is **pure gauge** (S=ln 7 is gauge-fixing, not physical entropy).
- **#559** now finds the algebra has **no potential preferring any subalgebra** (single-well / degenerate).
- **Together:** crystallisation 𝕆→ℍ is **not energy-driven SSB** — it is a **Γ-directed process** selecting one of a gauge-equivalent, energetically-degenerate family of subalgebras. The lost e₄…e₇ do not "fall into a vacuum"; their physical fate is fixed by the **dynamics of Γ (the process)**, not by a static potential.

> **HYPOTHESIS (flagged, not adopted):** crystallisation = a Γ-directed *process* over gauge-equivalent subalgebras, not potential-SSB. This is *consistent with* #548 + the §4b no-go, but it is not yet a derived mechanism — it relocates the keystone from "find the potential" (now shown not to exist) to "characterise the Γ-process." That ties #559 directly to **Fork 2 (the nature of Γ)** and to the **direct-Γ observable (#539)**.

## 5. Net result of this pass (honest)

**What survives (solid, anchorable):** the verified kinematic skeleton (𝟕=(𝟑,𝟏)⊕(𝟐,𝟐), lost = (2,2)); **and a rigorous negative** — the octonion algebra has **no SSB potential** (§4b).

**What was killed:** the physical interpretation (internal-DOF / Higgs / ρ=1) — numerology, three-for-three (§3).

**What it sharpened:** #559 is not a rep-theory problem *and not a potential problem* (the potential provably doesn't exist). Combined with #548, the answer to "where do e₄…e₇ go?" is reframed: **not into a vacuum — through a Γ-process over a gauge-degenerate family.** The genuine open work moves to **characterising the Γ-dynamics** (Fork 2 / #539), not hunting a Mexican hat.

## 6. AC status (#559)
| AC | Scope | Status |
|----|-------|--------|
| AC1 | generator→DOF map (𝕆→ℍ) | 🟡 **kinematic map established** (lost = (2,2) SO(4)-vector); physical mechanism reframed (§4b) — not potential-SSB |
| AC2 | Fork 1 (internal vs KK) | ⏳ **OPEN** — (2,2)=SO(4)-vector; the Γ-process (not the algebra) must decide (§2/§4b) |
| AC3 | Fork 2 (discrete vs continuous Γ) | ⏳ **open & now central** — the keystone relocated *to* Γ-dynamics (§4b) |
| AC4 | dimensionless falsifiable consequence | ❌ ρ=1 killed as numerology (§3); **and** the SSB-potential route is closed (§4b no-go) — a falsifiable number must come from the Γ-process / direct-Γ observable (#539), not a potential |
| AC5 | record as CTH anchors + update doc §4 | ⏳ anchor: verified skeleton, interpretation-kill, the §4b no-go, the Γ-process reframe |

**∴ The honest headline:** the kinematics of 𝕆→ℍ are nailed down from first principles, the Higgs interpretation is dead, **and the algebra provably has no SSB potential** — so crystallisation is not vacuum-selection but a **Γ-directed process over a gauge-degenerate (#548) family.** The keystone relocates from "find the potential" to "characterise the Γ-dynamics" — which is exactly the direct-Γ thread (#539), where (2) now points.
