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

## 4b. The dynamics probe — the no-go was OVERCLAIMED; the algebra DOES offer SSB ingredients (corrected after RT+Gemini review of PR #561)

> **Correction.** My first cut (`dynamics_probe.py`) claimed "no Mexican hat in the algebra." The RT and Gemini reviews (PR #561) both flagged this as **overclaimed**, and they were right. The probe only showed the *trivial* fact that **positive sum-of-squares actions are single-well** — it (i) assumed positive mass coefficients (rep-theory allows a wrong-sign V(|y|²) = −μ²|y|²+λ|y|⁴, which *is* a Mexican hat), and (ii) ignored cross-couplings to the retained sector. The follow-up `crosscoupling_probe.py` settles it.

**What the rep-theory actually fixes (correct, narrow):** the only SO(4)-invariant of a *single* (2,2)-vector y is |y|² — so any single-field self-potential has the *form* V(|y|²). Rep-theory does **not** fix the *sign* of the mass term.

**The cross-coupling computation (`crosscoupling_probe.py`) — the algebra supplies BOTH signs:**
- Norm and same-handed products (|y|², |X·y|², |y·X|²) are **positive-definite** (Euclidean octonion norm — the #474 D10 guardrail).
- **But the non-commutative cross form Re⟨X·(y e₄), (y e₄)·X⟩ is NEGATIVE-definite for imaginary backgrounds** (eigenvalues all −1 for X=e₁; −6.37 for generic imaginary X). Reason (clean): for an imaginary unit, left- and right-multiplication on the complement *anticommute*, so ⟨e₁(ye₄),(ye₄)e₁⟩ = −|y|².

**∴ Corrected conclusion: an SSB potential is NOT excluded — it is algebraically *available*.** A potential combining the positive norm with the negative non-commutative cross-coupling (switched on by an imaginary background in the retained sector) can be **sign-indefinite / tachyonic**. The octonion algebra carries the ingredients for spontaneous symmetry breaking; what it does *not* hand us for free is *which* combination the crystallisation dynamics selects (the coefficients).

### Relation to #548 (corrected)
- **#548:** the 7 quaternionic subalgebras are one G₂ orbit → *which* ℍ is **gauge** (the angular/orbit direction is redundancy, not physics). ✔ stands.
- **#559 (corrected):** the *radial* direction (crystallised vs not — the magnitude of the order parameter) is **physical** and *can* be driven by a genuine (sign-indefinite) potential the algebra supplies. So the Mexican-hat picture is *available*: a flat gauge rim (the G₂ orbit, #548) + a physical radial breaking. The earlier "no potential, therefore pure Γ-process" inference was **withdrawn** — it conflated gauge redundancy with vacuum degeneracy (Gemini's point).

> **Status:** the dynamics question is **OPEN and more promising than the no-go suggested.** The algebra has tachyon-capable couplings; the keystone is now to determine which coefficients the crystallisation selects (and whether the selected potential reproduces the observed spectrum). A *full* indefinite signature — should one combination dominate — also points at the split-octonion / sedenion (zero-divisor) level, where the positive-definite norm is lost; flagged for later, not claimed.

## 5. Net result of this pass (honest, corrected)

**Solid, anchorable:** the verified kinematic skeleton (𝟕=(𝟑,𝟏)⊕(𝟐,𝟐), lost = (2,2)); **and the corrected dynamics finding** — the algebra supplies *both* positive (norm) and **negative (non-commutative cross-coupling)** quadratic forms, so an SSB potential is **algebraically available** (the no-go is retracted).

**Killed:** the Higgs/ρ=1 interpretation (numerology, §3) — stays dead.

**The genuine open keystone:** not "is there a potential" (yes, ingredients exist) and not rep-labelling — but **which potential the crystallisation dynamics selects**, i.e. the coefficients of {positive norm, negative cross-coupling} and whether the resulting VEV/spectrum is physical. That is the real #559 continuation.

## 6. AC status (#559)
| AC | Scope | Status |
|----|-------|--------|
| AC1 | generator→DOF map (𝕆→ℍ) | 🟡 **kinematic map established** (lost = (2,2)); the SSB potential is **algebraically available** (§4b corrected), coefficients open |
| AC2 | Fork 1 (internal vs KK) | ⏳ **OPEN** — (2,2)=SO(4)-vector; decided by the selected potential / dynamics, not yet fixed |
| AC3 | Fork 2 (discrete vs continuous Γ) | ⏳ **open** — untouched by this pass |
| AC4 | dimensionless falsifiable consequence | ❌ ρ=1 killed (§3); a number must come from the **selected** potential's VEV/spectrum (open) or the direct-Γ observable (#539) |
| AC5 | record as CTH anchors + update doc §4 | ⏳ anchor: verified skeleton, interpretation-kill, the corrected SSB-ingredient finding |

**∴ The honest headline:** the kinematics of 𝕆→ℍ are nailed down from first principles; the Higgs interpretation is dead; my "no SSB potential" no-go was **overclaimed and is retracted** — the cross-coupling computation shows the octonion algebra **does** supply sign-indefinite (tachyon-capable) couplings, so an SSB potential is *available*. The genuine keystone is now **which potential the crystallisation dynamics selects** (coefficients + resulting spectrum) — a real, well-posed continuation of #559.
