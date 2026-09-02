/-
  QBP.Cosmo.Nucleosynthesis — mass-number ↔ Cayley–Dickson dimension identities
  =============================================================================

  Backing file for four CTH `provenance_kind:proof` anchors that assert an
  *arithmetic* correspondence between the mass number `A` of a selected
  alpha-process nuclide and a product of real dimensions of Cayley–Dickson
  algebras, as constructed in `QBP.Foundations.CDDimension`:

      dim ℝ (CDAlg ℝ 2) = 2² = 4   (ℍ, the quaternions)
      dim ℝ (CDAlg ℝ 3) = 2³ = 8   (𝕆, the octonions)
      dim ℝ (ImSubmodule 3) = 2³ − 1 = 7   (Im 𝕆, the imaginary octonions)
      dim ℝ (CDAlg ℝ 4) = 2⁴ = 16  (𝕊, the sedenions)

  The four anchored claims (each: `mass number = product of algebra dimensions`):

  * `alpha_particle_is_quaternionic`  ⁴He : A = 4  = dim ℍ
  * `iron_56_double_octet`            ⁵⁶Fe: A = 56 = dim(Im 𝕆) · dim 𝕆 = 7·8
  * `oxygen_16_is_sedenion`           ¹⁶O : A = 16 = (dim ℍ)² = dim 𝕊
  * `silicon_28_alpha_ladder`         ²⁸Si: A = 28 = dim(Im 𝕆) · dim ℍ = 7·4

  ── HONESTY BOUNDARY (read before citing this file) ──────────────────────────
  What is PROVEN here is exactly the arithmetic: each mass number equals the
  stated product of the *genuine* real dimensions of the corresponding CD
  algebras (the right-hand sides are `Module.finrank ℝ …` applied to the real
  carriers of `CDDimension.lean`, reduced via `finrank_cdAlg` /
  `finrank_imSubmodule`, NOT bare numerals). These are honest, non-vacuous
  theorems of arithmetic and linear algebra.

  What is NOT proven — and is deliberately confined to prose, never asserted as
  a Lean theorem — is the PHYSICS: that this dimensional coincidence *explains*
  nuclear stability, the doubly-magic character of ⁴He / ¹⁶O, or the alpha-ladder
  of stellar nucleosynthesis terminating near ⁵⁶Fe. Those are physical
  interpretations / hypotheses of the QBP programme, not consequences of the
  algebra. A dimension count is a necessary numerological coincidence, not a
  derivation of the nuclear binding that makes these nuclides abundant. Do not
  read the theorems below as a physical explanation of stability.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom; closure ⊆ {propext, Classical.choice,
  Quot.sound} for every theorem.
-/
import QBP.Foundations.CDDimension

namespace QBP.Cosmo.Nucleosynthesis

open QBP.Foundations.CDDimension QBP.Foundations.CDAlg Module

/-! ## 1. ⁴He — the alpha particle as the quaternion dimension

`PROOF-alpha-particle-quaternion`: the ⁴He mass number `A = 4` equals the real
dimension of the quaternions `ℍ = CDAlg ℝ 2`.

Physical interpretation (NOT proven): ⁴He is the fundamental building block of
the stellar alpha-process ladder; QBP reads its 4 nucleons as mirroring the
4 real dimensions of ℍ. The stability of the alpha particle is a nuclear-physics
fact, not a corollary of this dimension count. -/

/-- **⁴He mass number = dim ℍ.**  `A(⁴He) = 4 = finrank ℝ (CDAlg ℝ 2)`.
    Plain reading: the ⁴He mass number equals the real dimension of the
    quaternion algebra. -/
theorem alpha_particle_is_quaternionic :
    (4 : ℕ) = finrank ℝ (CDAlg ℝ 2) := by
  rw [finrank_cdAlg]; norm_num

/-! ## 2. ⁵⁶Fe — the double octet

`PROOF-iron-56-double-octet`: the ⁵⁶Fe mass number `A = 56` factors as
`dim(Im 𝕆) · dim 𝕆 = 7 · 8`.

Physical interpretation (NOT proven): ⁵⁶Fe sits near the peak of the nuclear
binding-energy-per-nucleon curve, the endpoint of exothermic stellar fusion;
QBP reads `56 = 7·8` as the product of the imaginary-octonion (7) and full
octonion (8) dimensions. Note the alternative factorisation `56 = 14·4 = dim G₂
· dim ℍ` (G₂ = Aut 𝕆); we do NOT anchor to that here because `dim G₂ = 14` is
Lie-theoretic bookkeeping, not a `finrank` of a real carrier in this repo — see
`FanoGenesis.g2_decomposition_14_8_3_3`. The binding-curve peak is a
nuclear-physics fact, not a corollary of this factorisation. -/

/-- **⁵⁶Fe mass number = dim(Im 𝕆) · dim 𝕆.**
    `A(⁵⁶Fe) = 56 = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 3) = 7*8`.
    Plain reading: the ⁵⁶Fe mass number equals the imaginary-octonion dimension
    times the full-octonion dimension. -/
theorem iron_56_double_octet :
    (56 : ℕ) = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 3) := by
  rw [finrank_imSubmodule, finrank_cdAlg]; norm_num

/-! ## 3. ¹⁶O — the sedenion square

`PROOF-oxygen-16-sedenion`: the ¹⁶O mass number `A = 16` equals `(dim ℍ)² = 4²`
and equally the full sedenion dimension `dim 𝕊 = 16`.

Physical interpretation (NOT proven): ¹⁶O is doubly magic (Z = N = 8) and a
principal alpha-ladder product; QBP reads `16 = 4² = 16` as the quaternion
dimension squared, coinciding with the sedenion dimension. Double-magic
stability is a shell-model fact, not a corollary of this identity. -/

/-- **¹⁶O mass number = (dim ℍ)².**
    `A(¹⁶O) = 16 = (finrank ℝ (CDAlg ℝ 2))^2 = 4^2`.
    Plain reading: the ¹⁶O mass number equals the square of the quaternion
    dimension. -/
theorem oxygen_16_is_sedenion :
    (16 : ℕ) = (finrank ℝ (CDAlg ℝ 2)) ^ 2 := by
  rw [finrank_cdAlg]; norm_num

/-- **(dim ℍ)² = dim 𝕊.**  The square of the quaternion dimension equals the
    sedenion dimension: `(finrank ℝ (CDAlg ℝ 2))^2 = finrank ℝ (CDAlg ℝ 4)`,
    i.e. `4² = 16`.  Together with `oxygen_16_is_sedenion` this pins
    `A(¹⁶O) = 16 = (dim ℍ)² = dim 𝕊`. -/
theorem oxygen_16_sedenion_dim :
    (finrank ℝ (CDAlg ℝ 2)) ^ 2 = finrank ℝ (CDAlg ℝ 4) := by
  rw [finrank_cdAlg, finrank_cdAlg]; norm_num

/-! ## 4. ²⁸Si — the Fano alpha-ladder rung

`PROOF-silicon-28-fano-ladder`: the ²⁸Si mass number `A = 28` factors as
`dim(Im 𝕆) · dim ℍ = 7 · 4`.

Physical interpretation (NOT proven): ²⁸Si is a major alpha-process waypoint
(silicon burning feeds the iron peak); QBP reads `28 = 7·4` as the
imaginary-octonion dimension (the 7 Fano directions) times the quaternion
dimension. The role of ²⁸Si in silicon burning is a nuclear-physics fact, not a
corollary of this factorisation. -/

/-- **²⁸Si mass number = dim(Im 𝕆) · dim ℍ.**
    `A(²⁸Si) = 28 = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 2) = 7*4`.
    Plain reading: the ²⁸Si mass number equals the imaginary-octonion dimension
    (7 Fano directions) times the quaternion dimension. -/
theorem silicon_28_alpha_ladder :
    (28 : ℕ) = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 2) := by
  rw [finrank_imSubmodule, finrank_cdAlg]; norm_num

/-! ## Completeness audit — `#print axioms` -/

#print axioms alpha_particle_is_quaternionic
#print axioms iron_56_double_octet
#print axioms oxygen_16_is_sedenion
#print axioms oxygen_16_sedenion_dim
#print axioms silicon_28_alpha_ladder

end QBP.Cosmo.Nucleosynthesis
