/-
  QBP.Cosmo.DenseMatter — iron-56 → neutron-star mass bridge through dim(Im 𝕆) = 7
  ================================================================================

  Backing file for the CTH anchor `PROOF-iron-to-ns-bridge`
  (`iron_to_ns_dim_im_octonion_link`).

  Claim (from the CTH inventory):
    Both the iron-56 mass number (end of stellar exothermic fusion) and the TOV
    limit (maximum neutron-star mass) depend on `dim(Im 𝕆) = 7`.  Specifically
      • iron-56 factors as  `56 = dim(Im 𝕆) · dim 𝕆 = 7 · 8`, and
      • the TOV/Chandrasekhar mass ratio satisfies
            `(M_TOV / M_Ch)² = dim(Im 𝕆) / dim(Im ℍ) = 7 / 3`,
        i.e. `M_TOV = M_Ch · √(7/3)`  (companion `PRED-TOV-limit-sqrt-7-over-3`).
    The shared factor is `dim(Im 𝕆) = 7`: the seven Fano directions control
    where fusion ends AND how heavy a collapsed remnant can be.

  ── WHAT IS PROVEN (honesty boundary) ───────────────────────────────────────
  * The arithmetic factorisation `56 = dim(Im 𝕆) · dim 𝕆`, with the right-hand
    factors being genuine real dimensions `Module.finrank ℝ …` of the CD carriers
    from `CDDimension.lean` (reduced by `finrank_imSubmodule` / `finrank_cdAlg`,
    NOT bare numerals).
  * The dimension ratio `dim(Im 𝕆) / dim(Im ℍ) = 7 / 3` as reals, again via the
    `finrank` lemmas.
  * The real-analysis derivation: GIVEN the physical premise
    `(M_TOV / M_Ch)² = dim(Im 𝕆) / dim(Im ℍ)` (with `M_TOV, M_Ch > 0`), it
    follows that `M_TOV = M_Ch · √(7/3)`.

  What is NOT proven — deliberately kept as an EXPLICIT hypothesis, never as a
  Lean theorem — is the PHYSICS that the TOV mass ratio actually equals that
  dimension ratio, or that nuclear binding "ends at iron because of the octonions".
  Those are QBP physical hypotheses; the dimension counts are a necessary
  numerical coincidence, not a derivation of the nuclear/GR physics.

  ── QBP ANSATZ, not textbook astrophysics ───────────────────────────────────
  The `(M_TOV/M_Ch)² = 7/3` premise is a **QBP-specific algebraic ansatz**, NOT
  a standard General-Relativity result: standard GR yields no universal
  dimensionless `7/3` neutron-star mass ratio (the Buchdahl bound is a `4/9`
  compactness limit, and the TOV limit is equation-of-state dependent). The Lean
  proves only the *arithmetic consequence* of the ansatz (`M_TOV = M_Ch·√(7/3)`),
  never the ansatz itself. Do not read it as a textbook TOV input.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import QBP.Foundations.CDDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace QBP.Cosmo.DenseMatter

open QBP.Foundations.CDDimension QBP.Foundations.CDAlg Module

/-! ## 1. The iron-56 factorisation `56 = dim(Im 𝕆) · dim 𝕆` -/

/-- **⁵⁶Fe mass number = dim(Im 𝕆) · dim 𝕆.**
    `A(⁵⁶Fe) = 56 = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 3) = 7·8`.
    Plain reading: the iron-56 mass number equals the imaginary-octonion
    dimension times the full-octonion dimension. -/
theorem iron_56_double_octet :
    (56 : ℕ) = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 3) := by
  rw [finrank_imSubmodule, finrank_cdAlg]; norm_num

/-- The imaginary-octonion dimension is exactly 7: `dim(Im 𝕆) = 2³ − 1 = 7`. -/
theorem dim_im_octonion : finrank ℝ (ImSubmodule 3) = 7 := by
  rw [finrank_imSubmodule]; norm_num

/-- The imaginary-quaternion dimension is exactly 3: `dim(Im ℍ) = 2² − 1 = 3`. -/
theorem dim_im_quaternion : finrank ℝ (ImSubmodule 2) = 3 := by
  rw [finrank_imSubmodule]; norm_num

/-! ## 2. The TOV/Chandrasekhar dimension ratio `dim(Im 𝕆) / dim(Im ℍ) = 7/3` -/

/-- **The dimension ratio is 7/3.**
    `(dim(Im 𝕆) : ℝ) / dim(Im ℍ) = 7/3`, via the genuine `finrank` values. -/
theorem tov_dim_ratio :
    (finrank ℝ (ImSubmodule 3) : ℝ) / (finrank ℝ (ImSubmodule 2) : ℝ) = 7 / 3 := by
  rw [dim_im_octonion, dim_im_quaternion]; norm_num

/-- **TOV mass from the dimension ratio (real-analysis derivation).**
    GIVEN the physical premise that the squared TOV/Chandrasekhar mass ratio
    equals the imaginary-octonion / imaginary-quaternion dimension ratio, the TOV
    mass is `M_Ch · √(7/3)`.  The physics (that the premise holds) is a
    hypothesis; the conclusion is a genuine consequence carrying the positivity
    facts `M_TOV, M_Ch > 0`. -/
theorem tov_mass_sqrt_seven_thirds
    (M_TOV M_Ch : ℝ) (hTOV : 0 < M_TOV) (hCh : 0 < M_Ch)
    (hphys : (M_TOV / M_Ch) ^ 2
      = (finrank ℝ (ImSubmodule 3) : ℝ) / (finrank ℝ (ImSubmodule 2) : ℝ)) :
    M_TOV = M_Ch * Real.sqrt (7 / 3) := by
  -- Reduce the physical premise to the numeric identity (M_TOV/M_Ch)² = 7/3.
  rw [tov_dim_ratio] at hphys
  -- The ratio is nonnegative, so it equals √ of its own square.
  have hpos : 0 < M_TOV / M_Ch := div_pos hTOV hCh
  have hratio : M_TOV / M_Ch = Real.sqrt (7 / 3) := by
    rw [← Real.sqrt_sq hpos.le, hphys]
  -- Clear the division: `M_TOV = √(7/3) · M_Ch`.
  rw [div_eq_iff (ne_of_gt hCh)] at hratio
  rw [hratio]; ring

/-! ## 3. The bridge theorem — shared factor `dim(Im 𝕆) = 7`

`iron_to_ns_dim_im_octonion_link` (the canonical anchor theorem) packages the
two facts that share the imaginary-octonion dimension: the iron-56 factorisation
carries `dim(Im 𝕆)` as a factor, and the TOV mass ratio carries the SAME
`dim(Im 𝕆)` as its numerator.  The conjunction makes the shared dependence
explicit and non-vacuous (each conjunct is a genuine arithmetic / linear-algebra
statement about `finrank ℝ`). -/

/-- **Iron-56 → neutron-star bridge through `dim(Im 𝕆) = 7`.**
    Conjunction of the three load-bearing facts:
      1. `56 = dim(Im 𝕆) · dim 𝕆` (iron factorisation),
      2. `dim(Im 𝕆) / dim(Im ℍ) = 7/3` (the TOV mass-ratio-squared),
      3. `dim(Im 𝕆) = 7` — the SHARED factor appearing in both. -/
theorem iron_to_ns_dim_im_octonion_link :
    (56 : ℕ) = finrank ℝ (ImSubmodule 3) * finrank ℝ (CDAlg ℝ 3)
    ∧ (finrank ℝ (ImSubmodule 3) : ℝ) / (finrank ℝ (ImSubmodule 2) : ℝ) = 7 / 3
    ∧ finrank ℝ (ImSubmodule 3) = 7 :=
  ⟨iron_56_double_octet, tov_dim_ratio, dim_im_octonion⟩

/-! ## Completeness audit — `#print axioms` -/

#print axioms iron_56_double_octet
#print axioms dim_im_octonion
#print axioms dim_im_quaternion
#print axioms tov_dim_ratio
#print axioms tov_mass_sqrt_seven_thirds
#print axioms iron_to_ns_dim_im_octonion_link

end QBP.Cosmo.DenseMatter
