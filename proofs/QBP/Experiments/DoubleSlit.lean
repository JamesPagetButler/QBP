/-
  Double-Slit Experiment (Experiment 03) - Formal Proofs

  Formalizes the QBP visibility derivation for the coupled quaternionic BPM model:
  - §1: Complex subspace & basis (ℂ ↪ ℍ, symplectic form)
  - §2: Quaternion algebra (j², j·z = z*·j)
  - §3: Coupling decomposition: (U₀ + U₁j)(ψ₀ + ψ₁j) expansion
  - §3b: Norm conservation via coupling cancellation
  - §4: Born rule (no cross-terms) + quatFraction η definition & bounds
  - §5: Visibility bounds (V ∈ [0,1])
  - §5b: V(η) bridge — the central QBP prediction: V = 1-η (Model A), V preserved (Model B)
  - §7: Complex subspace reduction (U₁ = 0 decouples → standard QM)
  - §8: Decay constant & monotonicity
  - §9: Edge cases & experimental scenario verification (A/B/C)

  Standard optics (Fraunhofer far-field) is in QBP.Optics.Fraunhofer.

  Ground Truth: research/03_double_slit_expected_results.md
  Analysis: analysis/03_double_slit/

  Strategy: Prove the algebraic identities; PDE solutions and numerical
  results stay in Python (empirical, tested by CI).
-/
import QBP.Basic

namespace QBP.Experiments.DoubleSlit

open QBP Real

-- TODO: Remove mkQ when Mathlib makes Quaternion an abbrev (or reducible).
-- Quaternion is a `def` (not `abbrev`), so anonymous constructors ⟨a,b,0,0⟩ : Q
-- elaborate to QuaternionAlgebra, breaking HMul Q Q resolution.
-- This helper ensures the result type is Q.
private abbrev mkQ (r i j k : ℝ) : Q := ⟨r, i, j, k⟩

/-! ## Section 1: Complex Subspace & Basis

The quaternionic wavefunction decomposes as ψ = ψ₀ + ψ₁j where ψ₀, ψ₁ ∈ ℂ.
We model ℂ as a subtype of ℍ (quaternions with imJ = imK = 0) and define
the quaternion unit j. -/

/-- The quaternion unit j, used to decompose ψ = ψ₀ + ψ₁j -/
noncomputable def qJ : Q := ⟨0, 0, 1, 0⟩

/-- A quaternion is "complex" if its j and k components are zero.
    This identifies ℂ ↪ ℍ via a + bi ↦ ⟨a, b, 0, 0⟩ -/
def isComplex (q : Q) : Prop := q.imJ = 0 ∧ q.imK = 0

/-- Complex quaternions satisfy the isComplex predicate by construction -/
theorem coeComplex_isComplex (a b : ℝ) : isComplex (⟨a, b, 0, 0⟩ : Q) := ⟨rfl, rfl⟩

/-- The symplectic form: decompose ψ = ψ₀ + ψ₁·j where ψ₀, ψ₁ are complex.
    Given complex components (re₀, im₀) and (re₁, im₁):
    ψ = ⟨re₀, im₀, re₁, im₁⟩

    This is because ⟨re₀, im₀, 0, 0⟩ + ⟨re₁, im₁, 0, 0⟩ * j
    = ⟨re₀, im₀, 0, 0⟩ + ⟨0, 0, re₁, im₁⟩
    = ⟨re₀, im₀, re₁, im₁⟩ -/
noncomputable def sympForm (re₀ im₀ re₁ im₁ : ℝ) : Q :=
  ⟨re₀, im₀, re₁, im₁⟩

/-! ## Section 2: Quaternion Algebra

The fundamental identities for quaternion j: j² = -1, and j commutes with
complex numbers by conjugation: j·z = z*·j where z* is complex conjugation. -/

/-- j² = -1 (fundamental quaternion identity) -/
theorem qJ_sq : qJ * qJ = -(1 : Q) := by
  unfold qJ
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-- j times a complex quaternion z = ⟨a, b, 0, 0⟩ gives ⟨0, 0, a, -b⟩.
    This is the quaternion representation of: j·z = z*·j
    where z* means complex conjugation (negating the i-component). -/
theorem j_mul_complex (a b : ℝ) :
    qJ * mkQ a b 0 0 = mkQ 0 0 a (-b) := by
  unfold qJ mkQ
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Complex quaternion times j: ⟨a, b, 0, 0⟩ * j = ⟨0, 0, a, b⟩.
    Note: z·j ≠ j·z in general (quaternions are non-commutative). -/
theorem complex_mul_j (a b : ℝ) :
    mkQ a b 0 0 * qJ = mkQ 0 0 a b := by
  unfold qJ mkQ
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Triple product j·z·j = -z* for complex z = a + bi.
    Note: this is NOT the conjugation action j·z·j⁻¹ = z* (which has an extra
    sign from j⁻¹ = -j). Here j·⟨a,b,0,0⟩·j = ⟨-a, b, 0, 0⟩ = -(a - bi) = -z*. -/
theorem j_complex_j (a b : ℝ) :
    qJ * mkQ a b 0 0 * qJ = mkQ (-a) b 0 0 := by
  rw [j_mul_complex]
  unfold qJ mkQ
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-! ## Section 3: Coupling Decomposition

The central theorem: expanding the quaternionic potential action
  (U₀ + U₁j)(ψ₀ + ψ₁j)
using the rule j·z = z*·j (where z* = complex conjugation) and j² = -1.

For real U₀, U₁ and complex ψ₀ = ⟨a₀, b₀, 0, 0⟩, ψ₁ = ⟨a₁, b₁, 0, 0⟩:
  Result = (U₀·ψ₀ - U₁·ψ₁*) + (U₀·ψ₁ + U₁·ψ₀*)·j

This is the algebraic engine of the coupled BPM equations.
The real and imaginary parts separate into two coupled complex equations. -/

/-- The full coupling decomposition for real potentials U₀, U₁ acting on
    a quaternionic wavefunction ψ₀ + ψ₁j.

    (U₀ + U₁j)(ψ₀ + ψ₁j)
    = U₀ψ₀ + U₀ψ₁j + U₁j·ψ₀ + U₁j·ψ₁j
    = U₀ψ₀ + U₀ψ₁j + U₁ψ₀*j + U₁ψ₁*j²    (using jz = z*j)
    = U₀ψ₀ + U₀ψ₁j + U₁ψ₀*j - U₁ψ₁*       (using j² = -1)
    = (U₀ψ₀ - U₁ψ₁*) + (U₀ψ₁ + U₁ψ₀*)j

    In components with ψ₀ = ⟨a₀, b₀⟩, ψ₁ = ⟨a₁, b₁⟩:
    Complex part 0: ⟨U₀a₀ - U₁a₁, U₀b₀ + U₁b₁⟩
    Complex part 1: ⟨U₀a₁ + U₁a₀, U₀b₁ - U₁b₀⟩

    The result quaternion is ⟨U₀a₀ - U₁a₁, U₀b₀ + U₁b₁, U₀a₁ + U₁a₀, U₀b₁ - U₁b₀⟩ -/
theorem coupling_decomposition (U₀ U₁ a₀ b₀ a₁ b₁ : ℝ) :
    let potential : Q := ⟨U₀, 0, U₁, 0⟩   -- U₀ + U₁j (real potentials)
    let psi : Q := ⟨a₀, b₀, a₁, b₁⟩        -- ψ₀ + ψ₁j
    potential * psi =
      ⟨U₀ * a₀ - U₁ * a₁,
       U₀ * b₀ + U₁ * b₁,
       U₀ * a₁ + U₁ * a₀,
       U₀ * b₁ - U₁ * b₀⟩ := by
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Coupling decomposition specialized to purely real ψ₀ and ψ₁.
    When b₀ = b₁ = 0: result = ⟨U₀a₀ - U₁a₁, 0, U₀a₁ + U₁a₀, 0⟩ -/
theorem coupling_decomposition_real (U₀ U₁ a₀ a₁ : ℝ) :
    let potential : Q := ⟨U₀, 0, U₁, 0⟩
    let psi : Q := ⟨a₀, 0, a₁, 0⟩
    potential * psi = ⟨U₀ * a₀ - U₁ * a₁, 0, U₀ * a₁ + U₁ * a₀, 0⟩ := by
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-! ## Section 3b: Norm Conservation (Coupling Cancellation)

The coupling terms in the BPM equations cancel algebraically in the norm
derivative. For the coupled equations:
  dψ₀/dz ~ -U₁·ψ₁*    (coupling into ψ₀)
  dψ₁/dz ~ +U₁·ψ₀*    (coupling into ψ₁)

The contribution to d/dz(|ψ₀|² + |ψ₁|²) from coupling is:
  Re(ψ₀* · (-U₁·ψ₁*)) + Re(ψ₁* · (U₁·ψ₀*)) = 0

This proves unitarity is algebraically guaranteed by the coupling structure.
The step-change in eta (outcome b) is redistribution, not leakage. -/

/-- The coupling terms cancel in the norm derivative.
    Given real U₁ and complex numbers ψ₀ = (a₀, b₀), ψ₁ = (a₁, b₁):

    term₀ = Re(ψ₀* · (-U₁·ψ₁*)) = -U₁(a₀a₁ + b₀b₁)
    term₁ = Re(ψ₁* · (U₁·ψ₀*))  = +U₁(a₁a₀ + b₁b₀)

    We compute: 2·Re(z) = z + z* for complex z, so the contribution is
    (term₀ + conj(term₀)) + (term₁ + conj(term₁)) = 0

    In the real formulation (which is what the BPM uses), this simplifies to:
    the coupling contribution to d/dt(a₀² + b₀² + a₁² + b₁²) vanishes. -/
theorem coupling_cancellation (U₁ a₀ b₀ a₁ b₁ : ℝ) :
    let coupling₀_re := -U₁ * a₁   -- coupling into Re(ψ₀): -U₁·Re(ψ₁*)
    let coupling₀_im := U₁ * b₁    -- coupling into Im(ψ₀): +U₁·Im(ψ₁*)  [conjugate]
    let coupling₁_re := U₁ * a₀    -- coupling into Re(ψ₁): +U₁·Re(ψ₀*)
    let coupling₁_im := -U₁ * b₀   -- coupling into Im(ψ₁): -U₁·Im(ψ₀*) [conjugate]
    -- d/dt(|ψ₀|² + |ψ₁|²) coupling contribution:
    -- = 2(a₀·coupling₀_re + b₀·coupling₀_im + a₁·coupling₁_re + b₁·coupling₁_im)
    2 * (a₀ * coupling₀_re + b₀ * coupling₀_im +
         a₁ * coupling₁_re + b₁ * coupling₁_im) = 0 := by
  ring

/-- Coupling cancellation, alternative formulation using complex inner product.
    ⟨ψ₀, -U₁·ψ₁*⟩ + ⟨ψ₁, U₁·ψ₀*⟩ = 0 where ⟨·,·⟩ = Re(z₁*z₂).
    This is the real part of: -U₁(a₀a₁ + b₀b₁) + U₁(a₁a₀ + b₁b₀) = 0 -/
theorem coupling_cancellation_inner (U₁ a₀ b₀ a₁ b₁ : ℝ) :
    let inner₀ := a₀ * (-U₁ * a₁) + b₀ * (U₁ * b₁)    -- Re(ψ₀* · (-U₁ψ₁*))
    let inner₁ := a₁ * (U₁ * a₀) + b₁ * (-U₁ * b₀)    -- Re(ψ₁* · (U₁ψ₀*))
    inner₀ + inner₁ = 0 := by
  ring

/-! ## Section 4: Born Rule for Symplectic Decomposition

The norm squared of ψ = ψ₀ + ψ₁j decomposes as |ψ|² = |ψ₀|² + |ψ₁|²
with NO cross-terms. This is because the complex and j-complex subspaces
are orthogonal in the quaternion norm. -/

/-- |ψ₀ + ψ₁j|² = |ψ₀|² + |ψ₁|² (no cross-terms in symplectic decomposition).
    For ψ = ⟨a₀, b₀, a₁, b₁⟩:
    |ψ|² = a₀² + b₀² + a₁² + b₁² = (a₀² + b₀²) + (a₁² + b₁²) = |ψ₀|² + |ψ₁|² -/
theorem normSq_sympForm (a₀ b₀ a₁ b₁ : ℝ) :
    (sympForm a₀ b₀ a₁ b₁).normSq =
    (a₀ ^ 2 + b₀ ^ 2) + (a₁ ^ 2 + b₁ ^ 2) := by
  unfold sympForm
  simp [Quaternion.normSq]
  ring

/-- When ψ₁ = 0 (complex wavefunction), the norm reduces to |ψ₀|² -/
theorem normSq_sympForm_zero_psi1 (a₀ b₀ : ℝ) :
    (sympForm a₀ b₀ 0 0).normSq = a₀ ^ 2 + b₀ ^ 2 := by
  rw [normSq_sympForm]
  ring

/-- Norm squared is non-negative (consequence of being sum of squares) -/
theorem normSq_sympForm_nonneg (a₀ b₀ a₁ b₁ : ℝ) :
    0 ≤ (sympForm a₀ b₀ a₁ b₁).normSq := by
  rw [normSq_sympForm]
  nlinarith [sq_nonneg a₀, sq_nonneg b₀, sq_nonneg a₁, sq_nonneg b₁]

/-- Quaternionic fraction: η = |ψ₁|² / (|ψ₀|² + |ψ₁|²).
    Measures how much of the wavefunction lives in the j-subspace.
    Defined here (after Born rule) for use in the V(η) bridge (Section 5b). -/
noncomputable def quatFraction (normSq0 normSq1 : ℝ) : ℝ :=
  normSq1 / (normSq0 + normSq1)

/-- Quaternionic fraction is non-negative when both norms are non-negative -/
theorem quatFraction_nonneg {n₀ n₁ : ℝ}
    (_h₀ : n₀ ≥ 0) (h₁ : n₁ ≥ 0) (hsum : n₀ + n₁ > 0) :
    quatFraction n₀ n₁ ≥ 0 := by
  unfold quatFraction
  exact div_nonneg h₁.le (le_of_lt hsum)

/-- Quaternionic fraction is at most 1 -/
theorem quatFraction_le_one {n₀ n₁ : ℝ}
    (h₀ : n₀ ≥ 0) (_h₁ : n₁ ≥ 0) (hsum : n₀ + n₁ > 0) :
    quatFraction n₀ n₁ ≤ 1 := by
  unfold quatFraction
  rw [div_le_one hsum]
  linarith

/-- η = 0 iff ψ₁ = 0 (pure complex wavefunction) -/
theorem quatFraction_zero_iff {n₀ n₁ : ℝ}
    (h₀ : n₀ > 0) (h₁ : n₁ ≥ 0) :
    quatFraction n₀ n₁ = 0 ↔ n₁ = 0 := by
  unfold quatFraction
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · linarith
  · intro h
    left; exact h

/-! ## Section 5: Visibility Bounds

Visibility V = (Imax - Imin)/(Imax + Imin) measures fringe contrast.
We prove 0 ≤ V ≤ 1 and characterize the extremes. -/

/-- Visibility definition: V = (Imax - Imin) / (Imax + Imin) -/
noncomputable def visibility (Imax Imin : ℝ) : ℝ :=
  (Imax - Imin) / (Imax + Imin)

/-- Visibility is non-negative when Imax ≥ Imin ≥ 0 and Imax > 0 -/
theorem visibility_nonneg {Imax Imin : ℝ}
    (hge : Imax ≥ Imin) (hmin : Imin ≥ 0) (hmax : Imax > 0) :
    visibility Imax Imin ≥ 0 := by
  unfold visibility
  apply div_nonneg
  · linarith
  · linarith

/-- Visibility is at most 1 when Imax ≥ Imin ≥ 0 and Imax > 0 -/
theorem visibility_le_one {Imax Imin : ℝ}
    (_hge : Imax ≥ Imin) (hmin : Imin ≥ 0) (hmax : Imax > 0) :
    visibility Imax Imin ≤ 1 := by
  unfold visibility
  rw [div_le_one (by linarith : Imax + Imin > 0)]
  linarith

/-- Full visibility (V = 1) when Imin = 0 and Imax > 0 (perfect interference) -/
theorem visibility_one {Imax : ℝ} (hmax : Imax > 0) :
    visibility Imax 0 = 1 := by
  unfold visibility
  simp
  exact ne_of_gt hmax

/-- Zero visibility (V = 0) when Imax = Imin > 0 (no interference, which-path) -/
theorem visibility_zero {I : ℝ} (_hI : I > 0) :
    visibility I I = 0 := by
  unfold visibility
  simp

/-! ## Section 5b: Visibility–Eta Bridge (QBP Prediction)

The central QBP observational prediction: the quaternionic fraction η
determines the observable fringe visibility V.

The Born rule (Section 4) proves |ψ|² = |ψ₀|² + |ψ₁|² with NO cross-terms.
This means the j-component contributes independently to the total intensity.

**Model A (incoherent j-component):** If ψ₁ has no spatial fringe structure
(flat background), the total intensity is I(x) = I_coh(x) + I_inc.
For perfect coherent fringes: I_max = 2·A + B, I_min = B, where A is the
spatial average of |ψ₀|² and B = |ψ₁|² (uniform).
The visibility degrades: **V = 1 - η** where η = quatFraction(A, B).

**Model B (correlated j-component):** If ψ₁ carries the same fringe pattern
as ψ₀ (e.g., spatially uniform coupling U₁), then I(x) scales uniformly
and visibility is preserved: **V = V₀** regardless of η.

Which model applies depends on the measurement and coupling geometry.
The experiment selection (research issue) determines the physical case. -/

/-- Model A: Incoherent j-component as spatially flat background.
    Assumes ψ₁ is approximately uniform across the fringe pattern — i.e.,
    ψ₁ varies slowly compared to the ψ₀ interference frequency.

    When ψ₀ interferes perfectly (I_max_coh = 2·n₀, I_min_coh = 0) and
    ψ₁ adds flat background n₁, the observed visibility equals 1 - η
    where η = quatFraction(n₀, n₁).

    Derivation:
      I_max = 2·n₀ + n₁, I_min = n₁
      V = (I_max - I_min)/(I_max + I_min) = 2·n₀/(2·n₀ + 2·n₁) = n₀/(n₀ + n₁)
      η = n₁/(n₀ + n₁)
      V = 1 - η  ∎ -/
theorem visibility_eq_one_sub_quatFraction {n₀ n₁ : ℝ}
    (h₀ : n₀ > 0) (h₁ : n₁ ≥ 0) :
    visibility (2 * n₀ + n₁) n₁ = 1 - quatFraction n₀ n₁ := by
  unfold visibility quatFraction
  have hsum : n₀ + n₁ ≠ 0 := ne_of_gt (by linarith : n₀ + n₁ > 0)
  have hdenom : 2 * n₀ + n₁ + n₁ ≠ 0 := ne_of_gt (by linarith : 2 * n₀ + n₁ + n₁ > 0)
  field_simp
  ring

/-- Model A corollary: When η = 0 (no j-component), visibility is perfect.
    This recovers the standard QM result as a special case of QBP. -/
theorem visibility_eta_zero {n₀ : ℝ} (h₀ : n₀ > 0) :
    visibility (2 * n₀ + 0) 0 = 1 - quatFraction n₀ 0 := by
  exact visibility_eq_one_sub_quatFraction h₀ (le_refl 0)

/-- Model A corollary: η = 0 gives V = 1 (perfect fringes).
    The complementary perspective of visibility_eta_zero: that theorem shows
    the visibility formula evaluates to 1-η; this one shows 1-η = 1 when η = 0. -/
theorem visibility_full_when_eta_zero {n₀ : ℝ} (_h₀ : n₀ > 0) :
    1 - quatFraction n₀ 0 = 1 := by
  unfold quatFraction
  simp

/-- Model A: Visibility is anti-monotone in background intensity.
    More j-component background means less visible fringes. -/
theorem visibility_antitone_background {n₀ B₁ B₂ : ℝ}
    (h₀ : n₀ > 0) (hB₁ : B₁ ≥ 0) (_hB₂ : B₂ ≥ 0) (hle : B₁ ≤ B₂) :
    visibility (2 * n₀ + B₂) B₂ ≤ visibility (2 * n₀ + B₁) B₁ := by
  unfold visibility
  -- After simplification: 2n₀/(2n₀ + 2B₂) ≤ 2n₀/(2n₀ + 2B₁)
  -- Larger denominator = smaller fraction (both numerators simplify to 2n₀)
  have hs₁ : 2 * n₀ + B₁ - B₁ = 2 * n₀ := by ring
  have hs₂ : 2 * n₀ + B₂ - B₂ = 2 * n₀ := by ring
  rw [hs₁, hs₂]
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

/-- Model B: Correlated spatial structure preserves visibility.
    When both ψ₀ and ψ₁ carry the same fringe pattern (spatially uniform
    coupling), the total intensity scales uniformly: I(x) = (1+r)·I₀(x).
    The scaling factor cancels in the visibility ratio. -/
theorem visibility_correlated {Imax Imin : ℝ} {r : ℝ}
    (_hge : Imax ≥ Imin) (hmin : Imin ≥ 0) (hmax : Imax > 0) (hr : r > -1) :
    visibility ((1 + r) * Imax) ((1 + r) * Imin) = visibility Imax Imin := by
  unfold visibility
  have h1r : (1 : ℝ) + r > 0 := by linarith
  have hIsum : Imax + Imin > 0 := by linarith
  have hscaled : (1 + r) * Imax + (1 + r) * Imin > 0 := by nlinarith
  -- field_simp uses these nonzero proofs from the local context automatically
  have hIsum_ne : Imax + Imin ≠ 0 := ne_of_gt hIsum
  have hscaled_ne : (1 + r) * Imax + (1 + r) * Imin ≠ 0 := ne_of_gt hscaled
  field_simp

/-! ## Section 7: Complex Subspace Reduction
-- Note: §6 (Fraunhofer far-field) extracted to QBP.Optics.Fraunhofer

When U₁ = 0 (no quaternionic coupling), the system decouples:
the ψ₀ and ψ₁ equations become independent Schrödinger equations. -/

/-- When U₁ = 0, the coupling decomposition reduces to U₀ acting on each
    component independently: (U₀ + 0·j)(ψ₀ + ψ₁j) = U₀·ψ₀ + U₀·ψ₁·j -/
theorem coupling_decouples_U1_zero (U₀ a₀ b₀ a₁ b₁ : ℝ) :
    let potential : Q := ⟨U₀, 0, 0, 0⟩   -- U₀ + 0·j
    let psi : Q := ⟨a₀, b₀, a₁, b₁⟩
    potential * psi = ⟨U₀ * a₀, U₀ * b₀, U₀ * a₁, U₀ * b₁⟩ := by
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
                Quaternion.imJ_mul, Quaternion.imK_mul]

/-- The symplectic form with ψ₁ = 0 is a complex wavefunction -/
theorem sympForm_zero_psi1 (a₀ b₀ : ℝ) :
    isComplex (sympForm a₀ b₀ 0 0) := by
  unfold sympForm isComplex
  exact ⟨rfl, rfl⟩

/-! ## Section 8: Decay Constant

The decay constant κ controls how quickly interference is lost with
increasing quaternionic coupling U₁. The quatFraction η definition
and bounds are in Section 4 (near the Born rule). -/

/-- Dimensionless coupling proxy: product of potential strength and slit separation.
    This is a simplified stand-in used for monotonicity and positivity proofs.
    The physical decay constant κ = |U₁|/(ℏv) [m⁻¹] from the ground truth
    has different dimensions; the full dimensional formula lives in the Python
    simulation (Phase 2), not in this algebraic skeleton. -/
noncomputable def decayConstant (U₁ d : ℝ) : ℝ := U₁ * d

/-- Decay length: L_decay = 1/κ (distance over which visibility drops by 1/e) -/
noncomputable def decayLength (κ : ℝ) : ℝ := 1 / κ

/-- Decay constant is positive for positive U₁ and positive d -/
theorem decayConstant_pos {U₁ d : ℝ} (hU₁ : U₁ > 0) (hd : d > 0) :
    decayConstant U₁ d > 0 := by
  unfold decayConstant
  exact mul_pos hU₁ hd

/-- Decay length is positive for positive κ -/
theorem decayLength_pos {κ : ℝ} (hκ : κ > 0) :
    decayLength κ > 0 := by
  unfold decayLength
  exact div_pos one_pos hκ

/-- Increasing U₁ increases the decay constant (faster decoherence) -/
theorem decayConstant_mono_U1 {U₁ U₁' d : ℝ}
    (hd : d > 0) (h : U₁ < U₁') :
    decayConstant U₁ d < decayConstant U₁' d := by
  unfold decayConstant
  exact mul_lt_mul_of_pos_right h hd

/-! ## Section 9: Edge Cases & Consistency

Verify that the formalism reproduces the three experimental scenarios:
  A: Baseline (no coupling, U₁=0) → V = 1
  B: Which-path (full coupling) → V = 0
  C: Post-measurement recovery → matches A at detector -/

/-- Scenario A (baseline): When Imin = 0, we get perfect visibility V = 1.
    Physically: no quaternionic coupling, standard double-slit. -/
theorem scenarioA_visibility {I₀ : ℝ} (hI₀ : I₀ > 0) :
    visibility I₀ 0 = 1 :=
  visibility_one hI₀

/-- Scenario B (which-path): When Imax = Imin, visibility V = 0.
    Physically: full quaternionic coupling destroys interference. -/
theorem scenarioB_visibility {I : ℝ} (hI : I > 0) :
    visibility I I = 0 :=
  visibility_zero hI

/-- Scenario C post-measurement recovery: when ψ₁ = 0 (measurement projects
    to complex subspace), the quaternionic fraction η = 0, and the system
    reduces to scenario A. -/
theorem scenarioC_matches_scenarioA_at_detector {n₀ : ℝ} (hn₀ : n₀ > 0) :
    quatFraction n₀ 0 = 0 := by
  rw [quatFraction_zero_iff hn₀ (le_refl 0)]

end QBP.Experiments.DoubleSlit
