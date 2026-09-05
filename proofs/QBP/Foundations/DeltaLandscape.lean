import QBP.Foundations.CrossProduct
import QBP.Foundations.Alternator

/-!
# QBP.Foundations.DeltaLandscape — descent of the #629 δ-landscape

**Research-thread evidence for #473 AC1 v0.3 (PR #631), Propositions 6 and 7′**
(`docs/foundations/473-ac1-first-link-2026-09-04.md`).  This file is ordinary
`QBP.Foundations` material — pure `CDAlg`/ℝ algebra with no substrate semantics.
Per Prop 2 (Lean policy) it does **NOT** open `proofs/QBP/Substrate/`, and nothing
here authorises such a file.

## What is proved

**Prop 6 (T1) — the landscape potential descends to the G₂-invariants.**
For a sedenion `s : CDAlg ℝ 4` write `s = a + b·ℓ` in the Cayley–Dickson pair
split, `a = cdLo s`, `b = cdHi s` (both octonions, `CDAlg ℝ 3`).  The #629
landscape potential is `V(s) = δ² = ‖[a,b]‖² = N (a*b − b*a)`.  For **imaginary**
`s` (`s.coord 0 = 0`, hence `a.coord 0 = 0`), with `c := b − b₀·1` the imaginary
part of `b`:

    N (a*b − b*a)  =  4 · ( N a · N c  −  ⟨a, c⟩² )

so `V` is a function of the three G₂-invariants `(|a|², |Im b|², ⟨a, Im b⟩)` only
(equivalently, of `(|a|², b₀, ⟨a, Im b⟩)` on the unit sphere), and the #629
gradient flow descends to the 3-dimensional orbit space `S¹⁴/G₂` of Prop 5.

The proof is exactly the route named in the Prop 6 evidence column:
`[a,b] = [a,c] = 2 (a × c)` (the real part `b₀·1` is central) plus the 7-dimensional
Lagrange identity `‖a × c‖² = ‖a‖²‖c‖² − ⟨a,c⟩²` on `Im 𝕆`
(`CrossProduct.octonion_cross_norm_identity`).

**Numerical counterpart.** `analysis/473-dirac-probe/orbit_space.py`, check (3):
"max |delta^2 − 4(|a|²|Im b|² − ⟨a,Im b⟩²)| over 2000 Haar samples", residual
7·10⁻¹⁶.  That check is a numerical flashlight; `sedenion_landscape_descends`
below is the theorem it was pointing at.

**Prop 7′ (T2) — an order-3 rotation invariant quadratic form on ℝ² is scalar.**
The `S₃ ⇒ λ = 1, ν = 0` step of Prop 7′: the S₃ factor of `Aut(𝕊) = G₂ × S₃` acts
on the `(a, Im b)` plane by ±120° rotations, and a symmetric bilinear form on ℝ²
fixed by a 120° rotation is a multiple of the identity.  This cuts the G₂-invariant
family `|a|² + λ|Im b|² + μb₀² + ν⟨a, Im b⟩` down to `Q_μ = |a|² + |Im b|² + μ b₀²`.

## Completeness

Zero `sorry`, zero `native_decide`, zero vacuous `True`.  `#print axioms` audit at
the bottom: every result depends only on `{propext, Classical.choice, Quot.sound}`.
-/

namespace QBP.Foundations.DeltaLandscape

open QBP.Foundations.CDAlg

/-! ## 1. T1 — Prop 6: the δ-landscape descends to the G₂-invariants -/

/-- **Real multiples of `1` are central for the commutator.**  Subtracting
    `r • 1` from the right argument does not change the commutator:
    `[x, y − r•1] = [x, y]`.  (True at every Cayley–Dickson level and over any
    commutative base ring; `1` is a two-sided unit by `cd_mul_one`/`cd_one_mul`.) -/
theorem commutator_sub_central {R : Type*} [CommRing R] {n : ℕ}
    (r : R) (x y : CDAlg R n) :
    x * (y - r • (1 : CDAlg R n)) - (y - r • (1 : CDAlg R n)) * x = x * y - y * x := by
  have hsub : y - r • (1 : CDAlg R n) = y + (-r) • (1 : CDAlg R n) := by
    rw [neg_smul]; abel
  rw [hsub, mul_add_right, mul_add_left, mul_smul_right, mul_smul_left,
    cd_mul_one, cd_one_mul]
  abel

/-- The commutator is twice the cross product: `x*y − y*x = 2 • (x ×ₙ y)`,
    immediately from `cross x y = ½ (x*y − y*x)`. -/
theorem commutator_eq_two_smul_cross {n : ℕ} (x y : CDAlg ℝ n) :
    x * y - y * x = (2 : ℝ) • CrossProduct.cross x y := by
  rw [CrossProduct.cross_def, smul_smul, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_smul]

/-- **Octonion commutator norm (both arguments imaginary).**
    For pure `x y : CDAlg ℝ 3` (`x.coord 0 = y.coord 0 = 0`):

      `N (x*y − y*x) = 4 · (N x · N y − ⟨x,y⟩²)`.

    This is the workhorse behind Prop 6: `[x,y] = 2 (x × y)` and the 7-dimensional
    Lagrange identity for the cross product on `Im 𝕆`. -/
theorem octonion_commutator_norm (x y : CDAlg ℝ 3)
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    N (x * y - y * x) = 4 * (N x * N y - (bil x y) ^ 2) := by
  rw [commutator_eq_two_smul_cross, CrossProduct.N_smul,
    CrossProduct.octonion_cross_norm_identity x y hx hy]
  norm_num

/-- The imaginary part of an octonion is imaginary: `(y − y₀•1).coord 0 = 0`. -/
theorem im_coord_zero {n : ℕ} (y : CDAlg ℝ n) :
    (y - (y.coord 0) • (1 : CDAlg ℝ n)).coord 0 = 0 := by
  rw [sub_coord, smul_coord, one_coord, if_pos rfl, mul_one, sub_self]

/-- **Octonion commutator norm, second argument arbitrary.**
    For pure `x : CDAlg ℝ 3` and *any* `y : CDAlg ℝ 3`:

      `N (x*y − y*x) = 4 · (N x · N (Im y) − ⟨x, Im y⟩²)`,  `Im y := y − y₀·1`.

    The real part of `y` drops out because `y₀·1` is central
    (`commutator_sub_central`). -/
theorem octonion_commutator_norm_im (x y : CDAlg ℝ 3) (hx : x.coord 0 = 0) :
    N (x * y - y * x)
      = 4 * (N x * N (y - (y.coord 0) • (1 : CDAlg ℝ 3))
             - (bil x (y - (y.coord 0) • (1 : CDAlg ℝ 3))) ^ 2) := by
  have h := commutator_sub_central (y.coord 0) x y
  rw [← h]
  exact octonion_commutator_norm x _ hx (im_coord_zero y)

/-- **Prop 6 — descent of the #473/#629 δ-landscape.**

    For an *imaginary* sedenion `s : CDAlg ℝ 4` with Cayley–Dickson octonion
    components `a = cdLo s`, `b = cdHi s`, the landscape potential
    `V(s) = δ² = ‖[a,b]‖²` satisfies

      `N (a*b − b*a) = 4 · ( N a · N (b − b₀·1) − ⟨a, b − b₀·1⟩² )`

    i.e. `V` is a function of the three G₂-invariants `|a|², |Im b|², ⟨a, Im b⟩`
    alone.  Hence the #629 gradient flow of `V` descends to the 3-dimensional
    orbit space `S¹⁴/G₂` (Prop 5).  Numerical counterpart:
    `analysis/473-dirac-probe/orbit_space.py` check (3), residual 7·10⁻¹⁶. -/
theorem sedenion_landscape_descends (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    N (cdLo s * cdHi s - cdHi s * cdLo s)
      = 4 * (N (cdLo s) * N (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))
             - (bil (cdLo s)
                 (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))) ^ 2) := by
  have ha : (cdLo s).coord 0 = 0 := by rw [cdLo_coord, loIdx_zero, hs]
  exact octonion_commutator_norm_im (cdLo s) (cdHi s) ha

/-- `V(s) = ‖[a,b]‖² ≥ 0` — the landscape potential is nonnegative (the norm form
    on `CDAlg ℝ 3` is a sum of squares). -/
theorem sedenion_landscape_nonneg (s : CDAlg ℝ 4) :
    0 ≤ N (cdLo s * cdHi s - cdHi s * cdLo s) :=
  alt_N_nonneg _

/-- **Cauchy–Schwarz on the orbit-space coordinates.**  Combining Prop 6 with
    `sedenion_landscape_nonneg`: on imaginary sedenions the Gram determinant of
    `(a, Im b)` is nonnegative, `|a|²·|Im b|² ≥ ⟨a, Im b⟩²`.  (So the orbit-space
    coordinates of Prop 5 are constrained exactly as `V ≥ 0` demands.) -/
theorem sedenion_gram_nonneg (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    (bil (cdLo s) (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))) ^ 2
      ≤ N (cdLo s) * N (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)) := by
  have h := sedenion_landscape_descends s hs
  have hnn := sedenion_landscape_nonneg s
  rw [h] at hnn
  linarith

/-! ## 2. T2 — Prop 7′: an order-3 rotation invariant quadratic form on ℝ² is scalar

Let `R` be the rotation of ℝ² by 120°, `R = (c  −s ; s  c)` with
`c = cos 120° = −1/2`, `s = sin 120° = √3/2`.  For a symmetric form
`Q = (p  q ; q  r)`, the entries of `Rᵀ Q R` are

    (RᵀQR)₁₁ = c²p + 2cs·q + s²r ,
    (RᵀQR)₁₂ = −cs·p + (c² − s²)·q + cs·r ,
    (RᵀQR)₂₂ = s²p − 2cs·q + c²r ,

and with `c² = 1/4`, `s² = 3/4`, `cs = −√3/4`, `c² − s² = −1/2` these are the three
hypotheses below.  Invariance `Rᵀ Q R = Q` forces `q = 0` and `p = r`, i.e. `Q` is
scalar.

**Order 3 is essential.**  A rotation by 180° is `−I`, which acts trivially by
conjugation (`(−I)ᵀ Q (−I) = Q`) — an order-2 rotation constrains nothing, so it
would *not* suffice.  It is the order-3 element of `S₃` (the ±120° rotations of the
`(a, Im b)` plane, Prop 14) that kills the off-diagonal `ν` and equalises the
diagonal `λ`. -/

/-- **Prop 7′, the `S₃ ⇒ λ = 1, ν = 0` step.**  A symmetric bilinear form
    `Q = (p q ; q r)` on ℝ² invariant under conjugation by the 120° rotation
    is scalar: `q = 0` and `p = r`.

    Applied to the G₂-invariant family `|a|² + λ|Im b|² + μ b₀² + ν ⟨a, Im b⟩`
    restricted to the `(a, Im b)` plane, this gives `ν = 0` and `λ = 1`, leaving
    the one-parameter family `Q_μ = |a|² + |Im b|² + μ b₀²` of Prop 7′.

    All three components of `Rᵀ Q R = Q` are taken as hypotheses (that is what
    invariance says), but only two are independent: the `₂₂` equation is exactly
    the negative of the `₁₁` equation, because conjugation preserves the trace —
    see `rot120_h22_of_h11`.  Hence `_h22` is unused in the proof. -/
theorem rot120_invariant_form_scalar (p q r : ℝ)
    (h11 : (1/4) * p - (Real.sqrt 3 / 2) * q + (3/4) * r = p)
    (h12 : (Real.sqrt 3 / 4) * p - (1/2) * q - (Real.sqrt 3 / 4) * r = q)
    (_h22 : (3/4) * p + (Real.sqrt 3 / 2) * q + (1/4) * r = r) :
    q = 0 ∧ p = r := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- √3 · (h11) + 3 · (h12), reduced by √3² = 3, gives −6q = 0.
  have hq : q = 0 := by
    linear_combination (-(Real.sqrt 3) / 6) * h11 - (1/2) * h12 - (q/12) * h3
  refine ⟨hq, ?_⟩
  -- 4 · (h12) gives √3·(p − r) = 6q = 0, and √3 ≠ 0.
  have hmul : Real.sqrt 3 * (p - r) = 0 := by linear_combination 4 * h12 + 6 * hq
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hpos
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hne
  · linarith

/-- The `₂₂` component of `Rᵀ Q R = Q` is redundant: it is the negative of the `₁₁`
    component (conjugation by a rotation preserves the trace `p + r`). -/
theorem rot120_h22_of_h11 (p q r : ℝ)
    (h11 : (1/4) * p - (Real.sqrt 3 / 2) * q + (3/4) * r = p) :
    (3/4) * p + (Real.sqrt 3 / 2) * q + (1/4) * r = r := by
  linear_combination -h11

/-- **Order 2 would not suffice — constructed witness.**  Instantiating the generic
    conjugation formulas `(c²p + 2cs q + s²r, −cs p + (c²−s²) q + cs r,
    s²p − 2cs q + c²r)` at the 180° rotation (`c = −1`, `s = 0`, i.e. `R = −I`)
    gives back `(p, q, r)` identically, so *every* symmetric form is 180°-invariant.
    Witness that this is strictly weaker than the 120° condition: the form
    `(p, q, r) = (1, 1, 0)` is 180°-invariant yet has `q ≠ 0` and `p ≠ r`, so
    `rot120_invariant_form_scalar` genuinely uses order 3. -/
theorem rot180_admits_nonscalar :
    ∃ p q r : ℝ,
      ((-1 : ℝ) ^ 2 * p + 2 * (-1 : ℝ) * 0 * q + (0 : ℝ) ^ 2 * r = p
        ∧ -((-1 : ℝ) * 0) * p + ((-1 : ℝ) ^ 2 - (0 : ℝ) ^ 2) * q + (-1 : ℝ) * 0 * r = q
        ∧ (0 : ℝ) ^ 2 * p - 2 * (-1 : ℝ) * 0 * q + (-1 : ℝ) ^ 2 * r = r)
      ∧ q ≠ 0 ∧ p ≠ r :=
  ⟨1, 1, 0, ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-! ## 3. Axiom audit

Every theorem in this file must depend only on `{propext, Classical.choice,
Quot.sound}` — no `sorryAx`, no native-reduction axiom, no user axiom. -/

#print axioms commutator_sub_central
#print axioms commutator_eq_two_smul_cross
#print axioms octonion_commutator_norm
#print axioms im_coord_zero
#print axioms octonion_commutator_norm_im
#print axioms sedenion_landscape_descends
#print axioms sedenion_landscape_nonneg
#print axioms sedenion_gram_nonneg
#print axioms rot120_invariant_form_scalar
#print axioms rot120_h22_of_h11
#print axioms rot180_admits_nonscalar

end QBP.Foundations.DeltaLandscape
