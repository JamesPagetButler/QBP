/-
  QBP.Foundations.ArtinTrace
  ==========================

  PR-C2b of the Artin strategy (`docs/foundations/artin-strategy-2026-06-06.md`,
  lemma L3).  The **trace / swap identity** for `CDAlg ℝ n`:

      x * y + y * x = (2 Re x) • y + (2 Re y) • x − (2 · ⟨x,y⟩) • 1

  where `Re x = x.coord 0` and `⟨x,y⟩ = bil x y = ∑ᵢ xᵢ yᵢ` is the polar form of
  the norm `N` (both from the merged `CDAlg` / `OctonionLaws`).  This is exactly
  the **polarization of quadraticity** `cdAlg_sq_eq`:

      x * x = (2 Re x) • x − N x • 1.

  Substituting `x → x + y`, expanding both sides by bilinearity of `*`, additivity
  of `Re`, and the polarization `N (x+y) = N x + N y + 2 ⟨x,y⟩`, then subtracting
  `x*x` and `y*y`, leaves precisely the swap identity.  **No `decide`, no basis
  enumeration, no `maxHeartbeats` bump** — the route is purely the algebra over the
  merged quadraticity lemma, valid for generic `n` (not just `n = 3`).

  Route note (reported for the record).  The strategy's §4 lemma table grades L3 as
  "M, bilinear → decide 8×8 + lift_bilinear_eq".  This file takes a cheaper route
  the strategy did not specify — polarization of the merged `cdAlg_sq_eq` — which
  needs no `decide`, generalizes in `n`, and reuses `cdAlg_sq_eq` + `bil` directly.
  (Deviation from the strategy's specified route, reported here per its own W1
  honest-route-attribution discipline; the orchestrator/reviewers ratified it.)  The pure-element specialization C2c's span-closure
  consumes (`x*y + y*x` for imaginary `x,y` collapsing to a scalar) is recovered as
  the corollary `cdAlg_mul_add_swap_pure` below.

  C2a-independence: this file imports `CDLifting` (which re-exports `CDAlg`) and
  `OctonionLaws` (merged; supplies `bil`), and does **NOT** import `ArtinCore`
  (PR #523, unmerged).  The strategy's claim that C2b ⟂ C2a held.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every result depends only on
  `{propext, Classical.choice, Quot.sound}`.
-/
import QBP.Foundations.CDLifting
import QBP.Foundations.OctonionLaws

namespace QBP.Foundations.CDAlg

variable {n : ℕ}

/-! ## 1. Additivity of `Re` and the polarization of `N`

`Re x = x.coord 0` is additive; the norm form `N` polarizes through `bil`. -/

/-- The real (scalar) part is additive: `Re (x + y) = Re x + Re y`. -/
theorem reCoord_add (x y : CDAlg ℝ n) : (x + y).coord 0 = x.coord 0 + y.coord 0 := by
  rw [add_coord]

/-- **Polarization of the norm form.**  `N (x + y) = N x + N y + 2 ⟨x,y⟩`, where
    `⟨x,y⟩ = bil x y`.  Immediate from `N = bil _ _` (diagonal of the polar form)
    and bilinearity + symmetry of `bil`. -/
theorem N_add (x y : CDAlg ℝ n) : N (x + y) = N x + N y + 2 * bil x y := by
  rw [N_eq_bil, N_eq_bil, N_eq_bil]
  rw [bil_add_left, bil_add_right, bil_add_right]
  have hsymm : bil y x = bil x y := by
    simp only [bil_def]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsymm]; ring

/-! ## 2. The trace / swap identity (L3)

The polarization of `cdAlg_sq_eq`.  Expand `(x + y) * (x + y)` two ways. -/

/-- Bilinear expansion of the square of a sum: `(x+y)(x+y) = xx + xy + yx + yy`. -/
theorem mul_self_add (x y : CDAlg ℝ n) :
    (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by
  rw [mul_add_left, mul_add_right, mul_add_right]; abel

/-- **L3 — the trace / swap identity.**  For all `x y : CDAlg ℝ n`,

      x * y + y * x = (2 Re x) • y + (2 Re y) • x − (2 ⟨x,y⟩) • 1,

    with `Re z = z.coord 0` and `⟨x,y⟩ = bil x y`.  This is the polarization of
    quadraticity (`cdAlg_sq_eq`): apply it to `x + y`, expand the square by
    bilinearity (`mul_self_add`), use additivity of `Re` (`reCoord_add`) and the
    norm polarization (`N_add`), then cancel the `x*x` and `y*y` quadratic terms.

    Statement form chosen so C2c can consume it for span-closure of
    `{1, x, y, x*y}`: the right-hand side lies in `span ℝ {1, x, y}` (no `x*y`
    term), so `y * x` is expressible from `x * y` modulo `span ℝ {1, x, y}` — the
    exact relation closure of the swapped product `y*x` needs. -/
theorem cdAlg_mul_add_swap (x y : CDAlg ℝ n) :
    x * y + y * x
      = (2 * x.coord 0) • y + (2 * y.coord 0) • x - (2 * bil x y) • (1 : CDAlg ℝ n) := by
  -- Quadraticity at x + y, expanded by bilinearity.
  have hsum : (x + y) * (x + y)
      = (2 * (x + y).coord 0) • (x + y) - (N (x + y)) • 1 := cdAlg_sq_eq (x + y)
  rw [mul_self_add] at hsum
  -- Quadraticity at x and y individually.
  have hx : x * x = (2 * x.coord 0) • x - (N x) • 1 := cdAlg_sq_eq x
  have hy : y * y = (2 * y.coord 0) • y - (N y) • 1 := cdAlg_sq_eq y
  -- Substitute the diagonal terms and the additive/polarized scalar pieces.
  rw [hx, hy, reCoord_add, N_add] at hsum
  -- `hsum` now reads, with `s := x*y + y*x` a single atom:
  --   ((2 x₀) • x - Nx • 1) + s + ((2 y₀) • y - Ny • 1)
  --     = (2 (x₀+y₀)) • (x+y) - (Nx • 1 + Ny • 1 + (2⟨x,y⟩) • 1)
  -- Solve for `s`: it equals (RHS) − (the two diagonal blocks), a pure module
  -- identity in the atoms {x, y, 1}.  Isolate, then discharge by `module`.
  have hs : x * y + y * x
      = ((2 * (x.coord 0 + y.coord 0)) • (x + y)
            - (N x + N y + 2 * bil x y) • (1 : CDAlg ℝ n))
        - ((2 * x.coord 0) • x - N x • 1) - ((2 * y.coord 0) • y - N y • 1) := by
    rw [← hsum]; abel
  rw [hs]; module

/-! ## 3. Pure-element specialization (the form C2c's span-closure consumes)

For *imaginary* (pure) `x, y` — `Re x = Re y = 0` — the swap identity collapses to a
single central scalar: `x * y + y * x = − (2 ⟨x,y⟩) • 1`.  This is the classical
"two imaginary octonions anticommute up to their inner product times 1" relation,
and is the central-scalar input W-J2 / risk-register flagged span-closure needs. -/

/-- **Pure-element swap identity.**  If `x` and `y` are imaginary (`Re = 0`), then
    `x * y + y * x = − (2 ⟨x,y⟩) • 1` — the swapped product is a central scalar.
    Specialization of `cdAlg_mul_add_swap` killing the two `Re` terms. -/
theorem cdAlg_mul_add_swap_pure (x y : CDAlg ℝ n)
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    x * y + y * x = - (2 * bil x y) • (1 : CDAlg ℝ n) := by
  rw [cdAlg_mul_add_swap, hx, hy]
  simp only [mul_zero, zero_smul, add_zero, neg_smul]
  abel

/-! ## 4. Completeness audit — `#print axioms` -/

#print axioms reCoord_add
#print axioms N_add
#print axioms mul_self_add
#print axioms cdAlg_mul_add_swap
#print axioms cdAlg_mul_add_swap_pure

end QBP.Foundations.CDAlg
