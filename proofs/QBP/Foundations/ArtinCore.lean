import QBP.Foundations.CDLifting
import QBP.Foundations.CDBridge
import QBP.Foundations.OctonionLaws

/-!
# QBP.Foundations.ArtinCore — Artin de-risk core (PR-C2a)

**Scope (truth-in-labelling).** This file does **NOT** prove Artin's theorem.
It delivers the *core lemmas* on which the ratified Artin route
(`docs/foundations/artin-strategy-2026-06-06.md`, chunk C2a) pivots:

  * `assoc_one_left` / `assoc_one_mid` / `assoc_one_right` (**L1**) — the
    associator vanishes whenever any slot is `1`.
  * `assoc_xy_survivor` (**L2, the de-risk gate**) — `assoc x y (x*y) = 0` for all
    `x y : CDAlg ℝ 3`, proven **from the merged alternativity lemmas alone**
    (no Moufang, no quadraticity, no Hurwitz classification).  This is the single
    load-bearing synthetic lemma identified by the counter-team (Jaynes J2); the
    whole route was gated on it closing in-kernel, which it does (this file).
  * `trilinear_vanish_on_span` — a reusable lift: an `R`-trilinear map vanishing
    on every triple drawn from a spanning **set** vanishes on the whole span.
  * `assoc_span4` — the C2a specialization: `assoc` vanishes on `span ℝ {1,x,y,x*y}`
    once it vanishes on the 64 generator triples over `{1, x, y, x*y}`.
  * `assoc_gen4_zero` — the **complete** generator-triple discharge: ALL 64 triples
    `assoc a b c` with `a,b,c ∈ {1, x, y, x*y}` vanish.  **Finding (deviates from
    the strategy's estimate):** the strategy expected ~60 to close easily and a
    hard remainder needing the `x*y + y*x` trace identity (C2b).  In fact the
    remainder is exactly the 6 *flexor* triples `assoc a b a` (a,b ∈ {x,y,x*y}),
    which all die by **flexibility** (`assoc_diag_flex`, an independent ✓-cell law,
    NOT the Moufang block).  So 64/64 close from L1 + alternativity-diag + L2 +
    flexibility — **no trace identity required**.  See the ESCALATE note in the
    docstring of `assoc_gen4_zero`: this may collapse the C2b/C2c/C2d hard path.

Nothing here claims associativity of the 2-generated subalgebra; that is C2d
(`octonion_artin`), which still needs `span ℝ {1,x,y,x*y}` proven multiplicatively
closed (`adjoin ℝ {x,y} ≤ span`).  This file delivers the trilinear-side reduction
(`assoc_span4` + `assoc_gen4_zero`) only.  See the strategy doc for the chunking.

Infra reused (all merged, kernel-checked, axioms ⊆ {propext, Classical.choice,
Quot.sound}): `CDLifting.assoc`, `assoc_trilinear`, `octonion_alternative`,
`assoc_diag_left`, `assoc_diag_right`, `octonion_{left,right}_alternative_polarized`;
`CDBridge.cdAlg_one_mul`, `cdAlg_mul_one`.
-/

namespace QBP.Foundations.CDAlg

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ## L1 — the associator vanishes when a slot is `1` -/

/-- **L1 (left).** `assoc 1 y z = 0`: `1` associates in the first slot.
    `(1*y)*z − 1*(y*z) = (y*z) − (y*z) = 0` via the unit laws. -/
theorem assoc_one_left (y z : CDAlg R n) : assoc (1 : CDAlg R n) y z = 0 := by
  simp only [assoc, cdAlg_one_mul, sub_self]

/-- **L1 (mid).** `assoc x 1 z = 0`: `(x*1)*z − x*(1*z) = x*z − x*z = 0`. -/
theorem assoc_one_mid (x z : CDAlg R n) : assoc x (1 : CDAlg R n) z = 0 := by
  simp only [assoc, cdAlg_mul_one, cdAlg_one_mul, sub_self]

/-- **L1 (right).** `assoc x y 1 = 0`: `(x*y)*1 − x*(y*1) = x*y − x*y = 0`. -/
theorem assoc_one_right (x y : CDAlg R n) : assoc x y (1 : CDAlg R n) = 0 := by
  simp only [assoc, cdAlg_mul_one, sub_self]

/-! ## L2 — the survivor `assoc x y (x*y) = 0` (the de-risk gate)

Synthetic proof from alternativity alone, following the counter-team's J2 chain.
We first kill `assoc x (x*y) y` (the slots-2,3-swapped form), then transport to
`assoc x y (x*y)` via polarized right-alternativity. -/

/-- Helper for L2: `assoc x (x*y) y = 0` for all `x y : CDAlg ℝ 3`.
    Both `((x*x)*y)*y` and `x*(x*(y*y))` reduce — by left/right alternativity —
    to the common value `(x*x)*(y*y)`, so their difference is `0`. -/
theorem assoc_x_xy_y (x y : CDAlg ℝ 3) : assoc x (x * y) y = 0 := by
  -- Unfold the associator.
  rw [assoc]
  -- Left-alternativity: x*(x*y) = (x*x)*y.
  have hL : x * (x * y) = (x * x) * y := (octonion_alternative x y).1.symm
  -- Right-alternativity: (x*y)*y = x*(y*y).
  have hR : (x * y) * y = x * (y * y) := (octonion_alternative x y).2
  rw [hL, hR]
  -- Goal: ((x*x)*y)*y − x*(x*(y*y)) = 0.
  -- Right-diag alternativity at (x*x): ((x*x)*y)*y = (x*x)*(y*y).
  have h1 : ((x * x) * y) * y = (x * x) * (y * y) := by
    have := assoc_diag_right (x * x) y
    rwa [assoc, sub_eq_zero] at this
  -- Left-diag alternativity at (x, y*y): (x*x)*(y*y) = x*(x*(y*y)).
  have h2 : (x * x) * (y * y) = x * (x * (y * y)) := by
    have := assoc_diag_left x (y * y)
    rwa [assoc, sub_eq_zero] at this
  rw [h1, h2, sub_self]

/-- **L2 — THE DE-RISK GATE.** `assoc x y (x*y) = 0` for all `x y : CDAlg ℝ 3`.

    This is the single irreducible survivor of the 64 generator-triple associators
    in the Artin route.  Proven **from the merged alternativity lemmas alone**:
    polarized right-alternativity gives `assoc x y (x*y) = − assoc x (x*y) y`, and
    `assoc x (x*y) y = 0` (`assoc_x_xy_y`).  No Moufang, no quadraticity, no
    classification — confirming the strategy's claim that C2 ⟂ the Moufang block. -/
theorem assoc_xy_survivor (x y : CDAlg ℝ 3) : assoc x y (x * y) = 0 := by
  -- Polarized right-alternativity in slots 2,3: assoc x y (x*y) + assoc x (x*y) y = 0.
  have hpol : assoc x y (x * y) + assoc x (x * y) y = 0 :=
    octonion_right_alternative_polarized x y (x * y)
  rw [assoc_x_xy_y x y, add_zero] at hpol
  exact hpol

/-! ## The reusable span-lifting lemma

A trilinear map vanishing on every triple from a spanning **set** vanishes on the
whole span.  Proven by three sequential single-slot `Submodule.span_induction`
applications: each slot's vanishing-set is a submodule (closed under `+`, `•`, `0`
by trilinearity) containing the generators.  This is the span-version of the
basis-lift argument in `CDLifting`, specialized to a finite generating family. -/

/-- **Span-lifting (reusable).** If `T` is `R`-trilinear and vanishes on every
    triple `(a,b,c)` with `a,b,c ∈ s`, then `T x y z = 0` for all `x y z` in
    `Submodule.span R s`. -/
theorem trilinear_vanish_on_span
    {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsTrilinear T) {s : Set (CDAlg R n)}
    (hgen : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, T a b c = 0)
    {x y z : CDAlg R n}
    (hx : x ∈ Submodule.span R s) (hy : y ∈ Submodule.span R s)
    (hz : z ∈ Submodule.span R s) :
    T x y z = 0 := by
  -- Slot 1: induct on x, with y z fixed in the span.
  induction hx using Submodule.span_induction with
  | mem a ha =>
    -- Now reduce slot 2: induct on y.
    induction hy using Submodule.span_induction with
    | mem b hb =>
      -- Slot 3: induct on z.
      induction hz using Submodule.span_induction with
      | mem c hc => exact hgen a ha b hb c hc
      | zero =>
        have := hT.smul_right (0 : R) a b 0
        simpa using this
      | add z₁ z₂ _ _ ih₁ ih₂ => rw [hT.add_right, ih₁, ih₂, add_zero]
      | smul r z₁ _ ih => rw [hT.smul_right, ih, smul_zero]
    | zero =>
      have := hT.smul_mid (0 : R) a 0 z
      simpa using this
    | add y₁ y₂ _ _ ih₁ ih₂ => rw [hT.add_mid, ih₁, ih₂, add_zero]
    | smul r y₁ _ ih => rw [hT.smul_mid, ih, smul_zero]
  | zero =>
    have := hT.smul_left (0 : R) 0 y z
    simpa using this
  | add x₁ x₂ _ _ ih₁ ih₂ => rw [hT.add_left, ih₁, ih₂, add_zero]
  | smul r x₁ _ ih => rw [hT.smul_left, ih, smul_zero]

/-! ## `assoc_span4` — vanishing of `assoc` on `span ℝ {1, x, y, x*y}`

The C2a specialization of the span-lift: if `assoc` vanishes on the 64 generator
triples over the 4-element family `{1, x, y, x*y}`, it vanishes on the whole span.
This is the reduction the Artin assembly (C2d) needs; C2a delivers it parametrized
on the generator-triple hypothesis so it composes once the remaining triples land
(C2b/C2c provide the trace identity that closes the OPEN triples). -/

/-- The 4-element generating family `{1, x, y, x*y}` as a `Set`. -/
def gen4 (x y : CDAlg R n) : Set (CDAlg R n) := {1, x, y, x * y}

/-- **`assoc_span4`.** If `assoc` vanishes on every triple drawn from
    `{1, x, y, x*y}`, then `assoc u v w = 0` for all `u v w ∈ span ℝ {1,x,y,x*y}`.
    Pure trilinear lift via `trilinear_vanish_on_span` + `assoc_trilinear`. -/
theorem assoc_span4 (x y : CDAlg ℝ 3)
    (hgen : ∀ a ∈ gen4 x y, ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y,
      assoc a b c = 0)
    {u v w : CDAlg ℝ 3}
    (hu : u ∈ Submodule.span ℝ (gen4 x y)) (hv : v ∈ Submodule.span ℝ (gen4 x y))
    (hw : w ∈ Submodule.span ℝ (gen4 x y)) :
    assoc u v w = 0 :=
  trilinear_vanish_on_span assoc_trilinear hgen hu hv hw

/-! ## L2-symmetric survivors closed without the trace identity -/

/-- L2-symmetry: `assoc y x (x*y) = 0`.  Polarized left-alternativity gives
    `assoc x y (x*y) + assoc y x (x*y) = 0`, then L2. -/
theorem assoc_yx_survivor (x y : CDAlg ℝ 3) : assoc y x (x * y) = 0 := by
  have hpol : assoc x y (x * y) + assoc y x (x * y) = 0 :=
    octonion_left_alternative_polarized x y (x * y)
  rw [assoc_xy_survivor x y, zero_add] at hpol
  exact hpol

/-- L2-symmetry: `assoc (x*y) x y = 0`.  Polarized left-alternativity in slots
    1,2 on `assoc x (x*y) y` gives `assoc x (x*y) y + assoc (x*y) x y = 0`, then
    `assoc_x_xy_y`. -/
theorem assoc_xy_x_y (x y : CDAlg ℝ 3) : assoc (x * y) x y = 0 := by
  have hpol : assoc x (x * y) y + assoc (x * y) x y = 0 :=
    octonion_left_alternative_polarized x (x * y) y
  rw [assoc_x_xy_y x y, zero_add] at hpol
  exact hpol

/-- L2-symmetry: `assoc (x*y) y x = 0`.  Polarized right-alternativity in slots
    2,3 on `assoc (x*y) x y` gives `assoc (x*y) x y + assoc (x*y) y x = 0`, then
    `assoc_xy_x_y`. -/
theorem assoc_xy_y_x (x y : CDAlg ℝ 3) : assoc (x * y) y x = 0 := by
  have hpol : assoc (x * y) x y + assoc (x * y) y x = 0 :=
    octonion_right_alternative_polarized (x * y) x y
  rw [assoc_xy_x_y x y, zero_add] at hpol
  exact hpol

/-- L2-symmetry: `assoc y (x*y) x = 0`.  Polarized right-alternativity in slots
    2,3 on `assoc y x (x*y)` gives `assoc y x (x*y) + assoc y (x*y) x = 0`, then
    `assoc_yx_survivor`. -/
theorem assoc_y_xy_x (x y : CDAlg ℝ 3) : assoc y (x * y) x = 0 := by
  have hpol : assoc y x (x * y) + assoc y (x * y) x = 0 :=
    octonion_right_alternative_polarized y x (x * y)
  rw [assoc_yx_survivor x y, zero_add] at hpol
  exact hpol

/-! ## Complete generator-triple discharge (64 of 64)

Split by the first slot's value into four 16-leaf helpers so each elaboration unit
stays within the default heartbeat budget (no bump, no `native_decide`).  Each leaf
closes by exactly one of: L1 (`assoc_one_*`), alternating-diag (`assoc_diag_left/right`),
flexibility (`assoc_diag_flex`, outer slots equal), or the L2 family. -/

/-- First slot `= 1`: all 16 triples die by L1-left. -/
private theorem assoc_gen4_inner_one (x y : CDAlg ℝ 3) :
    ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y, assoc (1 : CDAlg ℝ 3) b c = 0 := by
  intro b _ c _; exact assoc_one_left b c

/-- First slot `= x`: the 16 triples `assoc x b c`, `b,c ∈ {1,x,y,x*y}`.  Each leaf
    is closed by an explicitly-applied lemma (no `first`/unification search, so the
    default heartbeat budget suffices). -/
private theorem assoc_gen4_inner_x (x y : CDAlg ℝ 3) :
    ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y, assoc x b c = 0 := by
  intro b hb c hc
  simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
  -- Rewrite `b`,`c` to their values via `rw [hb, hc]` (LHS→RHS only, so `x`,`y`
  -- are never eliminated), then close each leaf with an explicitly-applied lemma.
  rcases hb with hb | hb | hb | hb
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_mid (x) (1)
    · rw [hb, hc]; exact assoc_one_mid (x) (x)
    · rw [hb, hc]; exact assoc_one_mid (x) (y)
    · rw [hb, hc]; exact assoc_one_mid (x) (x * y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x) (x)
    · rw [hb, hc]; exact assoc_diag_left (x) (x)
    · rw [hb, hc]; exact assoc_diag_left (x) (y)
    · rw [hb, hc]; exact assoc_diag_left (x) (x * y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x) (y)
    · rw [hb, hc]; exact assoc_diag_flex (x) (y)
    · rw [hb, hc]; exact assoc_diag_right (x) (y)
    · rw [hb, hc]; exact assoc_xy_survivor x y
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x) (x * y)
    · rw [hb, hc]; exact assoc_diag_flex (x) (x * y)
    · rw [hb, hc]; exact assoc_x_xy_y x y
    · rw [hb, hc]; exact assoc_diag_right (x) (x * y)

/-- First slot `= y`: the 16 triples `assoc y b c`. -/
private theorem assoc_gen4_inner_y (x y : CDAlg ℝ 3) :
    ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y, assoc y b c = 0 := by
  intro b hb c hc
  simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
  rcases hb with hb | hb | hb | hb
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_mid (y) (1)
    · rw [hb, hc]; exact assoc_one_mid (y) (x)
    · rw [hb, hc]; exact assoc_one_mid (y) (y)
    · rw [hb, hc]; exact assoc_one_mid (y) (x * y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (y) (x)
    · rw [hb, hc]; exact assoc_diag_right (y) (x)
    · rw [hb, hc]; exact assoc_diag_flex (y) (x)
    · rw [hb, hc]; exact assoc_yx_survivor x y
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (y) (y)
    · rw [hb, hc]; exact assoc_diag_left (y) (x)
    · rw [hb, hc]; exact assoc_diag_left (y) (y)
    · rw [hb, hc]; exact assoc_diag_left (y) (x * y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (y) (x * y)
    · rw [hb, hc]; exact assoc_y_xy_x x y
    · rw [hb, hc]; exact assoc_diag_flex (y) (x * y)
    · rw [hb, hc]; exact assoc_diag_right (y) (x * y)

/-- First slot `= x*y`: the 16 triples `assoc (x*y) b c`. -/
private theorem assoc_gen4_inner_xy (x y : CDAlg ℝ 3) :
    ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y, assoc (x * y) b c = 0 := by
  intro b hb c hc
  simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
  rcases hb with hb | hb | hb | hb
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_mid (x * y) (1)
    · rw [hb, hc]; exact assoc_one_mid (x * y) (x)
    · rw [hb, hc]; exact assoc_one_mid (x * y) (y)
    · rw [hb, hc]; exact assoc_one_mid (x * y) (x * y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x * y) (x)
    · rw [hb, hc]; exact assoc_diag_right (x * y) (x)
    · rw [hb, hc]; exact assoc_xy_x_y x y
    · rw [hb, hc]; exact assoc_diag_flex (x * y) (x)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x * y) (y)
    · rw [hb, hc]; exact assoc_xy_y_x x y
    · rw [hb, hc]; exact assoc_diag_right (x * y) (y)
    · rw [hb, hc]; exact assoc_diag_flex (x * y) (y)
  · rcases hc with hc | hc | hc | hc
    · rw [hb, hc]; exact assoc_one_right (x * y) (x * y)
    · rw [hb, hc]; exact assoc_diag_left (x * y) (x)
    · rw [hb, hc]; exact assoc_diag_left (x * y) (y)
    · rw [hb, hc]; exact assoc_diag_left (x * y) (x * y)

/-- **All 64 generator triples vanish.** For `a b c ∈ {1, x, y, x*y}`,
    `assoc a b c = 0`.

    **Finding / ESCALATE.** The strategy doc (`artin-strategy-2026-06-06.md` §4,
    §6) priced a *hard remainder* of generator triples that would need the
    `x*y + y*x` trace identity (chunk C2b) to close, expecting only ~60 of 64 to
    die from L1 + alternativity + L2.  In fact the only triples NOT covered by
    {L1 (slot = 1), alternating-diag, L2-family} are the six **flexor** triples
    `assoc a b a` with `a,b ∈ {x, y, x*y}` —
    `assoc x y x`, `assoc x (x*y) x`, `assoc y x y`, `assoc y (x*y) y`,
    `assoc (x*y) x (x*y)`, `assoc (x*y) y (x*y)`.  Each is killed by
    **flexibility** (`assoc_diag_flex : assoc a b a = 0`), an independent ✓-cell
    law lifted from `octonion_flexible_polarized` — **NOT** the Moufang block and
    **NOT** the trace identity.  Hence all 64 close here, from
    L1 + alternativity-diag + L2 + flexibility, with **no `x*y + y*x` identity
    needed**.  This means C2b's trace identity may be unnecessary for the
    associator-side reduction; the only residual obligation for full Artin (C2c/d)
    is the *span-closure* `adjoin ℝ {x,y} ≤ span ℝ {1,x,y,x*y}` (a Mul-closure
    fact, separate from associator vanishing).  Routed to Oppenheimer/theory for a
    possible route simplification — see report. -/
theorem assoc_gen4_zero (x y : CDAlg ℝ 3) :
    ∀ a ∈ gen4 x y, ∀ b ∈ gen4 x y, ∀ c ∈ gen4 x y, assoc a b c = 0 := by
  -- For the fixed value of the first slot, the inner 16 triples (`b,c ∈ gen4`) are
  -- discharged by `assoc_gen4_inner` below; this keeps each elaboration unit small
  -- (16 leaves, not 64) so the default heartbeat budget suffices — NO heartbeat
  -- bump, NO native_decide.
  rintro a ha b hb c hc
  simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  -- `rw [ha]` (not `rfl`/`subst`) keeps `x`,`y` in scope for the inner helpers.
  rcases ha with ha | ha | ha | ha
  · rw [ha]; exact assoc_gen4_inner_one x y b hb c hc
  · rw [ha]; exact assoc_gen4_inner_x x y b hb c hc
  · rw [ha]; exact assoc_gen4_inner_y x y b hb c hc
  · rw [ha]; exact assoc_gen4_inner_xy x y b hb c hc

/-- **C2a payload corollary.** `assoc` vanishes on the whole span
    `span ℝ {1, x, y, x*y}`: combine the complete generator-triple discharge
    (`assoc_gen4_zero`) with the trilinear span-lift (`assoc_span4`).  This is the
    associator-side reduction the Artin assembly (C2d) consumes; the remaining
    obligation for full Artin is multiplicative closure of the span
    (`adjoin ℝ {x,y} ≤ span`), which lives in C2c, NOT here. -/
theorem assoc_vanishes_on_span4 (x y : CDAlg ℝ 3)
    {u v w : CDAlg ℝ 3}
    (hu : u ∈ Submodule.span ℝ (gen4 x y)) (hv : v ∈ Submodule.span ℝ (gen4 x y))
    (hw : w ∈ Submodule.span ℝ (gen4 x y)) :
    assoc u v w = 0 :=
  assoc_span4 x y (assoc_gen4_zero x y) hu hv hw

/-! ## Completeness audit — `#print axioms`

Every theorem in this file must depend only on `{propext, Classical.choice,
Quot.sound}`.  The de-risk gate is `assoc_xy_survivor`; the C2a payload is
`assoc_vanishes_on_span4`. -/

#print axioms assoc_one_left
#print axioms assoc_one_mid
#print axioms assoc_one_right
#print axioms assoc_x_xy_y
#print axioms assoc_xy_survivor
#print axioms trilinear_vanish_on_span
#print axioms assoc_span4
#print axioms assoc_yx_survivor
#print axioms assoc_xy_x_y
#print axioms assoc_xy_y_x
#print axioms assoc_y_xy_x
#print axioms assoc_gen4_inner_one
#print axioms assoc_gen4_inner_x
#print axioms assoc_gen4_inner_y
#print axioms assoc_gen4_inner_xy
#print axioms assoc_gen4_zero
#print axioms assoc_vanishes_on_span4

end QBP.Foundations.CDAlg
