import QBP.Foundations.CrystalHosting

/-!
# QBP.Substrate.Hosting — the substrate as the arena of crystallisation

**Research-thread evidence for #473 AC1 (hosting), sub-issue #639.**

This is the FIRST file in `proofs/QBP/Substrate/`.  It exists because the
beekeeper explicitly lifted the empty-`Substrate/` rule for exactly this
definition file (2026-09-07, #473 `issuecomment-5574256922`).  It is a
**definition** file: it names the objects of the hosting frame and proves that
they are inhabited, disjoint, exhaustive and coherent.  It introduces **no new
mathematics** — every substantive theorem below is a restatement, on the named
objects, of a theorem already proved in `QBP.Foundations.CrystalHosting`,
`QBP.Foundations.NoAutonomousDynamics` or `QBP.Foundations.DeltaLandscape`, and
each restatement cites its original.

## The frame (beekeeper, 2026-09-07, verbatim)

> *the substrate is what allows crystallisation; a crystallisation enables one
> specific instance of the Cayley–Dickson tower, bounded by the boundary of that
> universe; a universe = one crystallised instance.*

## The objects

* **Substrate.**  `StateSphere` — the imaginary unit sphere of 𝕊,
  `{s : CDAlg ℝ 4 | s.coord 0 = 0 ∧ N s = 1}`, i.e. `S¹⁴ ⊂ Im 𝕊`.  The norm `N`
  is **algebra-supplied, not postulated**: it is the Cayley–Dickson norm form,
  positive definite at level 4 (`CDAlg.alt_N_eq_zero_iff`,
  `NormForm.N_eq_zero_iff`).  *Theorem, not choice.*

* **Potential.**  `potential s = N (cdLo s * cdHi s − cdHi s * cdLo s)` = the #629
  landscape `V(s) = δ² = ‖[a, b]‖²` on the Cayley–Dickson pair split
  `s = a + bℓ`.  `potential_descends` records (by citation) that `V` descends to
  the G₂-invariants `(|a|², |Im b|², ⟨a, Im b⟩)`
  (`DeltaLandscape.sedenion_landscape_descends`).  *Theorem, not choice.*

* **Initial ensemble.**  The surface measure of `N` on `StateSphere`.  This is a
  **beekeeper ruling** (horn 1, PERMITTED: MaxEnt with `N`'s geometry as
  reference) and is **NOT defined in this file** — there is no measure theory
  here at all.

* **The rule.**  A POSTULATE (#635; currently first-order overdamped descent of
  `V`).  **NOT defined here.**  Nothing below refers to a flow, a time parameter,
  or a dynamical system.

* **Universe.**  A `Universe` is a vacuum `s ∈ UniverseSpace` (a crystal on the
  state sphere) together with `U.hosted`, the subalgebra `{1, s, ℓ}` generates —
  *the specific Cayley–Dickson tower instance the crystallisation enables*.
  `universe_hosts_quaternion` puts `U.hosted` inside a quaternion subalgebra
  `span{1, ℓ, U, ℓU}`; `universe_hosted_proper` shows it is a *proper* part of 𝕊.
  The physics hosted on the unit sphere (an S³) of that ℍ is the Agda side
  (`S3FromCD.S³-HSpace`, `SkyrmionCharge.agda`, `SubstrateCharge.agda`) — **cited,
  not formalised here**; nothing below transports it.

* **In-flight region.**  `InFlight` — the imaginary unit non-vacua.
  `inFlight_no_quaternion_closure` makes "not yet crystallised" a *theorem*
  rather than a slogan: on `InFlight` the scalar-spectrum identity
  `−L_s² = N(s)·id` provably FAILS (`CrystalHosting.left_mul_sq_scalar_iff_vacuum`).

* **Poles.**  `polePlus`/`poleMinus` (`±ℓ`) are crystals whose hosted algebra is
  exactly `span{1, ℓ} ≅ ℂ` — the honest degeneration of the parametrisation
  (`CrystalHosting.vacuum_pole_of_dir_zero`).  `pole_hosts_complex` states this
  for the normalisation of any `b₀ • ℓ`, `b₀ ≠ 0`.

## What this file explicitly does NOT derive

1. **No derivation of ℝ, of the doubling, of the measure class, or of the rule.**
   Job A is closed negative (KILLED-locale-forcing-route; Prop 12 ratified).  The
   substrate *hosts*; **circularity with the algebra is permitted** — the objects
   here are built out of `CDAlg ℝ 4` on purpose and no attempt is made to
   generate the algebra from something prior.
2. **The crystal's ℍ is NOT identified with "the observer's ℍ".**  DERIV-holographic
   flag 3 is pending the beekeeper's ruling.  `U.hosted ⊆ span{1, ℓ, U, ℓU}` is a
   statement about a subalgebra of 𝕊 and nothing more.
3. **No boundary and no holography semantics.**  `Universe` carries no boundary
   field; the word "bounded" in the frame is not formalised anywhere below.
4. **No measure, no flow, no dynamics.**  See "initial ensemble" and "the rule".

A concluding section (§8) lists what is missing with the issue that owns it.
-/

namespace QBP.Substrate.Hosting

open QBP.Foundations
open QBP.Foundations.CDAlg
open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

/-! ## 1. The substrate: the imaginary unit sphere of 𝕊 -/

/-- **The substrate.**  The state sphere `S¹⁴ ⊂ Im 𝕊`: imaginary sedenions of
    unit Cayley–Dickson norm.  Both conditions are algebra-supplied — `coord 0`
    is the real part of the CD pair split and `N` is the CD norm form, positive
    definite at level 4 (`alt_N_eq_zero_iff`). -/
def StateSphere : Set (CDAlg ℝ 4) := {s | s.coord 0 = 0 ∧ N s = 1}

theorem mem_stateSphere {s : CDAlg ℝ 4} :
    s ∈ StateSphere ↔ s.coord 0 = 0 ∧ N s = 1 := Iff.rfl

theorem stateSphere_coord_zero {s : CDAlg ℝ 4} (h : s ∈ StateSphere) : s.coord 0 = 0 := h.1

theorem stateSphere_norm_one {s : CDAlg ℝ 4} (h : s ∈ StateSphere) : N s = 1 := h.2

/-- The norm form is strictly positive off `0` — the positive-definiteness of `N`
    at level 4 (`alt_N_eq_zero_iff`) in the form used repeatedly below. -/
theorem N_pos_of_ne_zero {s : CDAlg ℝ 4} (hs : s ≠ 0) : 0 < N s :=
  lt_of_le_of_ne (alt_N_nonneg s) (fun h => hs ((alt_N_eq_zero_iff s).mp h.symm))

/-- The substrate contains no `0`: the sphere is a genuine sphere. -/
theorem stateSphere_ne_zero {s : CDAlg ℝ 4} (h : s ∈ StateSphere) : s ≠ 0 := by
  intro h0
  have hN : N s = 0 := by rw [h0, N_zero]
  rw [h.2] at hN
  norm_num at hN

/-- Radial normalisation onto the state sphere. -/
noncomputable def normalise (s : CDAlg ℝ 4) : CDAlg ℝ 4 := (Real.sqrt (N s))⁻¹ • s

theorem normalise_def (s : CDAlg ℝ 4) : normalise s = (Real.sqrt (N s))⁻¹ • s := rfl

theorem normalise_coeff_ne_zero {s : CDAlg ℝ 4} (hs : s ≠ 0) : (Real.sqrt (N s))⁻¹ ≠ 0 :=
  inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (N_pos_of_ne_zero hs)))

/-- **Normalisation lands on the substrate.**  Any nonzero imaginary sedenion has
    a unit representative on `StateSphere`. -/
theorem normalise_mem_stateSphere {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) (hs0 : s ≠ 0) :
    normalise s ∈ StateSphere := by
  have hN : 0 < N s := N_pos_of_ne_zero hs0
  have hr2 : (Real.sqrt (N s)) ^ 2 = N s := Real.sq_sqrt hN.le
  refine ⟨?_, ?_⟩
  · rw [normalise_def, smul_coord, hs, mul_zero]
  · rw [normalise_def, N_smul, inv_pow, hr2, inv_mul_cancel₀ (ne_of_gt hN)]

/-! ## 2. The potential `V = ‖[cdLo s, cdHi s]‖²` -/

/-- **The landscape potential.**  `V(s) = δ² = ‖[a, b]‖²` for the Cayley–Dickson
    pair split `s = a + bℓ`, `a = cdLo s`, `b = cdHi s`.  This is the #629
    potential verbatim; `DeltaLandscape.sedenion_landscape_descends` is the
    theorem that it descends to the G₂-invariants. -/
def potential (s : CDAlg ℝ 4) : ℝ := N (cdLo s * cdHi s - cdHi s * cdLo s)

theorem potential_nonneg (s : CDAlg ℝ 4) : 0 ≤ potential s := alt_N_nonneg _

/-- **The potential is exactly the vacuum indicator.**  `V(s) = 0 ↔ s` is a
    crystal.  Positive definiteness of `N` (`alt_N_eq_zero_iff`) turns "the
    commutator has zero norm" into "the components commute", which is the
    *definition* of `CrystalHosting.IsVacuum`. -/
theorem potential_eq_zero_iff_isVacuum {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    potential s = 0 ↔ IsVacuum s := by
  rw [potential, alt_N_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩

theorem potential_pos_of_not_isVacuum {s : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (h : ¬ IsVacuum s) : 0 < potential s :=
  lt_of_le_of_ne (potential_nonneg s)
    (fun he => h ((potential_eq_zero_iff_isVacuum hs).mp he.symm))

/-- **`V` descends to the G₂-invariants** — `DeltaLandscape.sedenion_landscape_descends`
    restated on `potential`.  `V` is a function of `(|a|², |Im b|², ⟨a, Im b⟩)`
    alone, so it is constant on G₂-orbits. -/
theorem potential_descends (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    potential s
      = 4 * (N (cdLo s) * N (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))
             - (bil (cdLo s)
                 (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))) ^ 2) :=
  QBP.Foundations.DeltaLandscape.sedenion_landscape_descends s hs

/-! ## 3. Scaling behaviour of the crystal condition -/

/-- The crystal condition is scale-invariant away from `0`: `r • s` is a vacuum
    iff `s` is, for `r ≠ 0`.  (Needed to move witnesses onto the unit sphere.) -/
theorem isVacuum_smul_iff {r : ℝ} (hr : r ≠ 0) {s : CDAlg ℝ 4} :
    IsVacuum (r • s) ↔ IsVacuum s := by
  have hlo : cdLo (r • s) * cdHi (r • s) = (r * r) • (cdLo s * cdHi s) := by
    rw [cdLo_smul, cdHi_smul, mul_smul_left, mul_smul_right, smul_smul]
  have hhi : cdHi (r • s) * cdLo (r • s) = (r * r) • (cdHi s * cdLo s) := by
    rw [cdLo_smul, cdHi_smul, mul_smul_left, mul_smul_right, smul_smul]
  constructor
  · rintro ⟨h0, hc⟩
    refine ⟨?_, ?_⟩
    · rw [smul_coord] at h0
      exact (mul_eq_zero.mp h0).resolve_left hr
    · rw [hlo, hhi] at hc
      have := congrArg (fun z : CDAlg ℝ 3 => ((r * r)⁻¹ : ℝ) • z) hc
      simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hr hr), one_smul] using this
  · rintro ⟨h0, hc⟩
    exact ⟨by rw [smul_coord, h0, mul_zero], by rw [hlo, hhi, hc]⟩

/-! ## 4. The space of universes and the in-flight region -/

/-- **The space of universes.**  The vacuum locus `{V = 0}` on the state sphere:
    crystals.  (The *topology* of the quotient by `Aut(𝕊)` — the doc's `S²`,
    orbifold `S²(2,2,3)` — is NOT formalised here.) -/
def UniverseSpace : Set (CDAlg ℝ 4) := {s | s ∈ StateSphere ∧ IsVacuum s}

/-- **The in-flight region.**  `{V > 0}` on the state sphere: imaginary unit
    sedenions that have not crystallised. -/
def InFlight : Set (CDAlg ℝ 4) := {s | s ∈ StateSphere ∧ ¬ IsVacuum s}

theorem mem_universeSpace {s : CDAlg ℝ 4} :
    s ∈ UniverseSpace ↔ s ∈ StateSphere ∧ IsVacuum s := Iff.rfl

theorem mem_inFlight {s : CDAlg ℝ 4} :
    s ∈ InFlight ↔ s ∈ StateSphere ∧ ¬ IsVacuum s := Iff.rfl

/-- The two regions are cut out by the potential: `{V = 0}` and `{V > 0}`. -/
theorem mem_universeSpace_iff_potential {s : CDAlg ℝ 4} :
    s ∈ UniverseSpace ↔ s ∈ StateSphere ∧ potential s = 0 := by
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨hs, (potential_eq_zero_iff_isVacuum hs.1).mpr hv⟩
  · rintro ⟨hs, hp⟩
    exact ⟨hs, (potential_eq_zero_iff_isVacuum hs.1).mp hp⟩

theorem mem_inFlight_iff_potential {s : CDAlg ℝ 4} :
    s ∈ InFlight ↔ s ∈ StateSphere ∧ 0 < potential s := by
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨hs, potential_pos_of_not_isVacuum hs.1 hv⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, fun hv => ?_⟩
    rw [(potential_eq_zero_iff_isVacuum hs.1).mpr hv] at hp
    exact lt_irrefl 0 hp

/-- **The substrate is partitioned into crystallised and in-flight states.** -/
theorem stateSphere_partition : ∀ s ∈ StateSphere, s ∈ UniverseSpace ∨ s ∈ InFlight := by
  intro s hs
  by_cases h : IsVacuum s
  · exact Or.inl ⟨hs, h⟩
  · exact Or.inr ⟨hs, h⟩

/-- …and the two parts are disjoint. -/
theorem universeSpace_inFlight_disjoint : ∀ s : CDAlg ℝ 4, ¬ (s ∈ UniverseSpace ∧ s ∈ InFlight) := by
  rintro s ⟨⟨_, hv⟩, ⟨_, hnv⟩⟩
  exact hnv hv

/-- …so together they are exactly the substrate. -/
theorem universeSpace_union_inFlight : UniverseSpace ∪ InFlight = StateSphere := by
  ext s
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hs
    exact stateSphere_partition s hs

/-! ## 5. A universe -/

/-- **A universe = one crystallised instance.**  A crystal on the state sphere.
    The hosted tower instance is `Universe.hosted` below.  No boundary, no
    measure, no history: see the module docstring §"What this file does NOT
    derive". -/
structure Universe where
  /-- The crystal: an imaginary unit sedenion whose CD components commute. -/
  crystal : CDAlg ℝ 4
  /-- Membership in the vacuum locus of the state sphere. -/
  mem : crystal ∈ UniverseSpace

namespace Universe

variable (U : Universe)

theorem isVacuum : IsVacuum U.crystal := U.mem.2
theorem coord_zero : U.crystal.coord 0 = 0 := U.mem.1.1
theorem norm_one : N U.crystal = 1 := U.mem.1.2
theorem crystal_ne_zero : U.crystal ≠ 0 := stateSphere_ne_zero U.mem.1

/-- **The hosted tower instance.**  The subalgebra generated by `{1, crystal, ℓ}`
    under `+`, real scaling, the sedenion product and conjugation — *the specific
    Cayley–Dickson tower instance this crystallisation enables*. -/
def hosted : Set (CDAlg ℝ 4) := {x | GenByPair U.crystal ell x}

theorem mem_hosted {x : CDAlg ℝ 4} : x ∈ U.hosted ↔ GenByPair U.crystal ell x := Iff.rfl

theorem one_mem_hosted : (1 : CDAlg ℝ 4) ∈ U.hosted := GenByPair.one
theorem crystal_mem_hosted : U.crystal ∈ U.hosted := GenByPair.left
theorem ell_mem_hosted : ell ∈ U.hosted := GenByPair.right

end Universe

/-! ## 6. What a universe hosts (restatements of the `CrystalHosting` theorems) -/

/-- **Every universe hosts a quaternion algebra** — `CrystalHosting.vacuum_hosts_quaternion`
    restated on `Universe.hosted`.  There is one octonion direction `u` (a unit,
    or `0` exactly at the poles) with the whole hosted algebra inside
    `span_ℝ{1, ℓ, U, ℓU}`, `U = loOf u`.

    **Guardrail:** this asserts a containment in a quaternion subalgebra of 𝕊 and
    nothing else.  No identification with "the observer's ℍ" is made here
    (DERIV-holographic flag 3 pending). -/
theorem universe_hosts_quaternion (U : Universe) :
    ∃ u : CDAlg ℝ 3, u.coord 0 = 0 ∧ (N u = 1 ∨ u = 0) ∧
      ∀ x ∈ U.hosted, InQuatSpan (loOf u) x := by
  obtain ⟨u, _, _, _, hu0, hNu, _, _, hgen⟩ := vacuum_hosts_quaternion U.isVacuum
  exact ⟨u, hu0, hNu, fun x hx => hgen x hx⟩

/-- A CHOSEN hosting direction for a universe.  `Classical.choose` on
    `universe_hosts_quaternion`: `dir` is *a* valid direction, not a canonical
    one — no uniqueness (even up to sign) is claimed or proved here. -/
noncomputable def Universe.dir (U : Universe) : CDAlg ℝ 3 :=
  Classical.choose (universe_hosts_quaternion U)

theorem Universe.dir_spec (U : Universe) :
    (U.dir).coord 0 = 0 ∧ (N U.dir = 1 ∨ U.dir = 0) ∧
      ∀ x ∈ U.hosted, InQuatSpan (loOf U.dir) x :=
  Classical.choose_spec (universe_hosts_quaternion U)

theorem Universe.hosted_subset_quatSpan (U : Universe) :
    ∀ x ∈ U.hosted, InQuatSpan (loOf U.dir) x := (U.dir_spec).2.2

/-- **The quaternion relations at a universe's chosen direction** —
    `CrystalHosting.crystal_quaternion_table` restated at `U.dir` in the
    non-degenerate (non-pole) case `N U.dir = 1`.  `i = ℓ`, `j = loOf U.dir`,
    `k = ℓ · loOf U.dir`. -/
theorem universe_quaternion_table (U : Universe) (h : N U.dir = 1) :
    ell * ell = -(1 : CDAlg ℝ 4) ∧
    loOf U.dir * loOf U.dir = -(1 : CDAlg ℝ 4) ∧
    (ell * loOf U.dir) * (ell * loOf U.dir) = -(1 : CDAlg ℝ 4) ∧
    loOf U.dir * ell = -(ell * loOf U.dir) ∧
    loOf U.dir * (ell * loOf U.dir) = ell ∧
    (ell * loOf U.dir) * loOf U.dir = -ell ∧
    ell * (ell * loOf U.dir) = -loOf U.dir :=
  crystal_quaternion_table (U.dir_spec).1 h

/-- **The hosted tower instance is a PROPER part of 𝕊** — from
    `CrystalHosting.quatSpan_dir_proper`.  So "a crystallisation enables one
    specific instance of the tower" is a genuine restriction: the instance is not
    all of 𝕊. -/
theorem universe_hosted_proper (U : Universe) : ∃ z : CDAlg ℝ 4, z ∉ U.hosted := by
  obtain ⟨u, hu0, _, hsub⟩ := universe_hosts_quaternion U
  obtain ⟨z, hz⟩ := quatSpan_dir_proper (u := u) hu0
  exact ⟨z, fun hmem => hz (hsub z hmem)⟩

/-! ## 7. The poles host ℂ -/

/-- Every real multiple of `ℓ` is a crystal (its low CD component vanishes). -/
theorem smul_ell_isVacuum (b₀ : ℝ) : IsVacuum (b₀ • ell) := by
  refine ⟨by rw [smul_coord, ell_coord_zero, mul_zero], ?_⟩
  rw [cdLo_smul, cdLo_ell, smul_zero, alt_zero_mul, alt_mul_zero]

/-- **The poles host exactly ℂ = span{1, ℓ}.**  For any real multiple of `ℓ`, the
    algebra generated with `ℓ` is precisely `span_ℝ{1, ℓ}` — the degenerate
    (`u = 0`) branch of `CrystalHosting.vacuum_pole_of_dir_zero`.  Stated as an
    equality of sets, so it is both an upper *and* a lower bound. -/
theorem smul_ell_hosted_eq_complex (b₀ : ℝ) :
    {x : CDAlg ℝ 4 | GenByPair (b₀ • ell) ell x}
      = {x : CDAlg ℝ 4 | ∃ a b : ℝ, x = a • (1 : CDAlg ℝ 4) + b • ell} := by
  ext x
  constructor
  · intro hx
    have h0 : (b₀ • ell).coord 0 = 0 := by rw [smul_coord, ell_coord_zero, mul_zero]
    have hp : (b₀ • ell) - ((b₀ • ell).coord (hiIdx 0)) • ell = 0 := by
      rw [smul_coord, ell_coord_hiIdx_zero, mul_one, sub_self]
    have h := genByPair_ell_mem_quatSpan (b₀ • ell) h0 x hx
    rw [hp] at h
    obtain ⟨a, b, c, d, hx'⟩ := h
    exact ⟨a, b, by rw [hx', alt_mul_zero]; module⟩
  · rintro ⟨a, b, rfl⟩
    exact GenByPair.add (GenByPair.smul a GenByPair.one) (GenByPair.smul b GenByPair.right)

theorem smul_ell_ne_zero {b₀ : ℝ} (hb : b₀ ≠ 0) : b₀ • ell ≠ 0 := by
  intro h
  have hN : N (b₀ • ell) = b₀ ^ 2 := by rw [N_smul, N_ell, mul_one]
  rw [h, N_zero] at hN
  exact hb ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hN.symm)

/-- **`pole_hosts_complex`.**  For `b₀ ≠ 0` the normalisation of `b₀ • ℓ` is a
    point of `UniverseSpace` whose hosted algebra is exactly `span{1, ℓ} ≅ ℂ`:
    the poles of the vacuum parametrisation host ℂ, not ℍ. -/
theorem pole_hosts_complex {b₀ : ℝ} (hb : b₀ ≠ 0) :
    normalise (b₀ • ell) ∈ UniverseSpace ∧
      {x : CDAlg ℝ 4 | GenByPair (normalise (b₀ • ell)) ell x}
        = {x : CDAlg ℝ 4 | ∃ a b : ℝ, x = a • (1 : CDAlg ℝ 4) + b • ell} := by
  have hne : b₀ • ell ≠ 0 := smul_ell_ne_zero hb
  have h0 : (b₀ • ell).coord 0 = 0 := by rw [smul_coord, ell_coord_zero, mul_zero]
  have hform : normalise (b₀ • ell) = ((Real.sqrt (N (b₀ • ell)))⁻¹ * b₀) • ell := by
    rw [normalise_def, smul_smul]
  refine ⟨⟨normalise_mem_stateSphere h0 hne, ?_⟩, ?_⟩
  · rw [hform]; exact smul_ell_isVacuum _
  · rw [hform]; exact smul_ell_hosted_eq_complex _

/-- `ℓ` itself is such a pole. -/
theorem ell_mem_universeSpace : ell ∈ UniverseSpace :=
  ⟨⟨ell_coord_zero, N_ell⟩, ell_isVacuum⟩

/-- The universe at the north pole `+ℓ`. -/
def polePlus : Universe := ⟨ell, ell_mem_universeSpace⟩

theorem polePlus_hosted_eq_complex :
    polePlus.hosted = {x : CDAlg ℝ 4 | ∃ a b : ℝ, x = a • (1 : CDAlg ℝ 4) + b • ell} := by
  have h : polePlus.hosted = {x : CDAlg ℝ 4 | GenByPair ((1 : ℝ) • ell) ell x} := by
    rw [Universe.hosted]
    simp only [polePlus, one_smul]
  rw [h, smul_ell_hosted_eq_complex]

/-! ## 8. The local spectrum at a universe, and its failure in flight -/

/-- **The local spectrum at a universe.**  `CrystalHosting.left_mul_sq_at_vacuum`
    restated: at a crystal `−L_s²` is the scalar `N(s)·id`, and on the state
    sphere `N s = 1`, so `L_s² = −id` exactly — the crystal acts like a complex
    structure on the whole of 𝕊. -/
theorem local_spectrum_at_universe (U : Universe) (x : CDAlg ℝ 4) :
    U.crystal * (U.crystal * x) = -x := by
  rw [left_mul_sq_at_vacuum U.isVacuum x, U.norm_one]
  module

/-- The same in the `N`-carrying form (before using `N s = 1`). -/
theorem local_spectrum_at_universe_smul (U : Universe) (x : CDAlg ℝ 4) :
    U.crystal * (U.crystal * x) = (-(N U.crystal)) • x :=
  left_mul_sq_at_vacuum U.isVacuum x

/-- **`1` is the only eigenvalue of `−L_s²` at a universe** —
    `CrystalHosting.vacuum_eigenvalue_unique` on the unit sphere. -/
theorem universe_eigenvalue_unique (U : Universe) {x : CDAlg ℝ 4} (hx : x ≠ 0) {lam : ℝ}
    (h : -(U.crystal * (U.crystal * x)) = lam • x) : lam = 1 := by
  have hl := vacuum_eigenvalue_unique U.isVacuum hx h
  rwa [U.norm_one] at hl

/-- **"Not yet crystallised" is a theorem, not a slogan.**  For an in-flight state
    the scalar-spectrum identity `−L_s² = N(s)·id` provably FAILS: there is some
    `x` with `s·(s·x) ≠ −N(s)·x`.  This is exactly
    `CrystalHosting.left_mul_sq_scalar_iff_vacuum` read contrapositively, so the
    in-flight region is *precisely* the region where the crystal's degenerate
    local spectrum does not hold. -/
theorem inFlight_no_quaternion_closure {s : CDAlg ℝ 4} (hs : s ∈ InFlight) :
    ¬ (∀ x, s * (s * x) = (-(N s)) • x) := by
  intro h
  exact hs.2 ((left_mul_sq_scalar_iff_vacuum hs.1.1).mp h)

/-- The same on the unit sphere, where `N s = 1`. -/
theorem inFlight_no_complex_structure {s : CDAlg ℝ 4} (hs : s ∈ InFlight) :
    ¬ (∀ x, s * (s * x) = -x) := by
  intro h
  refine inFlight_no_quaternion_closure hs (fun x => ?_)
  rw [h x, hs.1.2]
  module

/-- Conversely, on the state sphere the identity `L_s² = −id` characterises the
    universes: the two regions are separated by a *theorem*, not a convention. -/
theorem mem_universeSpace_iff_complex_structure {s : CDAlg ℝ 4} (hs : s ∈ StateSphere) :
    s ∈ UniverseSpace ↔ ∀ x, s * (s * x) = -x := by
  constructor
  · intro hU x
    exact local_spectrum_at_universe ⟨s, hU⟩ x
  · intro h
    refine ⟨hs, (left_mul_sq_scalar_iff_vacuum hs.1).mp (fun x => ?_)⟩
    rw [h x, hs.2]
    module

/-! ## 9. Equivariance under `ℓ`-fixing automorphisms (the G₂ side) -/

/-- Automorphisms preserve the substrate: they fix the real part and the norm
    form (`CDAut.map_re_and_N`), which is exactly the pair of conditions defining
    `StateSphere`. -/
theorem stateSphere_map_mem (φ : CDAut 4) {s : CDAlg ℝ 4} (h : s ∈ StateSphere) :
    φ s ∈ StateSphere :=
  ⟨by rw [φ.map_re s, h.1], by rw [φ.map_N s, h.2]⟩

/-- The image of a universe under an automorphism is a universe. -/
def Universe.map (φ : CDAut 4) (U : Universe) : Universe :=
  ⟨φ U.crystal, ⟨stateSphere_map_mem φ U.mem.1, aut_map_isVacuum φ U.isVacuum⟩⟩

/-- **Hosting is equivariant under every `ℓ`-fixing automorphism** —
    `CrystalHosting.aut_hosting_equivariant` restated on `Universe`.  The crystal
    condition, the substrate and the hosted tower instance are all carried along.
    (Only the G₂ side is covered: `φ ℓ = ℓ`.  The `S₃` factor, which moves `ℓ`,
    is NOT treated — see §10.) -/
theorem hosting_equivariant (φ : CDAut 4) (hφ : φ ell = ell) (U : Universe) :
    IsVacuum (φ U.crystal) ∧ φ U.crystal ∈ StateSphere ∧
      ∀ x ∈ U.hosted, φ x ∈ (U.map φ).hosted := by
  refine ⟨aut_map_isVacuum φ U.isVacuum, stateSphere_map_mem φ U.mem.1, fun x hx => ?_⟩
  exact (aut_hosting_equivariant φ hφ U.isVacuum).2 x hx

/-- **The ℤ/2 of the `S₃` side.**  The grade automorphism `gradeAut` (`ℓ ↦ −ℓ`)
    moves `ℓ`, so `hosting_equivariant` does not cover it — but the hosted
    algebra is generated by `{1, s, ℓ}` and `−ℓ` generates the same algebra
    (`CrystalHosting.gradeAut_hosting_equivariant`), so hosting is equivariant
    under it all the same.  The order-3 elements of `S₃` remain open (§11). -/
theorem hosting_equivariant_grade (U : Universe) :
    IsVacuum (gradeAut U.crystal) ∧ gradeAut U.crystal ∈ StateSphere ∧
      ∀ x ∈ U.hosted, gradeAut x ∈ (U.map gradeAut).hosted := by
  refine ⟨aut_map_isVacuum gradeAut U.isVacuum, stateSphere_map_mem gradeAut U.mem.1,
    fun x hx => ?_⟩
  exact (gradeAut_hosting_equivariant U.isVacuum).2 x hx

/-! ## 10. Non-vacuity: both regions are inhabited, and not only by poles -/

theorem universeSpace_nonempty : ∃ s : CDAlg ℝ 4, s ∈ UniverseSpace :=
  ⟨ell, ell_mem_universeSpace⟩

theorem sAll_ne_zero : sAll ≠ (0 : CDAlg ℝ 4) := by
  intro h
  have hN : N sAll = 0 := by rw [h, N_zero]
  rw [N_sAll] at hN
  norm_num at hN

/-- The normalisation of `sAll = Σ_{a=1}^{15} e_a` is a universe. -/
theorem normalise_sAll_mem_universeSpace : normalise sAll ∈ UniverseSpace := by
  refine ⟨normalise_mem_stateSphere sAll_coord_zero sAll_ne_zero, ?_⟩
  rw [normalise_def]
  exact (isVacuum_smul_iff (normalise_coeff_ne_zero sAll_ne_zero)).mpr sAll_isVacuum

/-- **`UniverseSpace` is not just the two poles.**  `normalise sAll` is a crystal
    that is not a real multiple of `ℓ`, so `universe_hosts_quaternion` is not
    vacuously a statement about `span{1, ℓ} ≅ ℂ`. -/
theorem universeSpace_nonpole : ∃ s ∈ UniverseSpace, ∀ t : ℝ, s ≠ t • ell := by
  refine ⟨normalise sAll, normalise_sAll_mem_universeSpace, fun t h => ?_⟩
  have h1 := congrArg (fun z : CDAlg ℝ 4 => z.coord (1 : Fin (2 ^ 4))) h
  simp only [normalise_def, smul_coord] at h1
  rw [sAll_coord, if_neg (by decide : (1 : Fin (2 ^ 4)) ≠ 0), mul_one,
    ell, e_coord, if_neg (by decide : (1 : Fin (2 ^ 4)) ≠ hiIdx 0), mul_zero] at h1
  exact normalise_coeff_ne_zero sAll_ne_zero h1

theorem N_sedWitX : N sedWitX = 2 := by
  have hne : (⟨1, by omega⟩ : Fin (2 ^ 4)) ≠ ⟨10, by omega⟩ := by decide
  rw [sedWitX, alt_N_add, N_e, N_e, bil_e, if_neg hne]
  norm_num

theorem sedWitX_ne_zero : sedWitX ≠ (0 : CDAlg ℝ 4) := by
  intro h
  have hN : N sedWitX = 0 := by rw [h, N_zero]
  rw [N_sedWitX] at hN
  norm_num at hN

/-- **The in-flight region is inhabited.**  The normalisation of the standard
    non-alternativity witness `e₁ + e₁₀` is an imaginary unit sedenion that is not
    a crystal. -/
theorem normalise_sedWitX_mem_inFlight : normalise sedWitX ∈ InFlight := by
  refine ⟨normalise_mem_stateSphere sedWitX_coord_zero sedWitX_ne_zero, ?_⟩
  rw [normalise_def]
  exact fun hv =>
    sedWitX_not_isVacuum ((isVacuum_smul_iff (normalise_coeff_ne_zero sedWitX_ne_zero)).mp hv)

theorem inFlight_nonempty : ∃ s : CDAlg ℝ 4, s ∈ InFlight :=
  ⟨normalise sedWitX, normalise_sedWitX_mem_inFlight⟩

/-- Consequently `UniverseSpace` is a PROPER subset of the substrate: not every
    state of the substrate is a universe. -/
theorem universeSpace_ne_stateSphere : UniverseSpace ≠ StateSphere := by
  intro h
  obtain ⟨s, hs⟩ := inFlight_nonempty
  exact universeSpace_inFlight_disjoint s ⟨h ▸ hs.1, hs⟩

/-! ## 11. What is NOT in this file, and who owns it

Nothing below is defined, assumed or used anywhere above.  Each line names the
issue that owns the gap.

* **The initial ensemble / the surface measure of `N`.**  Beekeeper ruling
  (horn 1, PERMITTED) — there is no measure theory in this file at all, and
  `StateSphere` carries no measure-space structure.  Owner: #473 AC1.
* **The rule (the flow).**  POSTULATE, owner **#635** — currently first-order
  overdamped descent of `V`.  No flow, no time parameter and no dynamical system
  appears above; `potential` is a function, not a gradient field.
* **The Agda S³ witnesses and their transport.**  `S3FromCD.S³-HSpace`,
  `SkyrmionCharge.agda` (`B(hedgehog) = 1`, `π₃(S³) ≅ ℤ`), `SubstrateCharge.agda`
  (`B(f ⋆ g) = B f + B g`) are cited in the docstring and used nowhere in Lean.
  Transporting them to the unit sphere of every `ℍ_s` is open.  Owner: #639 (c).
* **Crystal-covariance across the order-3 elements of the `S₃` factor of `Aut(𝕊)`.**
  `hosting_equivariant` covers automorphisms with `φ ℓ = ℓ` (the G₂ side) and
  `hosting_equivariant_grade` covers the ℤ/2 (`gradeAut`, `ℓ ↦ −ℓ`).  The order-3
  elements of `S₃` (which send `ℓ` to another root of the CD doubling) are NOT
  treated; since `Universe.hosted` is *defined* with `ℓ`, covariance under them is
  a property of the definition still to be proved.  Owner: #639 (e).
* **The boundary of a universe.**  AXIOM-2 says the boundary encoding is 𝕆; the
  `Universe` structure above carries NO boundary field and no holography
  semantics.  DERIV-holographic flag 3 (identifying `ℍ_s` with "the observer's ℍ")
  is pending the beekeeper's ruling.  Owner: #473 / #639 (open question 2).
* **A "pointless" description of the in-flight region.**  `InFlight` is a plain
  `Set`; no locale, condensed object or limit of finite approximations is built.
  Owner: #636 / #639 (open question 3).
* **Where our universe sits.**  No `b₀` is fixed.  Owner: **#637**.
-/

/-! ## 12. Completeness audit — `#print axioms`

Every theorem in this file must depend on a subset of `{propext, Classical.choice,
Quot.sound}` (`decide`-based lemmas legitimately show fewer).  Anything else (`sorryAx`, a native-reduction axiom, a user axiom)
is a finding. -/

#print axioms mem_stateSphere
#print axioms stateSphere_coord_zero
#print axioms stateSphere_norm_one
#print axioms N_pos_of_ne_zero
#print axioms stateSphere_ne_zero
#print axioms normalise_def
#print axioms normalise_coeff_ne_zero
#print axioms normalise_mem_stateSphere
#print axioms potential_nonneg
#print axioms potential_eq_zero_iff_isVacuum
#print axioms potential_pos_of_not_isVacuum
#print axioms potential_descends
#print axioms isVacuum_smul_iff
#print axioms mem_universeSpace
#print axioms mem_inFlight
#print axioms mem_universeSpace_iff_potential
#print axioms mem_inFlight_iff_potential
#print axioms stateSphere_partition
#print axioms universeSpace_inFlight_disjoint
#print axioms universeSpace_union_inFlight
#print axioms Universe.isVacuum
#print axioms Universe.coord_zero
#print axioms Universe.norm_one
#print axioms Universe.crystal_ne_zero
#print axioms Universe.mem_hosted
#print axioms Universe.one_mem_hosted
#print axioms Universe.crystal_mem_hosted
#print axioms Universe.ell_mem_hosted
#print axioms universe_hosts_quaternion
#print axioms Universe.dir_spec
#print axioms Universe.hosted_subset_quatSpan
#print axioms universe_quaternion_table
#print axioms universe_hosted_proper
#print axioms smul_ell_isVacuum
#print axioms smul_ell_hosted_eq_complex
#print axioms smul_ell_ne_zero
#print axioms pole_hosts_complex
#print axioms ell_mem_universeSpace
#print axioms polePlus_hosted_eq_complex
#print axioms local_spectrum_at_universe
#print axioms local_spectrum_at_universe_smul
#print axioms universe_eigenvalue_unique
#print axioms inFlight_no_quaternion_closure
#print axioms inFlight_no_complex_structure
#print axioms mem_universeSpace_iff_complex_structure
#print axioms stateSphere_map_mem
#print axioms hosting_equivariant
#print axioms universeSpace_nonempty
#print axioms sAll_ne_zero
#print axioms normalise_sAll_mem_universeSpace
#print axioms universeSpace_nonpole
#print axioms N_sedWitX
#print axioms sedWitX_ne_zero
#print axioms normalise_sedWitX_mem_inFlight
#print axioms inFlight_nonempty
#print axioms universeSpace_ne_stateSphere

-- Data definitions that use choice / classical reasoning, printed for completeness.
#print axioms normalise
#print axioms Universe.dir
#print axioms hosting_equivariant_grade

end QBP.Substrate.Hosting
