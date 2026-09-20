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
2. **The crystal's ℍ is NOT derived to be "the observer's ℍ".**  That identification is
   the content of POST-observer-associativity — an OPEN root with a kill list (the flag-3
   split applied by the #652 encode, ruling bundle v0.7 §2; nothing ruled).  `U.hosted ⊆ span{1, ℓ, U, ℓU}` is a
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
    (that is POST-observer-associativity, an OPEN root — flag-3 split, ruling bundle v0.7 §2). -/
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

/-! ## 7b. Off the poles, hosting is an EQUALITY (#2); two generic universes
       share exactly `ℂ` (#3)

`universe_hosts_quaternion` (§6) is a **containment** `hosted ⊆ ℍ_u`; the
heterogeneous confirmer's verdict of 2026-09-19 (row 1, §8 item 2) demoted the
"`hosts ℍ_s =`" reading for exactly that reason and named the missing half as
the real prerequisite.  Here it is, with the hypothesis the confirmer identified:
the crystal must not be a **pole**.  The hypothesis is necessary — at a pole the
hosted algebra is `span{1, ℓ} ≅ ℂ` (`pole_hosts_complex`, §7), which is
2-dimensional, so no equality with a 4-dimensional `ℍ_u` can hold there.

Interpretation guardrail unchanged: these are statements about subalgebras of 𝕊.
No identification with "the observer's ℍ" or with any physical structure is made
(POST-observer-associativity / INTERP-holographic-boundary remain OPEN roots). -/

/-- **A universe is NON-POLE** when the component of its crystal orthogonal to
    the doubling unit `ℓ` is nonzero. -/
def Universe.NonPole (U : Universe) : Prop :=
  U.crystal - (U.crystal.coord (hiIdx 0)) • ell ≠ 0

/-- `NonPole` says exactly what its name says: the crystal is not a real multiple
    of `ℓ`. -/
theorem Universe.nonPole_iff (U : Universe) :
    U.NonPole ↔ ∀ t : ℝ, U.crystal ≠ t • ell := by
  constructor
  · intro h t hEq
    refine h ?_
    have hc : U.crystal.coord (hiIdx 0) = t := by
      rw [hEq, smul_coord, ell_coord_hiIdx_zero, mul_one]
    rw [hc, hEq, sub_self]
  · intro h hzero
    exact h (U.crystal.coord (hiIdx 0)) (by rw [← sub_eq_zero]; exact hzero)

/-- The north pole is, as advertised, NOT a non-pole: the hypothesis of
    `Universe.hosted_eq_quatSpan` genuinely excludes `pole_hosts_complex`. -/
theorem polePlus_not_nonPole : ¬ polePlus.NonPole := by
  intro h
  exact (polePlus.nonPole_iff.mp h) 1 (by rw [one_smul]; rfl)

/-- **`hosted_eq_quatSpan` (#2).**  For a NON-POLE universe there is a unit
    imaginary octonion direction `u` with

      `U.hosted = ℍ_u = span_ℝ{1, ℓ, U, ℓU}`,  `U = loOf u`,

    an EQUALITY of sets — both the containment of `universe_hosts_quaternion` and
    its converse.  (`crystal_quatSpan_independent` then makes `ℍ_u` genuinely
    4-dimensional, so the hosted algebra is a copy of ℍ on the nose.) -/
theorem Universe.hosted_eq_quatSpan (U : Universe) (h : U.NonPole) :
    ∃ u : CDAlg ℝ 3, u.coord 0 = 0 ∧ N u = 1 ∧
      U.hosted = {x : CDAlg ℝ 4 | InQuatSpan (loOf u) x} := by
  obtain ⟨u, α, γ, b₀, hu0, hNu, hlo, hhi⟩ :=
    (vacuum_iff_parametrised U.crystal).mp U.isVacuum
  have hP := crystal_perp_eq (u := u) (b₀ := b₀) hu0 hlo hhi
  have hk : α ^ 2 + γ ^ 2 ≠ 0 := by
    intro h0
    have hα : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg γ]
    have hγ : γ = 0 := by nlinarith [sq_nonneg α, sq_nonneg γ]
    exact h (by rw [hP, hα, hγ]; module)
  have hNu' : N u = 1 := by
    rcases hNu with h1 | h0
    · exact h1
    · exact absurd (by rw [hP, h0, loOf_zero, hiOf_zero]; module) h
  exact ⟨u, hu0, hNu',
    genByPair_eq_quatSpan_of_param (u := u) U.coord_zero hu0 hlo hhi hk⟩

/-- **`universe_intersection_generic_eq_complex` (#3).**  Two NON-POLE universes
    with DIFFERENT hosted algebras share exactly the complex line
    `span_ℝ{1, ℓ} ≅ ℂ`.

    The genericity hypothesis is stated intrinsically as `U₁.hosted ≠ U₂.hosted`;
    by `inQuatSpan_neg_dir` (the quaternion span only sees the direction up to
    sign) this IMPLIES the confirmer's `u₁ ≠ ±u₂`, which is the form the proof
    consumes.  It is **not** claimed to be equivalent: the converse — distinct
    directions give distinct hosted algebras — needs uniqueness of the hosting
    direction up to sign, which is NOT in this tree (see `Universe.dir`, whose
    own docstring disclaims any uniqueness).  `ℓ` lies in both, so the
    intersection is 2-dimensional — it is `ℂ`, not `ℝ`.  (Red Team F10, PR #663.) -/
theorem universe_intersection_eq_complex {U₁ U₂ : Universe}
    (h₁ : U₁.NonPole) (h₂ : U₂.NonPole) (hne : U₁.hosted ≠ U₂.hosted) :
    U₁.hosted ∩ U₂.hosted
      = {x : CDAlg ℝ 4 | ∃ a b : ℝ, x = a • (1 : CDAlg ℝ 4) + b • ell} := by
  obtain ⟨u₁, hu1, hN1, he1⟩ := U₁.hosted_eq_quatSpan h₁
  obtain ⟨u₂, hu2, hN2, he2⟩ := U₂.hosted_eq_quatSpan h₂
  have hd : u₁ ≠ u₂ := by
    intro hEq
    exact hne (by rw [he1, he2, hEq])
  have hd' : u₁ ≠ -u₂ := by
    intro hEq
    refine hne ?_
    rw [he1, he2, hEq]
    ext x
    simp only [Set.mem_setOf_eq]
    exact inQuatSpan_neg_dir
  rw [he1, he2]
  exact quatSpan_inter_eq_complex hu1 hu2 hN1 hN2 hd hd'

/-! ### A concrete non-pole universe, so §7b is not vacuous -/

theorem loOf_e1_mem_universeSpace :
    loOf (e (1 : Fin (2 ^ 3))) ∈ UniverseSpace := by
  have he0 : (e (1 : Fin (2 ^ 3)) : CDAlg ℝ 3).coord 0 = 0 := by
    rw [e_coord, if_neg (by decide : ¬ ((0 : Fin (2 ^ 3)) = 1))]
  refine ⟨⟨loOf_coord_zero he0, ?_⟩, ⟨loOf_coord_zero he0, ?_⟩⟩
  · rw [N_loOf, N_e]
  · rw [cdLo_loOf, cdHi_loOf, alt_mul_zero, alt_zero_mul]

/-- A universe whose crystal is `loOf e₁` — imaginary, unit, and with vanishing
    `ℓ`-component, hence non-pole. -/
def genericUniverse : Universe := ⟨loOf (e (1 : Fin (2 ^ 3))), loOf_e1_mem_universeSpace⟩

theorem genericUniverse_nonPole : genericUniverse.NonPole := by
  have hhi : genericUniverse.crystal.coord (hiIdx 0) = 0 := loOf_coord_hi_zero _
  intro hz
  rw [hhi, zero_smul, sub_zero] at hz
  have hN : N (loOf (e (1 : Fin (2 ^ 3)))) = 0 := by rw [show loOf (e (1 : Fin (2^3))) = genericUniverse.crystal from rfl, hz, N_zero]
  rw [N_loOf, N_e] at hN
  norm_num at hN

/-- **§7b is not vacuous:** a non-pole universe exists, and its hosted algebra is
    an honest 4-dimensional quaternion span. -/
theorem exists_nonPole_universe : ∃ U : Universe, U.NonPole :=
  ⟨genericUniverse, genericUniverse_nonPole⟩

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

/-! ## 8b. The Hessian of `potential` at a universe (#5, #9)

`CrystalHosting` §4c proves the algebra; here it is restated on `potential` and
on `Universe`.  `b₀` is the **pole coordinate** `s.coord 8 = s.coord (hiIdx 0)`
of the confirmer's §4.2 — pinned to the parametrisation below, not assumed. -/

/-- The Prop-15 parametrisation of a NON-POLE universe, with the non-degeneracy
    `α² + γ² ≠ 0` and `b₀` identified as the pole coordinate `s.coord (hiIdx 0)`. -/
theorem Universe.exists_param (U : Universe) (h : U.NonPole) :
    ∃ (u : CDAlg ℝ 3) (α γ b₀ : ℝ), u.coord 0 = 0 ∧ N u = 1 ∧
      cdLo U.crystal = α • u ∧ cdHi U.crystal = b₀ • (1 : CDAlg ℝ 3) + γ • u ∧
      α ^ 2 + γ ^ 2 ≠ 0 ∧ b₀ = U.crystal.coord (hiIdx 0) := by
  obtain ⟨u, α, γ, b₀, hu0, hNu, hlo, hhi⟩ :=
    (vacuum_iff_parametrised U.crystal).mp U.isVacuum
  have hP := crystal_perp_eq (u := u) (b₀ := b₀) hu0 hlo hhi
  have hk : α ^ 2 + γ ^ 2 ≠ 0 := by
    intro h0
    have hα : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg γ]
    have hγ : γ = 0 := by nlinarith [sq_nonneg α, sq_nonneg γ]
    exact h (by rw [hP, hα, hγ]; module)
  have hNu' : N u = 1 := by
    rcases hNu with h1 | h0
    · exact h1
    · exact absurd (by rw [hP, h0, loOf_zero, hiOf_zero]; module) h
  have hb : b₀ = U.crystal.coord (hiIdx 0) := by
    have hc : (cdHi U.crystal).coord 0 = b₀ := by
      rw [hhi, add_coord, smul_coord, smul_coord, one_coord, if_pos rfl, hu0, mul_one,
        mul_zero, add_zero]
    rw [← hc, cdHi_coord]
  exact ⟨u, α, γ, b₀, hu0, hNu', hlo, hhi, hk, hb⟩

/-- **The potential along a ray through a crystal is an exact quartic.**  No
    constant term (the crystal is a zero of `V`), no linear term (it is a
    minimum), quadratic coefficient `N (secVar s v)`. -/
theorem potential_taylor_at_universe (U : Universe) (v : CDAlg ℝ 4) (t : ℝ) :
    potential (U.crystal + t • v)
      = N (secVar U.crystal v) * t ^ 2
        + 2 * bil (secVar U.crystal v) (quadVar v) * t ^ 3
        + N (quadVar v) * t ^ 4 :=
  potential_taylor_at_vacuum U.isVacuum v t

/-- **The Hessian of `potential`, as a genuine second derivative.** -/
theorem deriv2_potential_at_universe (U : Universe) (v : CDAlg ℝ 4) :
    deriv (deriv (fun t : ℝ => potential (U.crystal + t • v))) 0
      = hessQuad U.crystal v :=
  deriv2_potential_at_vacuum U.isVacuum v

/-- **`vacuum_hessian_rank_six_eigenvalue` — the part that is PROVED (#5).**

    At a NON-POLE universe with pole coordinate `b₀ = s.coord (hiIdx 0)`, for
    EVERY imaginary direction `v`

      `Hess_s(v, v) = 8·(1 − b₀²)·‖P v‖²`,

    where `P v = eigDir α γ (transComp α γ u v)` is the transverse component.
    On the explicit 6-parameter transverse family (`e` imaginary, `e ⟂ u`) this
    gives `Hess = 8(1 − b₀²)·‖v‖` exactly; on the explicit 9-parameter flat
    family it gives `0`.

    **Proved elsewhere on this branch:** `finrank (u^⊥ ∩ Im 𝕆) = 6`
    (`HolographicSubalgebra.finrank_perpIm_eq_six`) and the transverse trace
    `48(1 − b₀²)` over an orthonormal 6-frame whose existence is discharged
    (`hess_trace_transverse_exists`).  **NOT proved:** the finrank identity
    `rank = 14 − 8 = 6` for the FULL tangent form, and the full-tangent-space
    trace.  Those remain owed. -/
theorem universe_hessian_eigenvalue (U : Universe) (h : U.NonPole) :
    ∃ (u : CDAlg ℝ 3) (α γ b₀ : ℝ), u.coord 0 = 0 ∧ N u = 1 ∧
      b₀ = U.crystal.coord (hiIdx 0) ∧ α ^ 2 + γ ^ 2 ≠ 0 ∧
      (∀ v : CDAlg ℝ 4, v.coord 0 = 0 →
          hessQuad U.crystal v
            = 8 * (1 - b₀ ^ 2) * N (eigDir α γ (transComp α γ u v))) ∧
      (∀ e : CDAlg ℝ 3, e.coord 0 = 0 → bil u e = 0 →
          hessQuad U.crystal (eigDir α γ e)
            = 8 * (1 - b₀ ^ 2) * N (eigDir α γ e)) ∧
      (∀ (e : CDAlg ℝ 3) (x y z : ℝ), e.coord 0 = 0 → bil u e = 0 →
          hessQuad U.crystal (flatDir α γ u e x y z) = 0) := by
  obtain ⟨u, α, γ, b₀, hu0, hNu, hlo, hhi, hk, hb⟩ := U.exists_param h
  refine ⟨u, α, γ, b₀, hu0, hNu, hb, hk, ?_, ?_, ?_⟩
  · intro v hv
    exact hessQuad_eq_transverse (u := u) (b₀ := b₀) hu0 hNu hv hlo hhi U.norm_one hk
  · intro e he hue
    exact hessQuad_eigDir (u := u) (b₀ := b₀) hu0 hNu he hue hlo hhi U.norm_one hk
  · intro e x y z he hue
    exact hessQuad_flatDir (u := u) (b₀ := b₀) hu0 hNu he hue hlo hhi U.norm_one hk x y z

/-- **At a pole the Hessian is identically zero** — the `rank 0` clause of #5. -/
theorem polePlus_hessian_eq_zero (v : CDAlg ℝ 4) : hessQuad polePlus.crystal v = 0 := by
  have h : polePlus.crystal = (1 : ℝ) • ell := by rw [one_smul]; rfl
  rw [h]
  exact hessQuad_pole_eq_zero 1 v

/-- **`hessian_spectrum_function_of_b0_sq` (#9).**  The transverse eigenvalue is a
    function of `b₀²` alone — stated where it belongs, about two UNIVERSES.

    If `U` and `U'` are non-pole universes whose crystals have the same squared
    pole coordinate `b₀² = (crystal.coord ℓ)²`, then ONE real number `λ` is the
    transverse coefficient of BOTH Hessian quadratic forms: for each universe there
    is a parametrisation `(u, α, γ)` with `Hess(v,v) = λ·‖P v‖²` in every imaginary
    direction `v`.  So the Hessian is blind to the sign of `b₀` and to the `(α, γ)`
    phase; it separates the `b₀²` level sets and nothing finer (the confirmer's
    row-12 correction).

    (This replaces an earlier version whose statement was the real-number identity
    `8(1−b₀²) = 8(1−b₀'²)` — no universe, no crystal, no `hessQuad` appeared in it;
    Red Team F6, PR #663.  The tautology is deleted, not renamed.) -/
theorem universe_hessian_eigenvalue_depends_only_on_b0_sq
    (U U' : Universe) (h : U.NonPole) (h' : U'.NonPole)
    (hb : U.crystal.coord (hiIdx 0) ^ 2 = U'.crystal.coord (hiIdx 0) ^ 2) :
    ∃ lam : ℝ,
      (∃ (u : CDAlg ℝ 3) (α γ : ℝ), u.coord 0 = 0 ∧ N u = 1 ∧ α ^ 2 + γ ^ 2 ≠ 0 ∧
          ∀ v : CDAlg ℝ 4, v.coord 0 = 0 →
            hessQuad U.crystal v = lam * N (eigDir α γ (transComp α γ u v))) ∧
      (∃ (u' : CDAlg ℝ 3) (α' γ' : ℝ), u'.coord 0 = 0 ∧ N u' = 1 ∧ α' ^ 2 + γ' ^ 2 ≠ 0 ∧
          ∀ v : CDAlg ℝ 4, v.coord 0 = 0 →
            hessQuad U'.crystal v = lam * N (eigDir α' γ' (transComp α' γ' u' v))) := by
  obtain ⟨u, α, γ, b₀, hu0, hNu, hb0, hk, hT, -, -⟩ := universe_hessian_eigenvalue U h
  obtain ⟨u', α', γ', b₀', hu0', hNu', hb0', hk', hT', -, -⟩ := universe_hessian_eigenvalue U' h'
  have hsq : b₀' ^ 2 = b₀ ^ 2 := by rw [hb0', hb0]; exact hb.symm
  refine ⟨8 * (1 - b₀ ^ 2), ⟨u, α, γ, hu0, hNu, hk, hT⟩, ⟨u', α', γ', hu0', hNu', hk', ?_⟩⟩
  intro v hv
  rw [hT' v hv, hsq]

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
    (`φ ℓ = ℓ` covers the whole G₂ side and, inside `S₃` — under Brown's
    description `Aut(𝕊) = G₂ × S₃`, which is not claimed here — the rotations:
    the identity and the two order-3 elements; the three reflections, of which
    `gradeAut` is one, send `ℓ ↦ −ℓ` and are handled separately.  See §11.) -/
theorem hosting_equivariant (φ : CDAut 4) (hφ : φ ell = ell) (U : Universe) :
    IsVacuum (φ U.crystal) ∧ φ U.crystal ∈ StateSphere ∧
      ∀ x ∈ U.hosted, φ x ∈ (U.map φ).hosted := by
  refine ⟨aut_map_isVacuum φ U.isVacuum, stateSphere_map_mem φ U.mem.1, fun x hx => ?_⟩
  exact (aut_hosting_equivariant φ hφ U.isVacuum).2 x hx

/-- **The ℤ/2 of the `S₃` side.**  The grade automorphism `gradeAut` (`ℓ ↦ −ℓ`)
    moves `ℓ`, so `hosting_equivariant` does not cover it — but the hosted
    algebra is generated by `{1, s, ℓ}` and `−ℓ` generates the same algebra
    (`CrystalHosting.gradeAut_hosting_equivariant`), so hosting is equivariant
    under it all the same.  The order-3 elements of `S₃` fix `ℓ`, so they are a
    case of `hosting_equivariant`; the explicit construction is
    `CrystalHosting.rotAut3`, and `hosting_equivariant_rot3` below records it. -/
theorem hosting_equivariant_grade (U : Universe) :
    IsVacuum (gradeAut U.crystal) ∧ gradeAut U.crystal ∈ StateSphere ∧
      ∀ x ∈ U.hosted, gradeAut x ∈ (U.map gradeAut).hosted := by
  refine ⟨aut_map_isVacuum gradeAut U.isVacuum, stateSphere_map_mem gradeAut U.mem.1,
    fun x hx => ?_⟩
  exact (gradeAut_hosting_equivariant U.isVacuum).2 x hx

/-- **The order-3 elements of the `S₃` side.**  `CrystalHosting.rotAut3` is an
    explicit automorphism `ρ` of 𝕊 with `ρ³ = id`, `ρ ≠ id` and `ρ ℓ = ℓ`
    (`CrystalHosting.rotAut3_pow_three`, `rotAut3_ne_id`, `rotAut3_ell`), so it is
    a case of `hosting_equivariant`.  With `hosting_equivariant_grade` for the
    reflection `gradeAut`, both classes of the `S₃` factor now have a named
    witness.  (That `gradeAut` and `ρ` *generate* `S₃`, and that
    `Aut(𝕊) = G₂ × S₃` — Brown 1967 — are classical facts, NOT formalised here.) -/
theorem hosting_equivariant_rot3 (U : Universe) :
    IsVacuum (rotAut3 U.crystal) ∧ rotAut3 U.crystal ∈ StateSphere ∧
      ∀ x ∈ U.hosted, rotAut3 x ∈ (U.map rotAut3).hosted :=
  hosting_equivariant rotAut3 rotAut3_ell U

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
* **That `Aut(𝕊) = G₂ × S₃`, and that the named automorphisms generate the `S₃`.**
  What *is* proved: `hosting_equivariant` covers every `φ` with `φ ℓ = ℓ`,
  `hosting_equivariant_grade` covers the reflection `gradeAut` (`ℓ ↦ −ℓ`), and
  `hosting_equivariant_rot3` covers the explicit order-3 automorphism
  `CrystalHosting.rotAut3` (`ρ³ = id`, `ρ ≠ id`, `ρ ℓ = ℓ`).  In the `S₃ ≅ D₃`
  description of `Aut(𝕊)/G₂` (Brown 1967; `analysis/473-dirac-probe/aut_s3.py`) an
  element acts on `Im 𝕊 = Im 𝕆 ⊕ ℝℓ ⊕ (Im 𝕆)ℓ` by a matrix `M ∈ O(2)` on the
  multiplicity space of the `7` together with the scalar `det M` on `ℓ`; the
  order-3 elements are the rotations by `±120°`, so they **fix `ℓ`** (it is the
  three reflections that move it — `gradeAut` is one of them).  What is NOT proved
  here: Brown's structure theorem itself, and that `gradeAut` together with `ρ`
  exhaust the `S₃` factor.  Owner: #639 (e).
* **The boundary of a universe.**  POST-boundary-encoding (AXIOM-2, re-rooted) says each universe has an
  encoding octonion, at the level DERIV-encoding-level derives; the `Universe` structure
  above carries NO boundary field and no holography semantics.  The identification of
  `ℍ_s` with "the observer's ℍ" is POST-observer-associativity, an OPEN root (flag-3
  split, ruling bundle v0.7 §2; nothing ruled).  Owner: #473 / #639 (open question 2).
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
#print axioms Universe.nonPole_iff
#print axioms polePlus_not_nonPole
#print axioms Universe.hosted_eq_quatSpan
#print axioms universe_intersection_eq_complex
#print axioms loOf_e1_mem_universeSpace
#print axioms genericUniverse_nonPole
#print axioms exists_nonPole_universe
#print axioms Universe.exists_param
#print axioms potential_taylor_at_universe
#print axioms deriv2_potential_at_universe
#print axioms universe_hessian_eigenvalue
#print axioms polePlus_hessian_eq_zero
#print axioms universe_hessian_eigenvalue_depends_only_on_b0_sq

-- Data definitions that use choice / classical reasoning, printed for completeness.
#print axioms normalise
#print axioms Universe.dir
#print axioms hosting_equivariant_grade
#print axioms hosting_equivariant_rot3

end QBP.Substrate.Hosting
