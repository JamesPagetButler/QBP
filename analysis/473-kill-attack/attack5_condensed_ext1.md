# Kill-attack 5 — the condensed/Ext¹ route to Prop 13(b)

**Target.** `KILLED-locale-forcing-route`, reversal clause **Prop 13(b)**: *"a mechanism
that supplies the dynamical rule from topological or measure-theoretic data."*
**Vehicle.** The ledger's own surviving candidate `CONJ-condensed-math-for-transition-state`
(status `marginal`; no kill, no `testable_when`).
**Mandate.** Definition-first. The object is undefined today; the deliverable is a
DEFINITION and a KILL, so the conjecture can be tested.
**Author.** lean-prover seat, worktree `probe-kill-5`, branch `research/473-kill-attack-5`,
2026-09-24.

---

## 0. Verdict table (read this first)

| # | Question | Verdict |
|---|---|---|
| V1 | Is a condensed in-flight object *definable* on today's QBP substrate objects? | **YES** — three candidates given (§3): D1 sublevel/vacuum cofiber, D2 zero-divisor cofiber, D3 hosting bundle. |
| V2 | Is any of them *computable* in Lean with the pinned Mathlib? | **NO.** Mathlib has `CondensedAb`, `Condensed.freeAb`, abelian + AB4/AB5 structure, `Abelian.Ext`, `Sheaf.H` — but **zero** computed Ext/cohomology for any condensed object, no `EnoughProjectives (CondensedAb)`, no LTE. Everything is *definable*, nothing is *evaluable*. (§2) |
| V3 | Can any of them depend on the RULE? | **NO — rule-independent by construction.** All three are functors of `(𝕊, N, V)`, in fact of the closed pair `(Σ, M)`; the rule is not an argument. (§4) |
| V4 | Sub-conjecture (a) — "𝕆→ℍ as an inverse system, ℍ the limit, 𝕆 the parent" — well-typed? | **Two readings. Limit reading: well-typed but VACUOUS** (every subalgebra is the limit of the 2-term system). **Projection reading: PROVABLY IMPOSSIBLE** (𝕆 is simple ⇒ no algebra hom 𝕆 ↠ ℍ). Honest replacement in §5.1. |
| V5 | Sub-conjecture (b) — "Ext¹(ℍ_cond, 𝕆_cond) ≠ 0 in flight, = 0 at the limit" | **ILL-POSED as written** (no time/state variable occurs in the expression; both arguments are rigid objects) and, under its most charitable repair (deformation theory), **identically zero** (ℍ is separable ⇒ rigid). (§5.2) |
| V6 | Sub-conjecture (c) — "horizon formation, finite Ext¹ parametrising the formation rate" | **KILLED as a rule-supplier.** An Ext group carries no clock; a *rate* has units 1/T and needs a prior dynamical rule. Also: the substrate has no horizon object at all. (§5.3) |
| V7 | **Prop 13(b) via this route** | **NOT DELIVERED. The kill survives.** The route is caught in a dilemma (§4.3): built from `V` ⇒ rule-blind; built from the flow ⇒ the rule is an input. There is no third horn. |
| V8 | Is there anything the condensed/pointless machinery *is* good for here? | **YES, and it is the opposite of the conjecture's claim:** the orbit space of the rule is a genuinely non-Hausdorff quotient — that is where pointless/condensed/NCG methods earn their keep. It presupposes the rule; it does not supply it. (§4.4) |

**One-sentence result.** *Every object this route can build is a function of the potential's
level-set topology; a Lean theorem proved here shows the potential's first-order data
constrains exactly **1 of the 14** tangential directions a rule may point in at any
in-flight state, leaving a **13-dimensional** family of rule deformations that no
level-set invariant — condensed or classical — can see; therefore no such invariant can
supply the rule.*

---

## 1. Ground truth: the objects on record

From `proofs/QBP/Substrate/Hosting.lean` (definition file; beekeeper lift 2026-09-07) and
`proofs/QBP/Substrate/RuleFlow.lean` (#635, the rule is a POSTULATE):

| Object | Definition | Status |
|---|---|---|
| Substrate `Σ` | `StateSphere = {s : CDAlg ℝ 4 | s.coord 0 = 0 ∧ N s = 1}` = `S¹⁴ ⊂ Im 𝕊` | Lean def |
| Potential `V` | `potential s = N (cdLo s * cdHi s − cdHi s * cdLo s) = ‖[a,b]‖²` | Lean def; `contDiff_potential` (C^∞, a quartic) |
| Universes `M` | `UniverseSpace = {s ∈ Σ ∧ IsVacuum s} = {V = 0}` | Lean def; `mem_universeSpace_iff_potential` |
| In-flight | `InFlight = {s ∈ Σ ∧ ¬IsVacuum s} = {V > 0}` | Lean def; inhabited (`inFlight_nonempty`) |
| ZD locus `Z` | `{V = 1}` on `Σ` (the argmax `{V = N²}`) | `ruleField_eq_zero_of_potential_eq_one` |
| The rule | `ruleField s = −(∇V − ⟪∇V,s⟫s − (∇V)₀·1)` — **POSTULATE** | `RuleFlow` §5 |
| Hosting | every crystal generates `⊆ span{1, ℓ, u, ℓu} ≅ ℍ` | `PROOF-crystal-hosts-quaternion` |
| No hosting in flight | on `InFlight` the scalar-spectrum identity provably FAILS | `inFlight_no_quaternion_closure` |
| Discriminator | quench `⟨b₀²⟩ = 0.146` vs anneal `1/3` | numerical, #637 |

`Hosting.lean` §11 already owns the gap this attack probes, verbatim:

> **A "pointless" description of the in-flight region.** `InFlight` is a plain `Set`; no
> locale, condensed object or limit of finite approximations is built. Owner: #636 / #639
> (open question 3).

### 1.1 Prerequisites — what exists, what does not (checked, not assumed)

| # | Prerequisite for any condensed construction | Status in the repo |
|---|---|---|
| 1 | `Σ` is compact Hausdorff (needed to form `CompHaus.of Σ` at all) | **PROVED — but in the Substrate layer.** `RuleFlow.isClosed_stateSphere`, `RuleFlow.isCompact_stateSphere` (`#print axioms` clean). They live in `QBP.Substrate.RuleFlow` and depend on its **scoped** `instNormedAddCommGroupCD` / `instInnerProductSpaceCD`. `Foundations` carries no topology on `CDAlg ℝ n` by design, so any condensed object over `Σ` is a **Substrate-layer artefact** needing its own beekeeper lift — and re-introducing a Foundations-level normed structure risks an instance diamond with the scoped one. |
| 2 | `M = {V=0}` and `Z = {V=1}` are closed in `Σ` | **NOT STATED**, though one line away in the same scoped setting: `contDiff_potential.continuous` + `isClosed_eq` (exactly the pattern used at `RuleFlow.lean:1459`). No `IsClosed UniverseSpace` / `IsClosed InFlight` exists. |
| 3 | The homotopy/cohomology type of `M` | **UNKNOWN.** Nothing in the repo computes `H^*(M)`, `π₀(M)`, or even whether `M` is connected. The ledger records only that the `Aut(𝕊)`-quotient of the vacuum `S²` is the orbifold `S²(2,2,3)` (Prop 15, elementary/numerical, #634 AC3). **Every invariant in §3 is a function of this unknown.** |
| 4 | Continuity (even measurability) of the hosting direction `s ↦ u(s)` | **UNPROVEN.** `Universe.dir` is a `Classical.choose`; `Universe.dir_spec` asserts no uniqueness, "not even up to sign". So D3 (§3.3) is not known to be a bundle, or even a Borel family. |

Items 3 and 4 are the honest cost floor of the conjecture, before a single Ext group is
written; items 1 and 2 are cheap but land the whole construction in the Substrate layer.

---

## 2. (A) Survey — the condensed API in the pinned Mathlib

Pin: `lean-toolchain = leanprover/lean4:v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Inspected under `proofs/.lake/packages/mathlib/Mathlib/`.

### 2.1 What EXISTS

| Item | Location | Note |
|---|---|---|
| `Condensed C := Sheaf (coherentTopology CompHaus.{u}) C` | `Condensed/Basic.lean` | |
| `CondensedSet := Condensed.{u} (Type (u+1))` | `Condensed/Basic.lean` | |
| `CondensedMod R := Condensed.{u} (ModuleCat.{u+1} R)`; `Abelian` instance | `Condensed/Module.lean` | |
| **`CondensedAb := CondensedMod.{u} (ULift ℤ)`** | `Condensed/Module.lean:63` | the ledger's `Cond(Ab)` |
| **`Condensed.freeAb : CondensedSet ⥤ CondensedAb`** (= `ℤ[−]`), with `setAbAdjunction` | `Condensed/Module.lean:71,74` | the free condensed abelian group |
| `compHausToCondensed`, `profiniteToCondensed`, `stoneanToCondensed`; **`Full` + `Faithful`** | `Condensed/Functors.lean` | `CompHaus ↪ Cond` |
| `TopCat.toCondensedSet`, `condensedSetToTopCat`, the CG adjunction with **invertible counit** | `Condensed/TopCatAdjunction.lean` | used by `PROOF-spatial-first-link-condensed-locale` |
| `HasLimits`/`HasColimits (CondensedMod R)`, finite (co)limits | `Condensed/Limits.lean` | ⇒ **cokernels exist**; §3's objects are constructible |
| AB5, AB4, AB4* for condensed modules | `Condensed/AB.lean` | |
| `IsGrothendieckAbelian (Sheaf J A)` for `A` Grothendieck + `HasSheafify` | `CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean:74` | ⇒ `CondensedAb` is Grothendieck abelian |
| `instance IsGrothendieckAbelian.hasExt` | `CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean:36` | ⇒ **`HasExt` holds for `CondensedAb`**, so `Abelian.Ext X Y n` is *defined* there |
| `Abelian.Ext X Y n` (derived-category definition, `HasExt.{w}`) | `Algebra/Homology/DerivedCategory/Ext/Basic.lean` | plus `Ext.EnoughInjectives`, `ExactSequences`, `Linear`, `ExtClass` |
| `CategoryTheory.Ext R C n` (left-derived `linearYoneda`, needs `EnoughProjectives`) | `CategoryTheory/Abelian/Ext.lean:43` | the *older* Ext; unusable for condensed (no `EnoughProjectives`) |
| **`Sheaf.H F n`** — sheaf cohomology as `Ext` from the constant sheaf `ℤ` | `CategoryTheory/Sites/SheafCohomology/Basic.lean` | applies verbatim to condensed abelian sheaves |
| Discreteness: `Condensed.discrete ⊣ underlying`, `isDiscrete_tfae` | `Condensed/Discrete/*` | Asgeirsson's characterisation |
| Site comparisons `Stonean ≃ Profinite ≃ CompHaus` (coherent) | `Condensed/Equivalence.lean` | |
| `Condensed.Explicit` — the explicit sheaf condition (finite products + one equaliser) | `Condensed/Explicit.lean` | the only genuinely *checkable* thing here |
| `LightCondensed`, `LightCondSet`, `LightCondMod`, `Sequence`, `InternallyProjective` | `Condensed/Light/*` | the metrisable/countable variant |
| `Condensed.Solid` (definition only) | `Condensed/Solid.lean` | with two `TODO (hard)` markers |

### 2.2 What does NOT exist

* **No `EnoughProjectives (CondensedAb)`.** `grep -rn "Projective" Mathlib/Condensed/` returns
  only `Light/InternallyProjective.lean`. The Clausen–Scholze fact that `ℤ[S]` is projective
  for `S` extremally disconnected — the *entire* computational engine of condensed homological
  algebra — is absent.
* **No computed `Ext` for any condensed object.** No vanishing theorem, no long exact sequence
  instance, no example. `Abelian.Ext X Y n` for `X Y : CondensedAb` type-checks and is then an
  opaque `Type w` with an `AddCommGroup`; nothing in Mathlib evaluates it.
* **No Liquid Tensor Experiment.** LTE is a separate ~90k-line development; only its
  *abelian-category prerequisites* landed. The ledger's
  `REF-condensed-categorical-foundations-mathlib` claim that this "makes Ext computations in
  Cond(Ab) tractable in QBP's Lean environment" is **an overstatement** and should be corrected:
  it makes the *category* available, not the *computations*. (Flagged, §7 item 3.)
* **No comparison theorem** `RΓ(X_cond, ℤ) ≃ RΓ_sheaf(X, ℤ)` for compact Hausdorff `X`
  (the theorem that makes condensed cohomology *mean* anything topological).
* **No condensed real/liquid vector spaces**, hence nothing about `Ext¹_{Cond(Ab)}(ℝ, ℝ)`.

### 2.3 Two findings for the ledger

* **`REF-pyknotic-condensed-topos-status` is confirmed against the pin.** `Condensed/Basic.lean`
  says, verbatim: *"Note: Our definition more closely resembles 'Pyknotic objects' in the sense
  of Barwick-Haine, as we do not impose cardinality bounds, and manage universes carefully
  instead."* Mathlib's `Condensed` is the pyknotic-style universe-managed object, exactly as
  the ledger anchor says. Good.
* **`REF-condensed-categorical-foundations-mathlib` overstates tractability** (§2.2). Proposed
  correction text in §7.

### 2.4 Computability verdict

> In the pinned Mathlib one can **write down** every object in §3 and **state** every Ext group
> the conjecture asks about. One can evaluate **none** of them. The gap is not a few lemmas; it
> is `EnoughProjectives` + the compact-Hausdorff comparison theorem + a relative-cohomology
> computation for a manifold-pair nobody has identified (§1.1 item 3). Cost estimate: LTE-scale.

---

## 3. (B) Candidate definitions of the in-flight object

All three are stated honestly: what the object is, what it is built from, and what it forgets.

### 3.1 D1 — the sublevel filtration and the vacuum cofiber

**The filtration (the well-typed "inverse system").**
For `ε > 0` put `Σ_ε := {s ∈ Σ | V s ≤ ε}`. Each `Σ_ε` is closed in the compact Hausdorff `Σ`,
hence compact Hausdorff. `ε ↦ Σ_ε` is a **cofiltered inverse system in `CompHaus`** ordered by
`ε' ≤ ε ⇒ Σ_{ε'} ⊆ Σ_ε`, and
`lim_{ε→0} Σ_ε = ⋂_{ε>0} Σ_ε = V⁻¹(0) = M`
(the inverse limit of a nested family of closed subsets of a compact Hausdorff space is the
intersection). **This is the honest version of sub-conjecture (a): an inverse system of compact
Hausdorff SPACES whose limit is the vacuum manifold — not an inverse system of algebras.**

**The condensed object.** Apply the fully faithful `compHausToCondensed`, then
`Condensed.freeAb = ℤ[−]`:

```
ℤ[M] ──ι──▶ ℤ[Σ_ε]     in CondensedAb
D1(ε) := coker ι                     (cokernels exist: Condensed/Limits.lean)
D1     := D1(ε) for ε ≥ max V = 1, i.e. coker(ℤ[M] → ℤ[Σ])
```

**What D1 is.** By the standard condensed identity for a closed immersion
`Y ↪ X` of compact Hausdorff spaces (Clausen–Scholze; **NOT in Mathlib**),
`coker(ℤ[Y] → ℤ[X]) ≅ ℤ̃[X/Y]`, the reduced free condensed abelian group on the pointed
quotient. So **D1 = ℤ̃[Σ/M]**: the free condensed abelian group on "the state sphere with all
universes collapsed to one point".

**Its invariants.** `Ext^i_{Cond(Ab)}(D1, ℤ)` is, by the compact-Hausdorff comparison
(**external input, not in Mathlib**), the ordinary **relative sheaf cohomology `H^i(Σ, M; ℤ)`**.
`Sheaf.H` gives the same thing intrinsically.

**What D1 forgets.** Everything about `V` except its zero set. `D1` is unchanged if `V` is
replaced by `f·V` for any continuous `f > 0`, by `V²`, by `V∘φ` for any homeomorphism `φ` of `Σ`
fixing `M` setwise — an infinite-dimensional family of different potentials with different
gradient flows. **This is the core of §4.**

### 3.2 D2 — the zero-divisor pair

Same construction with `Z := {V = 1}` (the argmax = the zero-divisor locus; every zero divisor
sits there, `RuleFlow` item 13) in place of `M`:
`D2 := coker(ℤ[Z] → ℤ[Σ]) ≅ ℤ̃[Σ/Z]`, invariants `H^i(Σ, Z; ℤ)`.
Physically the "ridge" rather than the "floor". Structurally identical, and identically blind:
`Z` is again a level set of `V`.

A **three-term** variant `ℤ[M] → ℤ[Σ_ε] → ℤ[Σ]` gives a long exact sequence relating
`H^*(Σ, M)`, `H^*(Σ, Σ_ε)`, `H^*(Σ_ε, M)` — this is Morse theory in cohomological dress (§6),
and is the most information the route can produce. It is classical, and rule-blind.

### 3.3 D3 — the hosting bundle (the honest replacement for (a))

Over `M` each crystal `s` hosts a quaternion algebra: `PROOF-crystal-hosts-quaternion` gives a
direction `u(s)` with `hosted(s) ⊆ span{1, ℓ, u(s), ℓ·u(s)} ≅ ℍ`, a *proper* 4-dimensional
subalgebra of `𝕊`. Modulo the unproven continuity of `s ↦ u(s)` (§1.1 item 4), this is a map

```
h : M ⟶ { 4-dimensional subalgebras of 𝕊 } ⊂ Gr₄(𝕊)
```

i.e. a **bundle of ℍ's over the vacuum manifold**, equivalently a sheaf of condensed
ℝ-algebras on `M_cond`. Over `InFlight` there is *no* such algebra: `inFlight_no_quaternion_closure`
says the scalar-spectrum identity provably fails there.

**The would-be Ext¹.** "Extend the hosting sheaf from the closed `M` across `Σ`" is an
extension problem, and such problems do have cohomological obstructions in `H¹`. **But here the
obstruction theory is void, not nonzero:** the fibre of the classifying problem is *empty* over
every in-flight point (no 4-dimensional subalgebra containing `{1, s, ℓ}` exists at all), which
is a pointwise non-existence, not a global obstruction class. There is no `H¹` to compute
because there is no candidate local section to glue. **This kills the (a)-repair as an Ext
source too.**

---

## 4. (C) Rule-dependence — the decisive analysis

### 4.1 The structural statement

Let `𝒟 = (𝕊, N, V)` be the algebra-supplied data and let `R` range over admissible rules
(smooth vector fields on `Σ`; the postulate `R = ruleField` is one point of that space).
D1, D2, D3 are each of the form `Φ(𝒟)` — in fact `Φ(Σ, M)` or `Φ(Σ, Z)`, a functor of a pair of
compact Hausdorff spaces. **`R` is not an argument of `Φ`.** Therefore for any invariant `I`
(Ext¹, H¹, cokernel, homotopy type, Euler characteristic, anything):

> `I(Φ(𝒟))` is **constant** as `R` varies. Two rules with different physics — quench
> `⟨b₀²⟩ = 0.146` and anneal `1/3` — give **literally the same object, the same term, the same
> Ext groups**.

An invariant that is constant across the alternatives cannot select among them. **A rule-blind
object cannot be a Prop 13(b) mechanism.** Said plainly, as the mandate asks: *this is true, and
it is the likely outcome the driver anticipated.*

### 4.2 The quantitative version — proved in Lean here

The qualitative statement above is definitional. Its quantitative form is a theorem, and it is
the Lean deliverable of this attack (`proofs/QBP/Foundations/TransitionState.lean`, §8 below):

Fix an in-flight state `s ∈ Σ` and let `g := ∇V(s)` (`RuleFlow.gradV`; `fderiv V s v = bil v g`
by `RuleFlow.fderiv_potential_apply`). Then

* `Tangent s` — directions keeping a curve on `Σ` and inside `Im 𝕊` to first order — has
  **`finrank = 14`** (`finrank_tangent`);
* `VNeutral s g` — those that additionally leave `V` stationary to first order — has
  **`finrank = 13` exactly** whenever `g` is tangential and nonzero (`finrank_vNeutral`), and
  **`= 14`** when `g = 0`, i.e. at every crystal (`vNeutral_eq_tangent_of_gradient_zero`);
* adding any `VNeutral` field to a rule field preserves the sphere, the imaginary part **and
  the exact first-order rate of change of `V`** (`add_vNeutral_preserves_data`), while changing
  the rule (`exists_vNeutral_ne_zero`, `add_vNeutral_ne`).

**The inference.** Any selection principle expressible in the data of §3 sees a candidate rule
`F` only through its effect on `V` — i.e. at first order only through `dV(F) = ⟪∇V, F⟫`. (A
level-set/sublevel/cofiber invariant is a functional of `V`'s topology, which is weaker still.)
Hence the solution set of any such principle is closed under adding an arbitrary `VNeutral`
field:

> **The V-and-topology data constrains at most 1 of the 14 tangential degrees of freedom per
> point. Thirteen are free — a 13-dimensional family of rule deformations per point, invisible
> to every condensed or classical invariant of `V`.**

That is `13/14` of the rule left undetermined, pointwise, and the undetermined part is exactly
the part that moves a trajectory *along* a level set and therefore changes which crystal it
lands on — which is precisely what `⟨b₀²⟩` measures.

### 4.3 The dilemma (why there is no third horn)

| Horn | Construction | Consequence |
|---|---|---|
| **1** | The object is built from `(𝕊, N, V)` and topology only (D1, D2, D3) | **Rule-blind by construction** (§4.1–4.2). No rule supplied. **KILL.** |
| **2** | The object is built from the flow (orbit space, reachable set, ω-limit map) | The rule is an **input**. Condensed math is then a *language*, not a *mechanism* — the Prop 8 "relocates the mystery" failure. |
| **3** | A variational/monotonicity criterion on a topological invariant selects the rule | **Too coarse, provably.** Quench and anneal both descend `V`; they differ by the schedule/noise, i.e. by motion *within* level sets — exactly the 13 directions §4.2 shows are invisible. Any criterion phrased in `V`'s level sets is constant on that 13-dimensional family. |

No fourth horn is available without adding data that is neither topological nor
measure-theoretic — at which point Prop 13(b) is not what is being satisfied.

### 4.4 Where the machinery *does* earn its keep (honest positive finding)

Horn 2 is circular for Prop 13(b), but it is not scientifically empty, and it is worth saying
where the value actually is:

* Every space in §3 is **spatial** (compact Hausdorff), and every quotient in sight is too: the
  relevant symmetry group `G₂ × S₃` (Brown 1967, cited not proved) is **compact**, so the orbit
  space `Σ/Aut(𝕊)` is again compact Hausdorff — the ledger's own `S²(2,2,3)` orbifold. Condensed
  mathematics is **conservative** on spatial inputs: its cohomology of a compact Hausdorff space
  is ordinary sheaf cohomology. **So on every object the conjecture names, condensed math
  returns classical topology and no new physical quantity** — which contradicts the
  conjecture's own selling point ("a new physical quantity not present in classical NCG").
* The **one** genuinely non-spatial object in the vicinity is the **orbit space of the rule**:
  the quotient of `Σ` by the flow is non-Hausdorff (an orbit limiting on a rest point cannot be
  separated from it), so it is a *bad quotient* — precisely the setting for pointless topology,
  topos theory and Connes' NCG. `INSIGHT-locale-condensed-chain`'s "pointless in-flight regime"
  intuition is therefore **right about where the pointlessness lives and wrong about what it
  does**: it lives in the quotient by the dynamics, and it presupposes the dynamics.

---

## 5. Sub-conjecture adjudication

### 5.1 (a) "the 𝕆→ℍ crystallisation is an inverse system … ℍ is the inverse limit, 𝕆 is the parent"

Two readings, both fatal, in opposite ways.

**Reading 1 (literal: limit).** An inverse system `A₀ ← A₁ ← A₂ ← …` of finite-dimensional real
algebras with `A₀ = 𝕆` and `lim = ℍ`. This is **well-typed**: the two-term system
`ℍ ↪ 𝕆` already realises it (`lim` of a system with a terminal-ish tail is the tail). It is also
**vacuous**: *every* subalgebra of *every* algebra is such a limit, so the statement carries no
information about crystallisation. And "condensed" adds nothing whatsoever: all objects are
finite-dimensional real vector spaces, on which the condensed functor is fully faithful and the
condensed structure is the ordinary topology.

**Reading 2 (the one QBP prose usually implies: projection `𝕆 → ℍ`).** **Provably impossible.**
`𝕆` is a *simple* non-associative ℝ-algebra (its only two-sided ideals are `0` and `𝕆`), so any
algebra homomorphism out of `𝕆` is either zero or injective. An injective map `𝕆 → ℍ` is
impossible on dimension grounds. **There is no nonzero algebra map `𝕆 → ℍ`.** So "crystallisation
as a map from 𝕆 onto ℍ" is not a morphism in any algebra category, condensed or not.

**Honest replacement.** Crystallisation is **subalgebra selection**, not projection and not a
limit. The moduli object is the space of quaternion subalgebras of `𝕆`, which is the compact
homogeneous space `G₂/SO(4)` (dimension `14 − 6 = 8`); in `𝕊` the corresponding object is
QBP's own **hosting bundle D3** over the vacuum manifold (`PROOF-crystal-hosts-quaternion`). The
in-flight region is where *no* point of that moduli space is available
(`inFlight_no_quaternion_closure`). This replacement is a **kinematic arena**, and it is
rule-independent — it is the object QBP already built.

### 5.2 (b) "Ext¹(ℍ_cond, 𝕆_cond) non-zero in flight, zero at the limit, parametrising a physical quantity"

**Defect 1 — ill-posed.** `Ext¹(X, Y)` is a bifunctor of two objects. The expression
`Ext¹(ℍ_cond, 𝕆_cond)` contains **no time, state, or process variable**. "Non-zero during
crystallisation and zero at the limit" ascribes a `t`-dependence to an expression whose
arguments are `t`-independent. To make the phrase meaningful one needs a *family* `X_t, Y_t`;
`ℍ` and `𝕆` are rigid finite-dimensional algebras and no such family is on offer.

**Defect 2 — the abelian reading is a universal constant.** As objects of `CondensedAb`,
`ℍ_cond ≅ ℝ_cond^4` and `𝕆_cond ≅ ℝ_cond^8`, so by additivity
`Ext¹_{Cond(Ab)}(ℍ_cond, 𝕆_cond) ≅ Ext¹_{Cond(Ab)}(ℝ, ℝ)^{32}`.
Whatever that group is (Mathlib does not know; condensed real vector spaces are the very thing
liquid/solid theory exists to tame), it is a **universal constant of the category** — the same
for every state, every rule, every time. It cannot parametrise any physical quantity. Note the
ledger's own `predicted_unit` for this conjecture is *"Ext¹ groups computed in condensed
abelian-group category"* — **a group is not a unit**; nothing can be compared to a measurement.

**Defect 3 — the charitable repair is identically zero.** The reading that would make (b)
*mean* what it wants is deformation theory: is there an infinitesimal deformation parameter for
the pair `(ℍ ⊂ 𝕆)`? The relevant group is Hochschild `HH²`. But **ℍ is a separable
ℝ-algebra** (central simple; `ℍ ⊗_ℝ ℂ ≅ M₂(ℂ)`), and for a separable algebra
`HH^n(A, M) = 0` for all `n ≥ 1` and all bimodules `M`. **ℍ is rigid: it has no nontrivial
infinitesimal deformations.** (`𝕆` is likewise rigid as an alternative algebra — its derivation
algebra `𝔤₂` is semisimple.) So the deformation-theoretic `Ext¹` the conjecture wants is not
"non-zero in flight, zero at the limit": it is **zero, always**. A technical caveat, recorded
for honesty: `𝕆` is a left ℍ-module and a right ℍ-module but **not** an ℍ-*bimodule* — with the
Cayley–Dickson product `(a·x)·b ≠ a·(x·b)` for `a, b ∈ ℍ`, `x ∈ 𝕆` (it would force
`ab̄ = b̄a`) — so `HH^*(ℍ, 𝕆)` must be taken with `𝕆` replaced by an honest bimodule; the
rigidity conclusion for `ℍ` itself (`HH²(ℍ, ℍ) = 0`) is unaffected and is the load-bearing one.

**Disposition.** (b) **dies as written** and **dies under repair as a deformation parameter**.
What survives is only the possibility of a *descriptor*: `H^*(Σ, M)` (D1) is a well-defined
invariant of the landscape — a fact about the arena, with no rule content. Keeping (b) requires
restating it as "the relative cohomology of the pair (state sphere, vacuum manifold) is a
well-defined invariant of the landscape", which is true, computable in principle, unknown today
(§1.1 item 3) — and rule-blind.

### 5.3 (c) "horizon formation is a topology change; finite Ext¹ parametrises the formation rate"

**Defect 1 — no object.** The substrate has no spacetime, no metric and no horizon.
`Hosting.lean` states explicitly that `Universe` carries **no boundary field** and that "no
boundary and no holography semantics" are formalised. There is nothing whose topology could
change. (c) is not currently a statement about any defined object in QBP.

**Defect 2 — an Ext group has no clock.** A *rate* has dimensions `1/T`. An Ext group is a
discrete abelian group attached to time-independent data; it has no units and no time parameter.
To extract a rate one must differentiate along a trajectory — i.e. one must **already have the
rule**. **This is the clean kill for (c) as a Prop 13(b) mechanism:** the proposed output (a
rate) presupposes the input it claims to supply.

**Defect 3 — if the topology change is real, the right tool is Morse theory, not Ext.** See §6.

### 5.4 (d) "higher-order harmonics are stalks of a condensed sheaf on a site of scales"

Not probed in this attack (out of the assigned scope). Recorded so the kill text does not
silently include it: (d) is untouched here and remains unadjudicated.

---

## 6. (D) Where a HOMOTOPY-TYPE formulation is the natural one (note only — nothing built)

"Topology change of the level sets" is, verbatim, the subject of **Morse theory**, not of
condensed mathematics:

* The homotopy type of `Σ_ε = {V ≤ ε}` is constant on intervals of regular values and changes
  exactly at critical values of `V`, by attaching a cell of dimension = the Morse index. The
  invariant of "horizon formation as a topology change" is therefore the **Morse data of `V`**:
  the critical values in `(0, 1)`, their indices, and the attaching maps. `V = 1` (the
  zero-divisor locus) is the argmax, so it is the top of the landscape; `V = 0` is the minimum
  locus `M`; all the topology change is in between.
* This is a **homotopy-theoretic** statement and the repo already has a homotopy layer: the
  Agda side (`S3FromCD.S³-HSpace`, `SkyrmionCharge.agda` with `π₃(S³) ≅ ℤ`,
  `SubstrateCharge.agda` with `B(f ⋆ g) = B f + B g`). Cubical Agda is the natural place to
  state "the homotopy type of the sublevel set changes at `ε = c`" — as a pushout/HIT
  description — and degrees/H-space structure are already native there. Cond(Ab) would express
  the same content as `H^*(Σ_ε, Σ_{ε'})` and would be strictly less informative (cohomology
  forgets what the homotopy type remembers).
* **Recommendation (not executed): do not build the Cond(Ab) version. If the transition-state
  topology is to be studied at all, the first deliverable is `π₀`/`H^*` of the vacuum manifold
  `M` and the critical values of `V` — a Morse/numerical computation, not a categorical one.**
  Even then it is rule-blind (§4), so it is a description of the arena, not a route to Prop 13(b).

---

## 7. (E) PROPOSED kill and testable_when — schema v0.3.4 shape (PROPOSAL ONLY; not written to the ledger)

Schema note, stated honestly: in `docs/cth/inventory.schema.v0.3.json`
(`inventory.schema.v0.3.4.json`) the `kill_condition` array of `KillConditionEntry` is defined
on **`Axiom` / `MetaPrinciple` / `Interpretation`**, not on a plain `Anchor`;
`CONJ-condensed-math-for-transition-state` is a tier-3 `Anchor`, whose available fields are
`testable_when`, `discriminator`, `killed_by`, `killed_note`, `status`. The entry below is
written in `KillConditionEntry` shape as the mandate asks; **where it is attached is a ledger-side
decision, not mine.**

### 7.1 `testable_when` (the field the conjecture currently lacks)

```
"testable_when": "When ALL FOUR prerequisites exist: (i) the compact-Hausdorff structure of
StateSphere is available to the layer that builds the condensed object — it is PROVED
(RuleFlow.isCompact_stateSphere / isClosed_stateSphere) but only inside Substrate under a
SCOPED normed instance, so a condensed object over Sigma is a Substrate artefact needing its
own lift; (ii) the vacuum locus M = {V=0} and the zero-divisor locus Z = {V=1} are proved
closed (not stated anywhere today, one line from contDiff_potential.continuous); (iii) H^*(M;
Z) and the critical values of V on Sigma are computed — nothing in the repo knows even
whether M is connected, and EVERY invariant of the proposed object is a function of this;
(iv) Mathlib acquires EnoughProjectives for CondensedAb, or the compact-Hausdorff comparison
RGamma(X_cond, Z) = RGamma_sheaf(X, Z), without which no Ext group in Cond(Ab) is evaluable.
Until all four hold the conjecture has no computable content; and note that predicted_unit
'Ext-1 groups computed in condensed abelian-group category' is not a UNIT, so no value of it
can be compared with any measurement."
```

### 7.2 `kill_condition` entries (array; one per open question)

```jsonc
"kill_condition": [
  {
    "question": "(a) Is the 𝕆→ℍ crystallisation an inverse system of condensed real algebras with ℍ as the limit?",
    "kill": "FIRED. The limit reading is vacuous (every subalgebra is the limit of the 2-term system ℍ ↪ 𝕆, and condensedness adds nothing to finite-dimensional real algebras); the projection reading is impossible (𝕆 is simple, so no nonzero algebra map 𝕆 → ℍ exists). The honest object is subalgebra SELECTION — the moduli space G₂/SO(4), realised in QBP as the hosting bundle over the vacuum manifold.",
    "closure": "derivation",
    "discharge": "PROOF-crystal-hosts-quaternion",
    "trigger_issue": "QBP#473 (kill-attack 5), QBP#639"
  },
  {
    "question": "(b) Is Ext¹(ℍ_cond, 𝕆_cond) non-zero in flight and zero at the limit, parametrising a physical quantity?",
    "kill": "FIRED. The expression contains no time or state variable, so it cannot be 'non-zero during' anything; in Cond(Ab) it reduces by additivity to Ext¹(ℝ,ℝ)^32, a universal constant of the category identical for every state and every rule; and under the charitable deformation-theoretic repair it is identically zero, because ℍ is separable over ℝ, hence rigid (HH^n(ℍ,−) = 0 for n ≥ 1). A group is not a predicted_unit.",
    "closure": "derivation",
    "discharge": "QBP#473 analysis/473-kill-attack/attack5_condensed_ext1.md §5.2",
    "trigger_issue": "QBP#473"
  },
  {
    "question": "(c) Does horizon formation have finite Ext¹ parametrising the formation RATE?",
    "kill": "FIRED as a rule-supplier. An Ext group carries no clock: a rate has dimensions 1/T and can only be extracted by differentiating along a trajectory, i.e. by presupposing the dynamical rule the mechanism claims to supply. Independently, the QBP substrate contains no horizon, no metric and no boundary object (Hosting.lean states this explicitly), so (c) is not yet a statement about any defined object.",
    "closure": "ruling-rescope",
    "trigger_issue": "QBP#473, QBP#635"
  },
  {
    "question": "Does the condensed route satisfy KILLED-locale-forcing-route Prop 13(b) — supplying the rule from topological/measure-theoretic data?",
    "kill": "FIRED. Every object the route can define on the current substrate is a functor of (Σ, M) or (Σ, Z) — of V's level-set topology alone — so its invariants are constant as the rule varies; quench (⟨b₀²⟩ = 0.146) and anneal (1/3) give the identical object. Quantitatively (Lean, QBP.Foundations.TransitionState): at any in-flight state the tangent space is 14-dimensional and V's first-order data constrains exactly one direction, leaving a 13-dimensional family of rule deformations invisible to every level-set invariant. The kill stands.",
    "closure": "derivation",
    "discharge": "QBP.Foundations.TransitionState.finrank_vNeutral",
    "trigger_issue": "QBP#473"
  }
]
```

### 7.3 Two further ledger corrections proposed (not written)

1. `REF-condensed-categorical-foundations-mathlib` — description says the Mathlib work "makes
   Ext computations in Cond(Ab) tractable in QBP's Lean environment". **Overstated.** Proposed
   replacement clause: *"makes the CATEGORY Cond(Ab) available (CondensedAb, freeAb, abelian +
   AB4/AB5, HasExt via IsGrothendieckAbelian, Sheaf.H); Ext groups are thereby DEFINABLE but not
   EVALUABLE — Mathlib has no EnoughProjectives for CondensedAb, no computed condensed Ext, and
   no Liquid Tensor Experiment."*
2. `REF-pyknotic-condensed-topos-status` — **confirmed against the pin** (`Condensed/Basic.lean`
   says its definition "more closely resembles Pyknotic objects"). No change; worth recording
   `last_tested_at` = 2026-09-24 with this verification.
3. `CONJ-condensed-math-for-transition-state` — status: on this analysis (a), (b) and (c) are
   each killed in the senses above; (d) is untouched. A demotion from `marginal` is a
   ledger-side ruling, not mine; the evidence is §5.

---

## 8. The Lean deliverable

`proofs/QBP/Foundations/TransitionState.lean` (new; wired into `QBP/Foundations.lean`).
Layer-clean: imports Mathlib + `QBP.Foundations.{CDDimension, Alternator}` only; it does **not**
import `QBP.Substrate` (the identification `g = ∇V(s)` is a **citation** of
`RuleFlow.fderiv_potential_apply`, never an import).

| Theorem | Plain-maths statement |
|---|---|
| `finrank_tangent` | At an imaginary unit state `s`, the directions preserving `N` and `Im` to first order form a **14**-dimensional space. |
| `finrank_vNeutral` | Those additionally orthogonal to `g` (= `∇V(s)`, tangential and nonzero) form a **13**-dimensional space — the potential constrains **exactly one** of the fourteen. |
| `vNeutral_eq_tangent_of_gradient_zero` | At a rest point of the gradient (every crystal) the potential constrains **nothing**: all 14 directions are `V`-neutral. |
| `add_vNeutral_preserves_data` | Adding a `V`-neutral field to a rule field preserves the sphere, the imaginary part, **and the exact first-order rate of change of `V`**. |
| `exists_vNeutral_ne_zero`, `add_vNeutral_ne` | Such a deformation genuinely exists and genuinely changes the rule. |
| `hypotheses_satisfiable`, `finrank_counts_instantiated` | **Anti-vacuity guard:** a concrete `s = e₁`, `g = e₂` satisfies every hypothesis, so the two dimension counts are instantiated, not empty conditionals. |

Why this earns its place: it converts "the object is rule-blind by construction" (a definitional
remark) into a **quantitative under-determination theorem with a number in it** — `13/14`
per point — which is what makes the kill checkable rather than rhetorical. The build result and
the `#print axioms` output are recorded in §10.

**What it does NOT prove:** nothing about the flow's existence, about orbits, about the
endpoint `⟨b₀²⟩`, or about the condensed category. The step from "13 tangential directions are
`V`-blind" to "the landing point in `M` differs" is an *argument* (§4.2), not a Lean theorem;
making it one would require integral curves, whose existence `RuleFlow` explicitly does not
prove (`FLAG-rule-flow-open`).

---

## 9. ESCALATE

1. **Ledger accuracy (mechanical, low risk):** `REF-condensed-categorical-foundations-mathlib`
   overstates Mathlib's condensed tractability (§2.2/§7.3). A correction is a ledger write and
   is not mine to make.
2. **Theory judgement (Furey/Feynman):** §5.1 shows the QBP phrase "the 𝕆→ℍ crystallisation"
   is not a map in any algebra category — `𝕆` admits no algebra map onto `ℍ`. The repo's own
   objects already encode the correct notion (subalgebra *selection*, `G₂/SO(4)` / the hosting
   bundle). **Is the prose elsewhere in QBP relying on a projection reading?** If any derivation
   uses "project 𝕆 onto ℍ" as a morphism, it is using a map that does not exist. This deserves
   a sweep, and it is a theory call, not a Lean call.
3. **Scope judgement (Oppenheimer):** §4.4 identifies the one place pointless/condensed methods
   genuinely belong — the non-Hausdorff orbit space of the rule. That is a *different* research
   question from the one `CONJ-condensed-math-for-transition-state` states, and it is downstream
   of the rule rather than upstream. Whether to re-scope the conjecture to it (rather than kill
   it outright) is a strategic decision.
4. **Not adjudicated:** sub-conjecture (d) (higher-order harmonics as stalks on a site of
   scales) was outside this attack's assigned scope and is untouched.

---

## 10. Build and audit record

**Toolchain.** `leanprover/lean4:v4.30.0`; Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
(the repo pin). Worktree `.claude/worktrees/probe-kill-5`; Mathlib packages symlinked from the
main tree; all Lean invocations through `run-bounded 6G <sec> taskset -c 3-5`, serialised behind
an `until ! pgrep -x lake` idle check.

**Build.**

```
$ run-bounded 6G 1800 taskset -c 3-5 lake build QBP.Foundations.TransitionState
ℹ [2952/2952] Built QBP.Foundations.TransitionState (6.8s)
Build completed successfully (2952 jobs).
EXIT=0
```

Zero errors, zero warnings (the file is lint-clean: no unused simp arguments, no dead tactics).
Peak observed RSS during the cold dependency build: **3.7 GB** in a single `lean` process, well
inside the 6 GB cgroup cap; no exit 137, no exit 124.

**`#print axioms` — all 15 declarations, verbatim from the build log:**

```
'QBP.Foundations.TransitionState.bilFun'                              [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.mem_tangent_iff'                     [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.mem_vNeutral_iff'                    [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.vNeutral_le_tangent'                 [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.vNeutral_eq_tangent_of_gradient_zero'[propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.bil_one_one'                         [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.tangentProbe_surjective'             [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.vProbe_surjective'                   [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.finrank_tangent'                     [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.finrank_vNeutral'                    [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.exists_vNeutral_ne_zero'             [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.hypotheses_satisfiable'              [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.finrank_counts_instantiated'         [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.add_vNeutral_preserves_data'         [propext, Classical.choice, Quot.sound]
'QBP.Foundations.TransitionState.add_vNeutral_ne'                     [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no native-reduction axiom, no user axiom, in any declaration.

**Gates.**

```
$ python3 scripts/check_lean_foundations.py --dir proofs/QBP/Foundations
ok: sorry at baseline (0)
ok: vacuous-`: True :=` theorem at baseline (0)
Lean foundations gate PASSED.                                    (exit 0)

$ python3 scripts/check_layer_imports.py
layer imports clean                                              (exit 0)
```

**Anti-vacuity guard.** `hypotheses_satisfiable` and `finrank_counts_instantiated` exhibit a
concrete `s = e₁`, `g = e₂` satisfying every hypothesis, so `finrank_tangent = 14` and
`finrank_vNeutral = 13` are instantiated statements, not conditionals with an empty antecedent.
(This is the #472-class check applied to this file: the *statement*, not only the proof, was
inspected for content.)
