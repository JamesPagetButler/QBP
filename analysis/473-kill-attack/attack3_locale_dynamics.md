# ATTACK 3 — can a locale supply the dynamical rule? (#473 Prop 12 loophole / Prop 13(b))

**Status:** research note, Tier 2. Nothing ruled, nothing anchored, no CTH entry.
**Lean:** `proofs/QBP/Foundations/LocaleDynamics.lean` (41 theorems, 0 `sorry`, 0 `native_decide`,
axiom closure `{propext, Classical.choice, Quot.sound}` for all 41 — attestation
`proofs/QBP/Foundations/LocaleDynamics.axioms.txt`).
**Target:** Prop 12 of `docs/foundations/473-ac1-first-link-2026-09-04.md` and its explicit
unworked loophole — *"(Not 'a locale cannot supply dynamics by kind': domain theory IS
locales-as-computation; the objection is the rule-dependence, which is testable.)"* — plus the
reversal clause Prop 13(b).

---

## 0. Verdict (read this first)

| Question | Answer | Evidence |
|---|---|---|
| Is the driver's sealed position true **as stated** ("every `V`-natural frame endomorphism factors through `V*`")? | **NO — false.** | `crack_vacNucleus_not_defOpens` (and trivially the identity endomorphism) |
| Is it true on the **`V`-definable subframe**? | **YES, and now a theorem.** | `natural_factors_through_comap` (compact `X` + fibrewise transitivity) |
| Does a `V`-natural locale-native mechanism supply the **vacuum sublocale** (the support)? | **YES — this is the real crack, and it was not on record.** | `vacNucleus_natural`, `vacNucleus_trace_surjective`/`_injective` |
| Does it supply a **measure** on the vacuum? | **NO.** | `eq_zero_of_compressed`, `natural_valuation_vanishes_of_const` |
| Does the domain-theoretic ("descend one notch") reading select anything inside the vacuum? | **NO — its least fixed point is `⊥`.** | `iInf_sublevel_eq_interior`, `iInf_sublevel_eq_bot_of_interior_eq_empty` |
| Does anything here **select quench vs anneal**? | **NO.** | §4 — the sublevel filtration is a function of `V` alone, hence *identical* for both rules |
| **Is Prop 13(b) reversed?** | **NO.** The kill stands, now for a reason that is theorem-shaped rather than rhetorical. | §6 |

**Net change to the record:** Prop 12 survives, but one of its sentences was *wrong*. "A locale
supplies neither (i) nor (ii)" is right about (i) and (ii); "a `V`-natural mechanism moves nothing
inside a level set" is **false**. Locale theory does hand you the vacuum *with its full internal
topology*, `V`-naturally, for free. It just hands you no measure on it, and no way to pick a rule.
That is a strictly sharper kill than the one on record, because it now names exactly what is
missing: not "structure", but **a reference measure and a transport rule — both of which are
metric data.**

---

## 1. The setting, made precise

Fix a topological space `X` and a **continuous potential** `V : C(X, ℝ)`. Everything below is
generic in `(X, V)`; the QBP instance is `X = StateSphere = S¹⁴ ⊂ Im 𝕊`
(`proofs/QBP/Substrate/Hosting.lean`) and `V = potential = ‖[a, b]‖²` (ibid., `potential`), with
the rule field of `proofs/QBP/Substrate/RuleFlow.lean`. The Lean file lives in
`QBP/Foundations/` and therefore **cannot** import either — which is the point: the argument uses
nothing about 𝕊.

| Object | Definition | Lean |
|---|---|---|
| `Ω(X)` | the frame of opens | `TopologicalSpace.Opens X` (Mathlib) |
| `V* : Ω(ℝ) → Ω(X)` | `W ↦ V⁻¹(W)`, a frame homomorphism | `Opens.comap V` (Mathlib) |
| **`V`-definable opens** | `defOpens V := range(V*)` | `defOpens` |
| **`V`-saturated** | `U` is a union of level sets of `V` | `Saturated` |
| **`V`-preserving homeo** | `h : X ≃ₜ X` with `V ∘ h = V` | `Preserves` |
| `h*` | the induced frame automorphism `Opens.comap h` | `act` |
| **`V`-natural endomap** | `f : Ω(X) → Ω(X)` with `f ∘ h* = h* ∘ f` for every `V`-preserving `h` | `Natural` |
| **`V`-natural valuation** | `ν` with `ν ∘ h* = ν` for every `V`-preserving `h` | `NaturalValuation` |
| **valuation** (Vickers) | `ν ≥ 0`, `ν ⊥ = 0`, monotone, modular | `LocaleValuation` |

`Natural` is the concrete equivariance form of "definable from `V` alone": a construction that can
only quote `V` cannot distinguish two configurations that a `V`-preserving homeomorphism carries
into each other. Note this is *weaker* than functorial-in-`(X,V)` naturality, so a mechanism that
fails `Natural` certainly fails the stronger condition, and — more importantly here — a mechanism
that *satisfies* `Natural` is a live candidate for the stronger one.

---

## 2. Where the sealed position IS true (§1–§2 of the Lean file)

* `defOpens V` is a **subframe** of `Ω(X)`: closed under `⊥`, `⊤`, binary `⊓`/`⊔` and **arbitrary**
  `sSup` (`bot_/top_/inf_/sup_/sSup_mem_defOpens`). Being the image of the frame homomorphism `V*`,
  it is a frame **quotient of `Ω(ℝ)`** — the AC1 target-(1) statement, delivered.
* `saturated_of_mem_defOpens`: **every `V`-definable open is `V`-saturated.** This is the exact
  sense of "moves nothing inside a level set", and it is trivially true for anything factoring
  through `V*`.
* `mem_defOpens_of_saturated_of_compactSpace`: on a **compact** `X` the converse holds with *no*
  extra hypothesis (proof: `Uᶜ` compact ⇒ `V(Uᶜ)` closed in `ℝ`, and saturation gives
  `U = V⁻¹(V(Uᶜ)ᶜ)`). Hence `mem_defOpens_iff_saturated`: **for compact `X`, `V`-definable ⇔
  `V`-saturated.** `S¹⁴` is compact, so this is the QBP case exactly.
  *(An earlier draft used the hypothesis `IsOpen (V '' U)`; that is **not** satisfiable in the case
  of interest — `V(\{V < ½\}) = [0, ½)` is open in the range, not in `ℝ`. The compactness proof
  replaces it. The weak lemma is kept with an honesty note attached.)*
* `natural_maps_defOpens` / `natural_factors_through_comap`: for compact `X`, **if** the
  `V`-preserving homeomorphisms act transitively on each level set (`FibrewiseTransitive`), then
  every `V`-natural endomap carries `defOpens` into `defOpens`, and there is
  `φ : Ω(ℝ) → Ω(ℝ)` with `f(V* W) = V*(φ W)` for all `W`.

**That is the driver's sealed position, now a theorem — restricted to `defOpens`.**

**Weak joint, flagged.** `FibrewiseTransitive V` is an *assumption*, not a theorem, and it is
where this could break for `S¹⁴`: a level set of the quartic `V` need not be a single homogeneous
piece (the argmax locus `{V = 1}` contains the 42 rank-2 zero divisors and the strata `|a| = 0`,
`|Im b| = 0`, `±ℓ` are singular — see `RuleFlow` items 8/13). If transitivity fails on some level
set, a `V`-natural map can already tell its pieces apart, and §2's factorisation fails there too.
**That direction only widens the crack of §3; it never helps the sealed position.**

---

## 3. The crack: the vacuum sublocale is `V`-native and DOES see inside a level set

The vacuum `{V = 0}` is closed; its complement `V⁻¹(ℝ ∖ {0})` is open and is `V`-definable
(`nonVac_mem_defOpens`). The **closed sublocale of the vacuum** is therefore given by the nucleus

```
j(U)  =  U ⊔ V⁻¹(ℝ ∖ {0})          (Lean: vacNucleus, a Mathlib `Nucleus (Opens X)`)
```

Facts proved:

| Fact | Lean |
|---|---|
| `j` is a nucleus (inflationary, idempotent, `⊓`-preserving) | `vacNucleus` (by construction, kernel-checked) |
| `j` is **`V`-natural** | `vacNucleus_natural` |
| fixed opens of `j` = opens above `V⁻¹(ℝ∖{0})` | `vacNucleus_fixed_iff` |
| every open of the vacuum **subspace** is the trace of a fixed open | `vacNucleus_trace_surjective` |
| a fixed open is determined by its trace on the vacuum | `vacNucleus_trace_injective` |

The last two together: **the fixed frame of `j` is in bijection with `Ω({V = 0})` — the nucleus
recovers the vacuum with its full internal topology.** That frame is emphatically *not* inside
`defOpens V`.

**Witness (`crackV`, `crackU`).** `X = ℝ`, `V(x) = max(x − 1, 0)` (continuous, `≥ 0`, vacuum
`= (−∞, 1]`). Then `crackV 0 = crackV ½ = 0` — same level set — and
`crackU = (−∞, ¼) ⊔ V⁻¹(ℝ∖{0})` is `j`-fixed, contains `0`, and does **not** contain `½`
(`crack_vacNucleus_separates_inside_level_set`). Consequently
`j(⟨(−∞, ¼)⟩) ∉ defOpens V` (`crack_vacNucleus_not_defOpens`): `j` is **not** a function of `V`'s
values.

So the sealed position, *as stated*, is false. (It is false even more cheaply: the identity
endomap is `V`-natural and does not factor through `V*` unless `V*` is onto. The vacuum nucleus is
the non-trivial refutation, because its fixed sublocale is exactly the object the sealed position
was about.)

**But notice what the crack does and does not deliver.** `j` is a *projection*: idempotent, no time
parameter, no ordering of states, the same object for every rule that has the same vacuum. It
supplies the **support** of the would-be endpoint distribution. It supplies no distribution on that
support, and no reason to prefer one endpoint distribution over another. Quench (`⟨b₀²⟩ = 0.146`)
and anneal (`≈ 1/3`) have the *same* vacuum and therefore the *same* `j`.

---

## 4. The domain-theory reading: "descend one notch" fixes nothing

Domain theory is indeed locales-as-computation, and the loophole deserves its best shot. The
canonical frame-native descent attached to `(X, V)` is the **sublevel filtration**

```
U_c = {V < c} = V*(Iio c),   c > 0,     (Lean: sublevel)
```

a monotone (`sublevel_mono`), `V`-definable (`sublevel_mem_defOpens`) family, downward directed,
and the only Scott-style "descend one notch" operator definable from `V` alone. Its least fixed
point is its infimum in the frame, and:

* **`iInf_sublevel_eq_interior`** — for `V ≥ 0`, `⨅_{c>0} U_c = interior({V = 0})` *exactly*.
* **`iInf_sublevel_eq_bot_of_interior_eq_empty`** — if the vacuum has empty interior, the least
  fixed point is `⊥`, the empty open.

For QBP the vacuum is a positive-codimension subset of `S¹⁴` (the vacuum orbit space is a 2-sphere;
`V` is a non-zero quartic polynomial, hence real-analytic and not identically zero — `RuleFlow`
`potential_witness` / `exists_ruleField_ne_zero` — so its zero set is nowhere dense on the
connected analytic manifold `S¹⁴`). Hence the interior is empty and the descent's least fixed point
is `⊥`.

> **Not mechanised, flagged:** "non-zero real-analytic ⇒ nowhere-dense zero set on a connected
> analytic manifold" is a standard fact but is *not* proved in this file; the Lean theorem carries
> `interior (vacuum V) = ∅` as a hypothesis. Mechanising the instantiation for `S¹⁴` is a clean
> follow-up (it would also be reusable for the argmax-locus results in `RuleFlow`).

**Why this is fatal to the loophole, in one line.** The sublevel filtration is a function of `V`
alone. *Every* rule that descends `V` — quench, anneal, any third rule — induces the **same**
filtration. So the filtration cannot distinguish them, whatever its fixed point is; and its fixed
point is in any case the empty open, so it distinguishes nothing at all. Domain theory gives a
least fixed point *of opens*, not a limit *of points*, and the open that is the limit is `∅`.

This is the honest answer to Prop 12's parenthesis: domain theory is not excluded "by kind", it is
excluded **by computation** — the computation runs and returns `⊥`.

---

## 5. Valuations (Vickers): `V`-naturality kills the measure

Valuations are the point-free replacement for measures (Vickers, *Topology via Logic* ch. 4 / *A
localic theory of lower and upper integrals*; Heckmann; the valuation–measure extension theorem for
locally compact locales). A valuation is `ν : Ω(X) → [0,∞]`, `ν(⊥) = 0`, monotone, **modular**
(`ν(U ∨ W) + ν(U ∧ W) = ν U + ν W`), usually Scott-continuous. The Lean `LocaleValuation` drops
Scott continuity and takes real (finite) values — **strictly weaker hypotheses, so the vanishing
results below are strictly stronger.**

Proved:

| Result | Statement | Lean |
|---|---|---|
| additivity | disjoint opens add | `map_sup_of_disjoint` |
| finite additivity | pairwise-disjoint finite families add | `sum_eq_sup` |
| **compression bound** | `n` disjoint opens of equal valuation ⇒ `n·ν(U) ≤ ν(⊤)` | `card_mul_le_top` |
| **compression vanishing** | an infinite disjoint family of equal-valuation copies ⇒ `ν(U) = 0` | `eq_zero_of_compressed` |
| pushforward | the `V`-shadow `W ↦ ν(V* W)` is a valuation on `Ω(ℝ)` | `pushforward` |
| **instantiation** | on `ℝ` with a constant potential, **every** `V`-natural valuation vanishes on every bounded interval | `natural_valuation_vanishes_of_const` |

The instantiation is the maximally degenerate case — one single level set — and it is chosen
because the compressing homeomorphisms (translations) can be *constructed* in Lean. The general
statement it stands for is the classical one: **`Homeo(M)` preserves no non-zero finite Borel
measure on a manifold `M` of positive dimension** (compress any open ball into `n` disjoint copies
of itself inside a chart). Level sets of the QBP potential are such manifolds. So:

> A `V`-natural valuation is (a) on `defOpens`, nothing but a measure on the value line `ℝ`
> (`pushforward`), and (b) on each level set, **zero** — because the `V`-preserving homeomorphism
> group of a level set is far too big to preserve a measure.

There is therefore no `V`-natural valuation concentrating on the vacuum at all, let alone one
reproducing quench's basin measure or anneal's Laplace measure. The crack of §3 hands you the
support and *nothing* can put mass on it naturally.

**Where the surface measure actually comes from.** The `N`-surface measure QBP uses is invariant
under the **isometry group of `N` preserving `V`** — a *compact* group — not under `Homeo_V(X)`.
Compactness is exactly what makes an invariant probability measure exist (Haar) and be essentially
unique. Shrinking the naturality group from `Homeo_V(X)` to `Isom_N(X) ∩ Homeo_V(X)` is the entire
content of "the measure needs the metric", and `N` is not frame data: two homeomorphic level sets
with different `N`-geometry carry different surface measures and the frame cannot tell them apart.

---

## 6. Verdict on Prop 13(b), and what class would be needed

**Prop 13(b) is NOT reversed by any mechanism in this class.** A mechanism that "supplies the
dynamical rule itself from topological/measure data" would have to supply, at minimum:

1. a **reference measure on each level set** (to say what "uniform" means), and
2. a **transport rule between level sets** (gradient descent in *some* metric, or a Gibbs weight
   `e^{−βV}` with a reference measure to weight).

§5 kills (1) for every `V`-natural valuation; §4 kills (2) for the only canonical frame-native
descent. §3's crack supplies the *support* and nothing else. No combination of nuclei and
valuations on `Ω(X)` gets past this, because a frame is a lattice of opens: it has no notion of
"how far", and both quench and anneal are specified by a quantity ("distance moved per unit time",
"energy per unit temperature") that has no lattice expression.

**What class *would* be needed** (i.e. what Prop 13(b) is really asking for):

| Candidate structure | Supplies (1)? | Supplies (2)? | Is it "beyond the frame"? |
|---|---|---|---|
| frame `Ω(X)` + nuclei | no (§5) | no (§4) | — |
| frame + a chosen valuation (a "measure locale", Vickers/Heckmann) | **by fiat** | no | yes — the valuation is extra data, and §5 says it is not `V`-natural |
| **metric locale** (Lawvere: `[0,∞]`-enriched category; quantale-enriched / approach-locale) | yes, via the metric's volume | yes, via metric gradient flow | **yes — a metric is exactly the data a frame omits** |
| Riemannian manifold `(S¹⁴, N)` + `V` | yes | yes (quench = `−∇_N V`) | this is what QBP already has |

So Prop 13(b) needs a **metric-carrying locale**, which is to say: it needs `N`. And `N` is
algebra-supplied (Prop 7′) but *not* locale-supplied. The route does not become non-circular by
adding categorical wrappers; it becomes non-circular only if something other than the algebra
supplies the metric, and nothing in this class does.

**Recommendation:** Prop 12 stands with one sentence corrected (§0). Prop 13(b) stands
unreversed. The Prop 12 parenthesis about domain theory should be replaced by §4's result — it is
better for the kill than the parenthesis was, because it is a computation with an answer rather
than a disclaimer. `Do not re-fund: categorical wrappers` (v0.4 §5) is unchanged; add
"metric locales / enriched locales" to the *funded-only-if* line rather than the
do-not-fund line, since that is the one categorical structure that would actually carry the missing
datum — but note it carries it by *containing a metric*, so it relocates rather than reduces (the
Prop 8 MDL rule applies to it too).

---

## 7. Residual / follow-ups

| # | Item | Why it matters |
|---|---|---|
| R1 | Mechanise `interior (vacuum V) = ∅` for `S¹⁴` (non-zero real-analytic ⇒ nowhere-dense zero set) | discharges the one hypothesis §4 carries; reusable in `RuleFlow` |
| R2 | Decide `FibrewiseTransitive` for the QBP `V` on each level set (probably FALSE on the singular strata) | if false, §2's factorisation is weaker than stated and the crack is wider — either way the verdict is unchanged, but the record should be right |
| R3 | Mechanise the manifold compression lemma (`Homeo(M)` preserves no finite measure, `dim M ≥ 1`) | upgrades §5's `ℝ` instantiation to the actual level sets |
| R4 | State the "rule = protocol" claim (v0.4 §7 rank 2) against §4: the filtration is rule-independent | turns "nothing selects the rule" into "the only frame-native selector is provably constant across rules" |

**Nothing in this note is anchored.** No CTH entry, no ledger edit, no ruling.
