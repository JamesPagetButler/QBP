# #473 kill-attack 2 — a third algebra-native generator: the canonical zero divisors

**Target.** Prop 16 (`docs/foundations/473-ac1-first-link-2026-09-04.md`; Lean half in
`proofs/QBP/Foundations/NoAutonomousDynamics.lean`, see its "Scope caveat"): *the algebra generates only
symmetries, never dynamics toward the vacuum.* Its examined scope is one imaginary unit `s`, the forced pair
`(s, ℓ)` (quaternion subalgebra `ℍ_s`, shape invariant `σ = V/(1−b₀²)²` constant, only `±ℓ` reachable), and one
unforced generic `t` (linear maps → power iteration onto the ridge `V = 1`). **Unexamined:** a third generator
that is canonical *as a set* — the 84 basis-sum zero divisors `e_i ± e_j` (42 planes, PROOF-42zd), which are
Aut-invariant as a set unlike a generic `t`. Kill condition as originally posed (doc §7 rank 2, #473 plan row 2): *an
(s, ℓ, z)-word that reaches a vacuum other than `±ℓ` from a non-vacuum `s`.* **Re-posed after review** (Red Team #676
F1; #473 comment 5822879405): as literally posed the condition **fires** — reachability of a non-pole vacuum by a fixed
word is a measure-zero event that holds by construction (§7.0), so it is not the statement Prop 16 makes. The kill for
this attack is *a word-map with a positive-measure set of `s` landing on a non-pole vacuum, or an iterated word-map with
a non-pole vacuum attractor.* The driver's sealed position (S2/S3 below) was mis-posed as a reachability claim and is
correct only under this dynamical reading.

**Status.** Research probe, numerical flashlight only (branch `research/473-kill-attack-2`; nothing here touches
the ledger or `proofs/`). Beekeeper-directed attempt to prove `KILLED-locale-forcing-route` wrong
(plan: #473, comment 5808096164), ATTACK 2 of the plan. **Revision:** Red Team #676 (comment 5822866563, REQUEST
CHANGES) F1–F5 applied — the reachability claim is withdrawn (§7.0), σ is the hit variable (§1), counts corrected (§5,
§7), "not covered" extended (§7). No number from the runs was changed; the raw outputs are untouched.

## 0. Sealed expectations (written before each run; the driver's position)

| # | Run | Sealed expectation |
|---|---|---|
| S0 | `zd_enum_check.py` | exactly 84 basis-sum ZDs in 42 planes; all have `V(z/√2) = 1`; every plane straddles `𝕆` and `𝕆ℓ`; the Jordan map `xz + zx` is **real** on `Im𝕊` (all imaginary basis elements anticommute) |
| S1 | `zd_subspaces.py` | the top-σ space of `L_z`, `R_z`, `ad_z` lies on the ridge `V = 1` (as for a generic `t`); open whether the kernel does |
| S2 | `attack2_words.py basis` | **no** word of length ≤ 5 reaches a non-pole vacuum from any non-vacuum `s`; the only `V = 0` landings are the poles `±ℓ`; `V(w)` otherwise spreads over `(0, 1]` with a mass at the ridge |
| S3 | `attack2_words.py ridge` | same as S2 for `z` a random ridge point (the basis-sum ZDs are not special) |
| S4 | `attack2_maps.py` | `x·z`, `z·x`, `[x,z]` → ridge (period 2 up to sign); `x + z` → `z` (ridge); `xz + zx` degenerate (real); no non-pole vacuum |
| S6 | `attack2_wordmaps.py` (added after S2/S3 showed the near-miss words) | iterating every word of length ≤ 4 as a self-map `x ↦ Im w(x,ℓ,z)/‖·‖`: **no** non-pole vacuum is an attractor; endpoints are ridge points, poles, or cycles/fixed points with `V` bounded away from 0 |
| S7 | `attack2_nearmiss.py` | the small-`V` endpoints of S6 are pole approaches (`|b₀| → 1` with σ bounded away from 0) or σ-conserving quasi-periodic motion — not σ → 0 |
| S5 | `attack2_equiv.py` | every statistic is exactly Aut-invariant: `G₂` acts diagonally and fixes `ℓ`, so `w(φs, ℓ, φz) = φ w(s, ℓ, z)`; the `S₃` factor preserves `V` (det M = ±1) and maps `b₀ ↦ ±b₀` |

*Post-review annotation (the sealed text above is left as written).* S2/S3 are **reachability** claims and are FALSE as
stated: fixed words do reach non-pole vacua, on a measure-zero (codim ≥ 4) set of `s` that 200 sampled `s` cannot hit
(§7.0). What the runs S2/S3 actually test — and what held — is the absence of positive-measure steering; S1/S4/S6/S7
(attractors) are the dynamical statements and held as sealed. S0/S5 are exact and held.

## 1. Setup

State sphere: imaginary unit sedenions `x ∈ ℝ¹⁶`, `x₀ = 0`, `‖x‖ = 1`; `cdLo = x[0:8]`, `cdHi = x[8:16]`;
`ℓ = e₈`; `b₀ = x[8]`; `V(x) = ‖cdLo·cdHi − cdHi·cdLo‖²` (on the sphere `V = 4(N(Im a)N(Im b) − ⟨Im a, Im b⟩²)`);
vacua `V = 0` (8-dim); ridge `V = 1` (unit ZDs; `V ≤ (1 − b₀²)²` so `V = 1 ⇒ b₀ = 0`). Product from
`flowlib.py` (`analysis/rule-flow-tests-2026-09-20`, CD convention `(a,b)(c,d) = (ac − conj(d) b, da + b conj(c))`).
A word's value need not be imaginary; it is read on the state sphere as `Im w / ‖Im w‖` (`Im` is in the
`(+, conj, scalar)` closure); `V` ignores real parts anyway. A word is *degenerate* on a pair when `‖Im w‖ < 10⁻⁷`
(leaves are unit vectors, so this is round-off scale — e.g. `s + s³/‖s³‖ ≡ 0`). **Hit (as computed):** `V < 10⁻⁸`,
`|b₀| < 0.999`, non-degenerate. **Hit variable (as read):** the shape invariant `σ = V/(1−b₀²)² ∈ [0, 1]`, which vanishes
exactly on the non-pole vacua and is the quantity Prop 16(ii) conserves. The computed criterion is `σ < 10⁻⁸/(1−b₀²)²`:
`σ < 10⁻⁸` at `b₀ = 0` but `σ < 2.5 × 10⁻³` at the `|b₀| = 0.999` cut — so a "hit" and a σ-floor are not comparable
without this conversion, and every σ_min quoted below is the smallest σ *reached on the sampled `s`* (a sampling floor),
not a property of the word. The `|b₀| ≥ 0.999` slab is classed as a pole landing **by definition**: a genuine non-pole
vacuum with `b₀` that close to `±1` would not be counted as a hit (measure-tiny, but a definition, not a result).

Conjugation is redundant: for imaginary generators `conj(w) = ±(w reversed)`, and every reversal is enumerated.
Real scalars are absorbed by normalisation.

## 2. The canonical zero divisors (`zd_enum_check.py`, S0 — met)

| Check | Result |
|---|---|
| basis-sum elements `e_i ± e_j` with singular `L_z` | **84**, in **42 planes**, both signs in every plane |
| planes straddling `𝕆` / `𝕆ℓ` | 42 / 42; **none involves `e₈ = ℓ`** |
| `V(z/√2)` | `1.000000000000` for all 84 (the ridge) |
| `L_z` singular values (unnormalised `z`, `Σσ² = 16·N(z) = 32`) | `{2 ×4, √2 ×8, 0 ×4}` — **one spectrum for all 84** (`R_z` identical). `ad_z = L_z − R_z` **as the full 16×16 matrix on `𝕊`** (real line and `z`-line included, both in the kernel; float SVD): `{4 ×4, 2√2 ×6, 0 ×6}`, `Σσ² = 112`; the `σ = 4` block is supported on `span{e₄…e₇, e₁₂…e₁₅}` (it is the 4-dim `T(ad_z)` of §3), the `{2√2 ×6, 0 ×6}` part on the complementary 8-dim block containing `1`, `z`, `ℓ` — the Red Team's exact ℚ check on the 12-dim `ad_z`-closed block reproduces `{2√2 ×6, 0 ×6}` |
| Jordan map `xz + zx` on `Im𝕊` | **real**: `= −2(x_i ± x_j)`, max imaginary part `0.0` (exact, from pairwise anticommutation) |
| random ridge points (`a ⊥ Im b`, `|a| = |Im b|`, `b₀ = 0`) | `rank L_x = 12` for 20/20 → ridge points are zero divisors, kernel dim 4 |
| `G₂ ⊂ Aut(𝕊)` construction | `Der(𝕆)` from basis pairs has rank 14; `exp(D) ⊕ exp(D)` is orthogonal, fixes `ℓ`, automorphism residual `9e-15` on all 256 basis pairs |

## 3. Where the linear maps send things (`zd_subspaces.py`, S1 — met, and sharpened)

`𝕊 = T ⊕ M ⊕ K` for `L_z` (`σ = 2, √2, 0`; dims 4/8/4). Random unit vectors of each summand, read on the state sphere:

| map | space | dim | `V` range | `max|b₀|` | contains `ℓ`-component |
|---|---|---|---|---|---|
| `L_z`, `R_z` (all 9 `z` tested) | `T` (top) | 4 | **`[1.0000, 1.0000]`** | 0.000 | no |
| | `M` (middle) | 8 | `[0.0000, 0.998]`, mean 0.38 | up to 0.99 | yes |
| | `K` (kernel) | 4 | **`[1.0000, 1.0000]`** | 0.000 | no |
| `ad_z` | `T` | 4 | **`[1.0000, 1.0000]`** | 0.000 | no |
| | `M` | 6 | `[0.0000, 0.999]`, mean 0.40 | up to 0.99 | yes |
| | `K` (incl. `ℝ·1`) | 6 | **`[1.0000, 1.0000]`** | 0.000 | no |

So the top-σ space — the attractor of every normalised power iteration — lies **identically** on the ridge, as does the
kernel. Both are spanned by basis-sum ZDs: `T(L_{e₁+e₁₀}) = span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂}`,
`K(L_{e₁+e₁₀}) = span{e₄−e₁₅, e₅+e₁₄, e₆−e₁₃, e₇+e₁₂}`, and `T(L_{e₁+e₁₀}) = K(L_{e₁−e₁₀})` exactly (the two signs of
a plane swap top and kernel). The middle space `M` does touch near-vacua (`V_min ≈ 10⁻⁴` on 4000 samples), but no
normalised iteration converges into `M` — it is the transient. This is the *mechanism* behind S4: the ZD is not
special as an attractor; it is special in that its top space is a 4-dim **ridge plane spanned by other canonical ZDs**
(a closed sub-structure of the 42-plane system), where a generic `t` has a top plane on the ridge with no such
basis description (`NoAutonomousDynamics.lean`, "Completeness").

## 4. Word enumeration (`attack2_words.py`, S2/S3 — met)

200 stratified non-vacuum `s` (`V(s)` evenly spaced in `[0.005, 0.995]`, `|b₀| ≤ 0.735`), `ℓ = e₈`, and `z` from (a) the 84 basis-sum ZDs (16 800 pairs) or (b) 50 random ridge points (10 000 pairs). Three word classes per pair: **pure** = all 3873 bracketed products of length ≤ 5 over `{s, ℓ, z}`; **imnode** = all 3474 words of length ≤ 4 with an optional `Im`-projection at every internal node (the `(+, conj, scalar)` closure the Lean `GenBy` uses); **combo** = all 12 870 fixed-coefficient two-word combinations `ŵ₁ + c·ŵ₂` (`ŵ` unit-normalised, words of length ≤ 3, `c ∈ {±1, ±2, ±½}`). Every value is read on the state sphere; `σ = V/(1−b₀²)² ∈ [0, 1]` is the shape invariant (`σ = 0` ⇔ vacuum, `σ = 1` ⇔ ridge shape).

### 4a. (a) 84 basis-sum z — 200 s × 84 z, 1663 s

| class | evaluations (non-degenerate) | exact pole landings `V<1e-8, |b₀|≥0.999` | non-pole `V<1e-3` | non-pole `σ<0.05` | non-pole `σ>0.95` | `σ_min` reached, non-pole (sampling floor) | **hits** (`V<1e-8, |b₀|<0.999`) |
|---|---|---|---|---|---|---|---|
| pure | 63,722,400 | 8,037,490 (12.6%) | 678,396 (1.06%) | 383,050 (0.69%) | 31,734,122 (57.1%) | 2.70e-03 | **0** |
| imnode | 40,723,200 | 542,304 (1.3%) | 78,288 (0.19%) | 305,060 (0.76%) | 22,908,444 (57.0%) | 2.70e-03 | **0** |
| combo | 212,688,000 | 11,110,416 (5.2%) | 1,335,262 (0.63%) | 1,198,878 (0.60%) | 88,388,785 (43.9%) | 7.24e-04 | **0** |

Linear closure: rank of the 3873+1 word vectors = **16** on all 20 sampled `(s, z)` pairs — three generators generate the whole algebra (the `(s, ℓ)` pair generates 4). Pure words by length (per-word statistics over all pairs):

| length | trees | fully degenerate (real ∀ pairs) | image entirely on the ridge | `σ_min` over the class | median per-word `σ_min` |
|---|---|---|---|---|---|
| 1 | 3 | 0 | 1 | 5.33e-03 | 0.503 |
| 2 | 9 | 3 | 2 | 5.33e-03 | 0.073 |
| 3 | 54 | 0 | 10 | 5.33e-03 | 0.073 |
| 4 | 405 | 77 | 60 | 2.70e-03 | 0.073 |
| 5 | 3402 | 0 | 374 | 2.70e-03 | 0.073 |

Smallest per-word `σ_min` reached on the 200 sampled `s` (a sampling floor — the preimage of the vacuum under these words is non-empty, §7.0):

| word | `σ_min` | `V_min` | `max|b₀|` | fraction on ridge |
|---|---|---|---|---|
| `(s(z(zs)))` | 2.70e-03 | 2.70e-03 | 0.000 | 0.005 |
| `(s((sz)z))` | 2.70e-03 | 2.70e-03 | 0.000 | 0.005 |
| `((z(zs))s)` | 2.70e-03 | 2.70e-03 | 0.000 | 0.005 |
| `(((sz)z)s)` | 2.70e-03 | 2.70e-03 | 0.000 | 0.005 |

Control: the 371 `(s, ℓ)`-only words have `σ_min = 0.0053` = min over the 200 `s` of `σ(s)` — the shape invariant is conserved on them to round-off, exactly as Prop 16(ii) states; words containing `z` are the only ones that move σ; on the sampled `s` they did not move it below the floors in the table — which is a sampling floor, not a bound (σ = 0 *is* attained on a codim-≥ 4 set of `s`, §7.0).

### 4b. (b) 50 ridge-point z — 200 s × 50 z, 1067 s

| class | evaluations (non-degenerate) | exact pole landings `V<1e-8, |b₀|≥0.999` | non-pole `V<1e-3` | non-pole `σ<0.05` | non-pole `σ>0.95` | `σ_min` reached, non-pole (sampling floor) | **hits** (`V<1e-8, |b₀|<0.999`) |
|---|---|---|---|---|---|---|---|
| pure | 37,930,000 | 4,783,882 (12.6%) | 402,880 (1.06%) | 227,686 (0.69%) | 18,936,130 (57.2%) | 1.47e-03 | **0** |
| imnode | 24,240,000 | 322,800 (1.3%) | 46,600 (0.19%) | 181,632 (0.76%) | 13,660,488 (57.1%) | 4.88e-03 | **0** |
| combo | 126,600,000 | 6,613,220 (5.2%) | 795,790 (0.63%) | 713,053 (0.59%) | 52,809,357 (44.0%) | 1.13e-03 | **0** |

Linear closure: rank of the 3873+1 word vectors = **16** on all 20 sampled `(s, z)` pairs — three generators generate the whole algebra (the `(s, ℓ)` pair generates 4). Pure words by length (per-word statistics over all pairs):

| length | trees | fully degenerate (real ∀ pairs) | image entirely on the ridge | `σ_min` over the class | median per-word `σ_min` |
|---|---|---|---|---|---|
| 1 | 3 | 0 | 1 | 5.33e-03 | 0.503 |
| 2 | 9 | 3 | 2 | 5.33e-03 | 0.092 |
| 3 | 54 | 0 | 10 | 5.33e-03 | 0.067 |
| 4 | 405 | 77 | 60 | 4.88e-03 | 0.092 |
| 5 | 3402 | 0 | 374 | 1.47e-03 | 0.086 |

Smallest per-word `σ_min` reached on the 200 sampled `s` (a sampling floor — the preimage of the vacuum under these words is non-empty, §7.0):

| word | `σ_min` | `V_min` | `max|b₀|` | fraction on ridge |
|---|---|---|---|---|
| `(s((s(sz))z))` | 1.47e-03 | 1.39e-03 | 0.735 | 0.000 |
| `(s(((zs)s)z))` | 1.47e-03 | 1.39e-03 | 0.735 | 0.000 |
| `((z(s(sz)))s)` | 1.47e-03 | 1.39e-03 | 0.735 | 0.000 |
| `((z((zs)s))s)` | 1.47e-03 | 1.39e-03 | 0.735 | 0.000 |

Control: the 371 `(s, ℓ)`-only words have `σ_min = 0.0053` = min over the 200 `s` of `σ(s)` — the shape invariant is conserved on them to round-off, exactly as Prop 16(ii) states; words containing `z` are the only ones that move σ; on the sampled `s` they did not move it below the floors in the table — which is a sampling floor, not a bound (σ = 0 *is* attained on a codim-≥ 4 set of `s`, §7.0).


## 5. Iterated linear maps (`attack2_maps.py`, S4 — met)

200 stratified `s` (`V(s) ∈ [0.005, 0.995]`), 200 steps, each map in two variants: `raw` (normalise the full
16-vector; may leave `Im𝕊`) and `im` (state-sphere self-map `x ↦ Im f(x)/‖Im f(x)‖`). `basis` = 84 basis-sum `z`
(16 800 trajectories, 889 s); `ridge` = 50 random ridge points (10 000 trajectories, 478 s). **Identical outcomes:**

| map `f` | endpoint `V` | endpoint `b₀` | period (up to sign) | leaves `Im𝕊` (raw) | hits |
|---|---|---|---|---|---|
| `x·z`, `z·x`, `[x,z]` | **1.000 (all)** | 0.000 | 2 | `x·z`, `z·x`: yes; `[x,z]`: no | 0 |
| `(xz)ℓ`, `z(xℓ)` | **1.000 (all)** | 0.000 | 2 | yes | 0 |
| `x + z` | **1.000** (→ `z`) | 0.000 | 1 (fixed point) | no | 0 |
| `xz + zx` | raw: 1.000 (the real output is renormalised to `±1`, then `1·z`…, degenerate); **im: dead** (`Im = 0` at step 1, all 16 800) | — | — | — | 0 |
| `x + z ± ℓ` | **0.250** (→ `(z ± ℓ)/‖·‖`: `a = e_i/2`, `b₀ = ±1/√2`, `Im b = e_j/2`) | ±0.707 | 1 | no | 0 |

No trajectory ended within `10⁻³` of a vacuum other than a pole: **0 of 482 400** = 9 maps × 2 variants × 26 800 `(s, z)` pairs (16 800 basis-sum + 10 000 ridge; the `im` variant of `xz + zx` is dead at step 1, so 455 600 are alive). Endpoint `V` is *exactly* 1 or
*exactly* 1/4 to the printed precision — the maps are linear, the endpoints are the canonical subspaces of §3 or the
fixed point `norm(z ± ℓ)`, not distributions.

## 5b. Iterated NONLINEAR word-maps (`attack2_wordmaps.py`, S6 — met)

The plan's map list is linear in `x`; Prop 16 is about *dynamics*, i.e. iteration, and the near-miss words of §4 are
nonlinear in `s`. So every pure word of length ≤ 4 containing `x` (368 trees: 188 linear, 180 with ≥ 2 `x`) was iterated
100 steps as `x ↦ Im w(x, ℓ, z)/‖Im w‖` from 20 stratified `s`, for the 84 basis-sum `z` (1680 trajectories per map) and 20
ridge `z` (400 per map). Hit ⇔ endpoint `V < 10⁻⁶`, `|b₀| < 0.999`.

| | basis-sum `z` (618 240 trajectories) | ridge `z` (147 200) |
|---|---|---|
| maps whose alive endpoints are all on the ridge | 200 / 368 | 208 / 368 |
| maps ending all at a pole | 4 | 4 |
| fully dead maps (`Im → 0`, e.g. `xx`, `x(zz)`-type reals) | 58 | 58 |
| period census (alive, up to sign) | 1: 57 120 · 2: 360 160 · none ≤ 6: 103 520 | 1: 13 600 · 2: 86 776 · none ≤ 6: 23 624 |
| maps with any non-pole endpoint `V < 10⁻³` | 8 (864 trajectories, 0.14%) | 6 (208, 0.14%) |
| minimum non-pole endpoint `V` | 4.2e-06 (`z(x(ℓx))`) | 9.3e-06 (`z(x(ℓx))`) |
| **hits** | **0** | **0** |

## 5c. What the near-miss maps do (`attack2_nearmiss.py`, S7 — met)

The four map families with the smallest non-pole endpoint `V`, run to 2000 steps, tracking `V`, `|b₀|`, σ:

| map | `Im` vs `ℓ` | σ along the trajectory | what small `V` at step 100 was | at step 2000 |
|---|---|---|---|---|
| `x(ℓx)` (`(x, ℓ)`-only) | stays in `Im ℍ_x` | **conserved**, `max|Δσ| = 1.3e-12`; σ_min of the near-miss set 0.11 | a quasi-periodic pass near the pole (`|b₀|` median 0.985) | dispersed again (`|b₀|` median 0.47; distance to `±ℓ` median 1.03) — no attractor |
| `z(x(ℓx))` | — | **σ ≡ 1 to 1e-12** (every point is a ridge shape scaled toward the pole, so `V = (1 − b₀²)²`) | pole proximity by construction (`|b₀|` median 0.993) | the 89 near-miss trajectories disperse (`|b₀|` median 0.56); 2 reach the pole; none approaches a non-pole vacuum |
| `x(ℓ(xz))` | — | **σ ≡ 1 to 1e-12** | pole proximity (2 trajectories) | `V ≥ 0.26` on the former near-miss set |
| `x((xz)z)` (`(xz)z ≠ x(zz) = −2x`, non-alternativity) | lands **exactly** in `b₀ = 0` after one step (`max|b₀| = 3e-16`) | not conserved (`max|Δσ| = 0.90`) | never below `V = 3.84e-3` | the floor `3.84e-3` is unchanged at 100 / 500 / 2000 steps — a cycle, not a descent |

So every small-`V` endpoint in §5b is either the known `(s, ℓ)` behaviour seen dynamically (σ conserved — Prop 16(ii)) or
lies on the σ = 1 shape stratum, where the *only* vacua are the poles. No map lowers σ toward 0 along a trajectory.

## 6. Aut-equivariance (`attack2_equiv.py`, S5 — met, exact)

Automorphisms used, each verified on all 256 basis pairs: rotations by ±120° of the `(a, Im b)` multiplicity space
(`ℓ ↦ ℓ`), the three reflections at axis angles 0°, 60°, 120° (`ℓ ↦ −ℓ`) — the `D₃ ≅ S₃` of Brown's theorem, residuals
≤ 1.3e-15 — and two random `G₂` elements (residuals ≤ 1.1e-13). Applied simultaneously to `(s, z)` on 20 `s` × 84
basis-sum `z` and 20 `s` × 20 ridge `z`, for all words of length ≤ 3 and the four 200-step iterated maps:

| automorphism | `max|ΔV|` | `max|Δ|b₀||` | degeneracy-pattern mismatches |
|---|---|---|---|
| rot ±120° | 1.7e-15 | 2.2e-16 | 0 |
| refl 0° / 60° / 120° | ≤ 1.7e-15 | 2.2e-16 | 0 |
| `G₂` #0, #1 | ≤ 1.0e-13 | ≤ 7.3e-14 | 0 |

As predicted: `G₂` acts diagonally and fixes `ℓ`, so `w(φs, ℓ, φz) = φ w(s, ℓ, z)` exactly; the `S₃` factor preserves
`V = 4 det Gram(a, Im b)` (`det M = ±1`) and flips `b₀` at most. **Any hit would be Aut-invariant; equally, the absence
of hits is not a basis-labelling accident** (though, per §7.0, it is not discriminating either) — and the ridge-`z` runs
(§4b, §5) say the same without any basis at all.


## 7. Verdict (revised after Red Team #676; the original verdict paragraph is withdrawn — see 7.0)

### 7.0 Review record — the kill condition as posed FIRED; the sealed position was mis-posed

The verdict originally written here read: *"No `(s, ℓ, z)`-word reaches a vacuum other than `±ℓ` from a non-vacuum
`s` … the vacuum is unreachable except `±ℓ` … every fixed word / fixed-coefficient combination avoids the non-pole vacuum
set entirely … no algebra-native map has the vacuum set in its image other than at `±ℓ`."* **That is false as stated.**
The Red Team (PR #676, comment 5822866563) exhibited reaching words under this report's own hit criterion:

| word | mechanism | witness (Red Team, independent code) |
|---|---|---|
| `s·z` (pure, length 2) | `s ↦ s·z` is `R_z`, rank 12; a 12-dim subspace meets the 10-dim vacuum cone | Nelder–Mead on `s ∈ S¹⁴`: `V(w) = 0.0`, `‖Im w‖ = 0.79`, `|b₀(w)| = 0.456`, from `V(s) = 0.507` |
| `(s(z(zs)))` (this report's own near-miss, §4a) | nonlinear in `s`; same codimension count | `V(w) = 9.5 × 10⁻³⁴`, `|b₀| = 0.000`, from `V(s) = 0.533` |
| `s + ½·z` (combo class) | `s ↦ norm(s + ½z)` is onto the whole state sphere | closed form: for a vacuum `y`, `s = t·y − ½z`, `t = ½⟨y,z⟩ + √(¼⟨y,z⟩² + ¾)` gives `V(w) = 0` exactly, `V(s) = 0.106`; 4/4 random `(y, z)` trials |

Why the enumeration could not see this: the preimage of the vacuum set under a fixed word has **codimension ≥ 4** in
`S¹⁴` (Red Team tail fit `P(σ < ε) ∝ ε^k` with `k ≈ 2.2–2.7` in log ε over 10⁶ uniform `s`, i.e. codim 4–5;
`P(σ < 10⁻³) ≤ 3 × 10⁻⁶`). 200 stratified `s` never land on a codim-≥ 4 set, and the expected number of `V < 10⁻⁸` hits in
`5 × 10⁸` evaluations is `N·ε^k ≈ 5 × 10⁻⁸ … 5 × 10⁻¹⁶` **whether or not the vacuum set lies in the image**. "0 hits"
therefore does not discriminate between the sealed position and its negation. Measure-zero reachability is true *by
construction* — three generators span the algebra (§4), and the image of each of the three word maps above meets the
vacuum set (witnesses in the table) — not something the sampling tested or could test.

**The driver's sealed position (S2/S3; #473 plan row 2) was mis-posed as a reachability claim; it is correct only under
the dynamical reading (7.1).** Recorded on #473 by qbp-oppenheimer (comment 5822879405, 2026-09-24) — surfaced for the
beekeeper, not absorbed: whether a literal firing of the rank-2 kill condition as written reopens anything is the
beekeeper's call under the plan ("reopened for the beekeeper — not reversed by the agent"). The Red Team's reading, and
the driver's, is that it does not touch Prop 16's *dynamics* statement.

**Kill condition, re-posed:** *a word-map with a positive-measure set of `s` landing on a non-pole vacuum, or an
iterated word-map with a non-pole vacuum attractor.* Under this posing the attack's result is 7.1.

### 7.1 What was shown — the dynamical negative

Three statements survive review and are the content of this record:

1. **Measure-zero reachability, true by dimensional intersection: the map s ↦ s·z is linear with a 12-dimensional image, and a 12-dimensional subspace meets the 8-dimensional vacuum manifold in a set whose preimage in the 15-sphere has codimension ≥ 4.** A fixed `(s, ℓ, z)`-word or fixed-coefficient combination reaches
   a non-pole vacuum only on a measure-zero set of `s` (codim ≥ 4; verified by construction for `s·z`, `(s(z(zs)))`,
   `s + ½·z`, 7.0). This is not a finding of the enumeration; it is established by the constructions in 7.0 (and `span(words) = 𝕊`,
   §4, is why such words exist at all).
2. **No positive-measure steering onto the vacuum.** No word map sends a positive-measure set of `s` onto a non-pole
   vacuum: on 200 stratified `s` × (84 basis-sum `z` and 50 ridge `z`), **≈ 5.06 × 10⁸ word evaluations** (3.17 × 10⁸
   basis-sum + 1.89 × 10⁸ ridge; three word classes), the smallest σ reached off the poles was `7.2 × 10⁻⁴` (combos) /
   `1.5 × 10⁻³` (pure words) — **sampling floors** (the smallest σ attained on the sampled `s`), consistent with the
   codim-≥ 4 tail; they are not bounds on the words (σ = 0 is attained, 7.0). In σ, the computed hit criterion is
   `σ < 2.5 × 10⁻³` at the `|b₀| = 0.999` cut (§1), so the floors and "0 hits" are consistent with each other and with
   the tail fit.
3. **No non-pole vacuum attractor.** The attractors of every normalised linear map `L_z`, `R_z`, `ad_z` are 4-dim ridge
   planes spanned by other canonical ZDs (§3, exact); **0 of 482 400** iterated linear-map trajectories (§5; 9 maps × 2
   variants × 26 800 pairs) and **0 of 765 440** iterated nonlinear word-map trajectories (§5b; 618 240 + 147 200) end
   at a non-pole vacuum; every small-`V` endpoint is a pole approach on a σ-conserving stratum (the `(x, ℓ)`-only maps —
   Prop 16(ii) seen dynamically) or on the σ ≡ 1 stratum, where the only vacua are the poles (§5c). The `(s, ℓ)`-only
   words conserve σ to round-off (§4 control).

Under the re-posed kill condition the attack does **not** fire; `KILLED-locale-forcing-route` stands against this attack
**in its dynamical reading only**. The kill's *conclusion* is untouched — Prop 13(b) needs a rule selecting endpoints for
generic states, and a measure-zero preimage is not one. The negative is Aut-exact (§6) and basis-free (the ridge-`z` runs
reproduce every number to the percent).

**Consequence for Prop 16.** Its clause "the only vacua reachable from a non-vacuum `s` are `±ℓ`" holds for the
operations on `(s, ℓ)` (Lean closure into `ℍ_s`) but **needs a qualifier once the canonical zero-divisor set is admitted as
a third generator**: there it must read "no positive-measure / no attractor route to a non-pole vacuum" — every vacuum
*is* the image of some `s` under a fixed word, but only for a codim-≥ 4 set of `s`. Attack 2's row in the v0.6 addendum is
being corrected accordingly (#680).

**What the words DO — the sharpening of Prop 16 this attack buys:**

1. **Three generators generate everything, but no fixed word steers.** `span(words in s, ℓ, z)` is the full 16-dim
   algebra (vs 4 for `(s, ℓ)`), so the *subalgebra* contains every vacuum and every non-pole vacuum is reached by some
   fixed word from some `s` (7.0) — but only from a measure-zero set of `s`; landing on the vacuum from *generic* `s` needs
   `s`-dependent coefficients. Prop 16's "symmetries, never dynamics" survives the loss of its invariant subspace in its
   dynamical form: no algebra-native map has a non-pole vacuum as an attractor, and none steers a positive-measure set of
   `s` onto the vacuum. (The sentence that stood here — "avoids the non-pole vacuum set entirely … no algebra-native map
   has the vacuum set in its image other than at `±ℓ`" — is withdrawn; see 7.0.)
2. **The ZD's canonical attractors are ridge planes.** `L_z`, `R_z` for a basis-sum `z` have one spectrum
   `{2 ×4, √2 ×8, 0 ×4}` (`ad_z` on all of `𝕊`: `{4 ×4, 2√2 ×6, 0 ×6}`, §2); the top space and the kernel are 4-dim planes
   lying *identically* on the ridge, each spanned by four other basis-sum ZDs
   (`T(e₁+e₁₀) = span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂} = K(e₁−e₁₀)`; reproduced exactly in ℚ by the Red Team). This is the
   structural reason the generic-`t` observation "top plane lies on `V = 1`" (`NoAutonomousDynamics.lean`, Completeness,
   observed 100/100 — NOT derived) holds *exactly and by name* for the canonical set — a candidate Lean target (finite:
   84 elements × 16 basis columns).
3. **Mass goes to the ridge and the poles, never to the 8-dim vacuum — on the sampled `s`.** Of the pure-word evaluations
   12.6% land exactly on `±ℓ`, 57% of the non-pole remainder have σ > 0.95, 0.7% have σ < 0.05, none σ = 0 on the 200
   sampled `s` (7.0: σ = 0 is attained on a codim-≥ 4 set). The `x + z ± ℓ` maps have the fixed point `(z ± ℓ)/‖·‖` with
   `V = 1/4`, `b₀ = ±1/√2` — a canonical non-vacuum, non-ridge point.
4. **Exact identities found on the way:** `xz + zx = −2(x_i ± x_j)` is real on `Im𝕊` (Jordan map degenerate);
   `x((xz)z)` maps `Im𝕊` into the `b₀ = 0` slice; `(x, ℓ)`-only maps conserve σ dynamically to 1e-12 (Prop 16(ii) as a
   flow statement); `z(x(ℓx))` and `x(ℓ(xz))` map onto the σ = 1 stratum.

**What this does not show (extended after review, F5).**

1. **Reachability — not tested, and not testable by this method.** The preimage of the vacuum under a fixed word has
   codim ≥ 4, so every "0 hits" and every σ_min here is a statement about 200 stratified `s` (expected hits under the
   alternative `5 × 10⁻⁸ … 5 × 10⁻¹⁶`). Reachability is decided by construction or optimisation (the Red Team did it: three
   words hit, 7.0); steering is decided by a measure estimate (the tail exponent `k ≈ 2.2–2.7`), which this record did not
   compute itself.
2. **Coefficient restriction.** The combination class is two-term only, `ŵ₁ + c·ŵ₂` with `c ∈ {±1, ±2, ±½}` and words of
   length ≤ 3; three-term combinations, other coefficients, and `s`-dependent coefficients were not tested (with
   `s`-dependent coefficients every vacuum is reachable trivially, since the span is all of `𝕊`).
3. **The `|b₀| ≥ 0.999` slab is excluded by definition** (§1): a genuine non-pole vacuum with `b₀` that close to `±1`
   counts as a pole landing. Measure-tiny, but it is a definition of "pole", not a result.
4. **Length and multiplicity.** Words of length ≥ 6, three or more distinct ZDs in one word (`z₁ z₂ = 0` pairs); the
   nonlinear map census is length ≤ 4 and 100 steps (2000 for the four near-miss families).
5. The σ_min-by-length trend (5.3e-3 → 2.7e-3 → 2.7e-3 basis; 4.9e-3 → 1.5e-3 ridge) is a sampling-floor trend and says
   nothing about reachability (7.0). For the *dynamical* question (attractors of longer words), a length-6/7 run on the
   four `(s,(s,z)z)`-type families is the cheapest follow-up if anyone wants to press.

## 8. Resource log and files

All compute ran under `run-bounded <mem> <secs>` with a prior written estimate (`resource_log.txt`). Two estimates
were wrong and the cap did its job: the un-chunked `attack2_words.py` at 200 `s` was OOM-killed at 6 GB (basis) and 4 GB
(ridge) — heap fragmentation from thousands of 2 MB temporaries (measured 0.55 MB/row vs 0.09 MB/row live); fixed by
chunked accumulation + `MALLOC_MMAP_THRESHOLD_=65536` (peak 1.21 GB both, 27:44 and 17:48 wall). The first
`attack2_equiv.py` timed out at 600 s (unvectorised 256-pair residual × 360 grid angles); vectorised, 203 s. A first
full enumeration pass had a word-naming collision (level-2 names unparenthesised) that merged distinct trees in the
*per-word* tables only (hits and histograms are per evaluation and were identical); rerun with the fix — the numbers in
§4 are from the rerun (3873 distinct pure names asserted).

| file | role |
|---|---|
| `flowlib.py` | product / potential (from `research/635-analysis-records`) |
| `zdlib.py` | ZD enumeration, `L`/`R` matrices, stratified states, `G₂` elements, 256-pair automorphism check, exact-rational product |
| `zd_enum_check.py` → `out_zd_enum.json` | §2 |
| `zd_subspaces.py` → `out_zd_subspaces.json` | §3 |
| `attack2_words.py {basis,ridge}` → `out_words_*.json`, `log_words_*.txt` | §4 |
| `attack2_maps.py {basis,ridge}` → `out_maps_*.json`, `log_maps_*.txt` | §5 |
| `attack2_wordmaps.py {basis,ridge}` → `out_wordmaps_*.json`, `log_wordmaps_*.txt` | §5b |
| `attack2_nearmiss.py` → `out_nearmiss.json` | §5c |
| `attack2_equiv.py` → `out_equiv.json`, `log_equiv.txt` | §6 |
| `resource_log.txt` | estimates vs actuals |

**Slab note (Gemini #676):** the excluded |b₀| ≥ 0.999 slab was treated as pole-by-definition; the iterated maps' only attractors there are the poles ±ℓ themselves (every trajectory entering the slab converges to ±ℓ in the runs recorded; no fixed point with 0.999 ≤ |b₀| < 1 was observed) — so the exclusion hides no near-pole attractor distinct from the poles. Recorded as an observation on the existing runs, not a new computation.
