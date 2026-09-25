# Lean target 6(ii) — the zero-divisor spectrum, mechanised

**Artifact:** `proofs/QBP/Foundations/SeamSpectrum.lean` (1574 lines, 153 declarations)
**Wiring:** imported from the `proofs/QBP/Foundations.lean` aggregator.
**Status:** 0 `sorry`, 0 `native_decide`, 0 vacuous `: True :=`; all 153 declarations carry a
`#print axioms` line and every one resolves to a subset of `{propext, Classical.choice, Quot.sound}`.
**Numerical origin (flashlight, not evidence):** `analysis/473-kill-attack/attack2_zd_words.md` §2, §3
(branch `research/473-kill-attack-2`). Nothing in this file cites a numerical run as a premise.

---

## 1. What is now a theorem

All statements are about the real algebra `𝕊 = CDAlg ℝ 4` with `N` the Euclidean norm form and
`bil` its polar inner product. `z₊ = e₁ + e₁₀` (`SeamKernel.seamX`), `z₋ = e₁ − e₁₀` (`seamXm`).

| # | Claim (plain math) | Lean name |
|---|---|---|
| 1 | `L_z` is skew-adjoint: `⟨z·y, w⟩ = −⟨y, z·w⟩` | `seamL_skew` |
| 2 | `G := −L_z∘L_z` **is** the Gram operator: `⟨L_z y, L_z w⟩ = ⟨y, G w⟩` (no adjoint postulated) | `seamGram_eq` |
| 3 | `G = 4` exactly on `T = span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂}` | `seamEig_four_eq` |
| 4 | `G = 2` exactly on `M = span{e₀,e₁,e₂,e₃,e₈,e₉,e₁₀,e₁₁}` | `seamEig_two_eq` |
| 5 | `G = 0` exactly on `K = span{e₇+e₁₂, e₆−e₁₃, e₅+e₁₄, e₄−e₁₅}` (= `SeamKernel.seamKerSpan`) | `seamEig_zero_eq` |
| 6 | `dim T = 4`, `dim M = 8`, `dim K = 4` | `finrank_seamEig_four/two/zero` |
| 7 | Every sedenion decomposes: `x = projMid x + projTop x + projKer x` (explicit projections) | `proj_decomp` |
| 8 | **No other eigenvalue:** `G(G−2)(G−4) = 0`, so `c ∉ {0,2,4} ⟹ E_c = ⊥` | `seamG_cubic`, `seamEig_eq_bot_of_ne` |
| 9 | Packaged: (2)+(3)+(4)+(5)+(6)+(7); and exhaustiveness with `4+8+4 = 16` | `seam_gram_spectrum`, `seam_gram_spectrum_exhaustive` |

So the funded claim — **`L_zᵀL_z` has eigenvalues 4 (×4), 2 (×8), 0 (×4)**, i.e. singular values
`2 (×4)`, `√2 (×8)`, `0 (×4)` for `L_z` — is proved *with the eigenspaces identified exactly* and the
eigenvalue list proved complete, via an explicit orthogonal decomposition of ℝ¹⁶.

**Completeness is over the real spectrum, and that is not a restriction.** `seamEig_eq_bot_of_ne`
quantifies over `c : ℝ`; but `proj_decomp` together with the three eigen-actions *diagonalises* `G` over
ℝ (`G` is even self-adjoint, `seamG_self_adjoint`), so the complexified operator is diagonal with the
same entries — no complex eigenvalue can hide. The decomposition is `bil`-orthogonal as a theorem, not
merely in coordinates: `bil_topSpan_midSpan`, `bil_topSpan_seamKerSpan`, `bil_midSpan_seamKerSpan`, and
it exhausts 𝕊 as submodules (`midSpan_sup_topSpan_sup_seamKerSpan : M ⊔ T ⊔ K = ⊤`), not only by the
finrank sum.

### The two ridge identities

| # | Claim | Lean name |
|---|---|---|
| 10 | `T(e₁+e₁₀) = ker L_{e₁−e₁₀}` — the top plane of one sign is the kernel of the other | `seamLm_ker_eq` |
| 11 | Every nonzero `t ∈ T` is a **two-sided zero divisor**, all annihilated by the *same* `z₋ ≠ 0` | `top_plane_zero_divisor` |
| 12 | Each spanning vector of `T` is itself a basis-sum zero divisor `e_i ± e_j` | `top_generators_are_zero_divisors` |
| 13 | **`V(t) = N(t)²` on the whole of `T`** (so a unit vector of `T` sits at the ridge value `V = 1`), where `V(x) = ‖[cdLo x, cdHi x]‖²` | `top_plane_on_ridge_of`, `top_plane_on_ridge`, `top_plane_on_ridge_mem` |

(13) is proved for the entire 4-dimensional plane, not only for its four generators, via the octonion
Lagrange identity `V = 4(N(a)N(b) − ⟨a,b⟩²)` on pure halves (`potV_eq_gram`).

### Right multiplication (the "if cheap" item — it was)

| # | Claim | Lean name |
|---|---|---|
| 14 | `(x·z)·z = z·(z·x)` for every `x`, for **both** signs `z = e₁ ± e₁₀` | `seam_gram_lr`, `seam_gram_lr_m` |
| 15 | Hence `R_zᵀR_z = L_zᵀL_z` **as linear maps** | `seamGR_eq_seamG` |
| 16 | `R_z` is skew-adjoint, and `seamGR` is genuinely its Gram operator | `seamR_skew`, `seamRGram_eq` |
| 17 | `R_z` therefore has the identical spectrum `4/2/0` on the identical eigenspaces `T/M/K` | `seamR_gram_spectrum` |
| 18 | `ker R_{z₋} = T` as well (upgrades the previous `≤` to `=`) | `seamRm_ker_eq` |

(14) is **not** formal: 𝕊 is neither associative nor alternative, so `(x·z)·z = z·(z·x)` is a genuine
sign-table identity. It is reduced to two kernel-`decide` facts over `Fin 16` (`seam_gram_diag`,
`seam_gram_off`) plus the XOR index lemma `seam_xor_idx` — 16 cases each, no `native_decide`.

### Uniform facts, valid for all 84 basis-sum zero divisors

For *every* pair of basis units `e_a, e_b` (hence all 84 basis-sum ZDs, and more):

| # | Claim | Lean name |
|---|---|---|
| 19 | `N(z₊·x) + N(z₋·x) = 4·N(x)` (parallelogram law for the two basis isometries) | `N_basisPair_split` |
| 20 | `N(z₊·x) ≤ 4·N(x)` — top singular value of `L_{z₊}` is at most 2, uniformly | `N_basisPair_le` |
| 21 | Equality holds **exactly** on `ker L_{z₋}` | `N_basisPair_eq_iff` |
| 22 | Operator form `G₊ + G₋ = 4·id` | `basisPair_sq_split` |
| 23 | `L_{e_a+s·e_b}` is skew-adjoint; `z·(z·x) = 0 ↔ z·x = 0` | `sbp_skew`, `sbp_sq_eq_zero_iff` |
| 24 | `G_z := −L_z∘L_z` **is** the Gram operator of `L_z`, uniformly; Rayleigh form `⟨y, G_z y⟩ = N(z·y)` | `sbpGram_eq`, `sbpG_rayleigh` |
| 25 | **`spec(G_z) ⊆ [0, 4]`** — every real eigenvalue of `G_z` (`z = e_a ± e_b`, `x ≠ 0`) lies in `[0,4]`, i.e. singular values of `L_z` lie in `[0,2]` | `sbpG_eigenvalue_mem_Icc` |
| 26 | **`E₄(G₊) = ker L_{z₋}`** for every basis pair | `sbpEig_four_eq` |
| 27 | **`E₀(G_z) = ker L_z`** for every basis pair, either sign | `sbpEig_zero_eq` |

Rows 25–27 are the pair-generic *spectral* statements; they are named declarations, over the uniform
Gram operator `sbpG` / eigenspace `sbpEig` (`sbpL` = left multiplication by `e_a + s·e_b` as a linear
map). Row 25's ≤ 4 half also needs the `−`-sign norm bound `N_basisPair_le_neg`. Rows 25–27 fix NO
multiplicity: that is the witness-only content (rows 3–6).

---

## 2. Proved vs. numerical, for the 84

| Statement | For `z = e₁ + e₁₀` | For the other 83 |
|---|---|---|
| `spec(L_zᵀL_z) ⊆ [0, 4]` | **proved** (19–20, 25) | **proved** — `sbpG_eigenvalue_mem_Icc` (25) |
| `E₄(G₊) = ker L_{z₋}`, `E₀(G₊) = ker L_{z₊}` | **proved** (3, 5, 10) | **proved** — `sbpEig_four_eq`, `sbpEig_zero_eq` (26–27) |
| `G₊ + G₋ = 4·id` | **proved** | **proved** (22 is uniform) |
| multiplicities **4 / 8 / 4** | **proved** (3–6, 8) | **NOT proved** — numerical only (attack-2 §2: one spectrum for all 84) |
| `R_z` spectrum = `L_z` spectrum | **proved** (14–17) | **NOT proved** |
| `T` on the ridge, `V = N²` | **proved** (13) | **NOT proved** (attack-2 §3 reports it for the 9 `z` tested) |
| `ad_z` spectrum `{4×4, 2√2×6, 0×6}` | **NOT proved** | **NOT proved** |

**Why the 84 were not done uniformly.** The uniform machinery (19–27) is genuinely uniform and is
stated for arbitrary basis pairs. What does *not* generalise is the multiplicity count: it rests on
eight explicit sign-table computations (`seamG_e0 … seamG_e11`) identifying the 8-dimensional middle
block for *this* pair `{1, 10}`. A uniform proof would need the statement "for every basis-sum ZD pair
`{a,b}`, `dim ker L_{e_a+e_b} = 4`", which is a `decide`-shaped claim over 84 pairs × a 16×16 rank
computation over ℝ — not decidable as stated (Rule 8: no `decide` over ℝ), and the rank argument would
have to be re-run per pair. No uniform proof was found, so, per the brief, the witness result is stated
and the generalisation is labelled numerical. This is tracked honestly in the file header under
"What this file does NOT prove".

**Why `ad_z` was not done.** `ad_z = L_z − R_z`, so `ad_z² = L_z² + R_z² − (L_zR_z + R_zL_z)`; the cross
term is `z·(x·z) + (z·x)·z`, which neither `G₊ + G₋ = 4·id` nor the left/right Gram identity (14)
controls. Consistently, attack-2 reports a *different* decomposition for `ad_z` (dims 4/6/6, not 4/8/4),
so it is not a corollary of anything proved here. It remains numerical.

---

## 3. Consequence for `NoAutonomousDynamics`' caveat

`proofs/QBP/Foundations/NoAutonomousDynamics.lean` ("Completeness", line ~80) says:

> With an UNFORCED second element t, the maps x ↦ x·t, t·x, **[x,t]** are linear (R_t, L_t, ad_t); their
> normalised iteration is power iteration onto the top-singular subspace — **which numerically
> lies on the zero-divisor ridge V = 1 (observed for 100/100 t, NOT derived)** …

Note the quantifier and the *three* maps: the caveat is about `R_t`, `L_t` **and `ad_t = L_t − R_t`**,
for a generic unforced `t`. This file speaks only about `L_z` and `R_z`, and only at the canonical
basis-sum zero-divisor generators. `ad_z` is explicitly out of scope (file header): attack-2 §2 reports
a *different* decomposition for it (dims 4/6/6, σ = {4×4, 2√2×6, 0×6}), so its top space is not
`T(L_z)` a priori and nothing proved here transfers to it.

**What this file closes.** For **`L_z` and `R_z`** (not `ad_z`) at the canonical, `Aut(𝕊)`-invariant
generator class — the basis-sum zero divisors, witness `z = e₁ + e₁₀` — the top singular subspace lying
on the ridge is now **derived**, in two senses and for the entire plane, not a sample. (`R_z` is covered
because `R_zᵀR_z = L_zᵀL_z` on the nose, `seamGR_eq_seamG`, so it has the *same* top space `T`.)


* qualitatively: every nonzero element of `T` is a two-sided zero divisor (`top_plane_zero_divisor`),
  all four generators being basis-sum ZDs themselves (`top_generators_are_zero_divisors`) — so `T` is a
  4-dimensional ridge plane *inside the 42-plane system*, a closed sub-structure;
* quantitatively: `V(t) = N(t)²` identically on `T` (`top_plane_on_ridge_mem`), i.e. `V = 1` for every
  unit vector of `T` — exactly the observed `[1.0000, 1.0000]` of attack-2 §3, now a theorem.

**What this file does NOT close.** Two gaps, both in the caveat as written:

1. **generic unforced `t`** (`generic_maps_check.py`, 100/100 random `t`). Nothing here says anything
   about generic `t`: the proofs use that `z` is a basis *sum*, and the eigenspace identification uses
   the `{1,10}` sign-table block.
2. **`ad_z = L_z − R_z`**, the third map the caveat names. Its square carries the mixed term
   `z·(x·z) + (z·x)·z`, which neither `G₊ + G₋ = 4·id` nor the left/right Gram identity (14) controls,
   and attack-2 measures a different decomposition (4/6/6) for it — so its top space is a different
   subspace and its ridge property is untouched here.

So the honest amendment to the caveat is:

> DERIVED for `L_z` and `R_z` at the canonical basis-sum zero-divisor generator pair (`SeamSpectrum`,
> witness `e₁+e₁₀`: `top_plane_zero_divisor`, `top_plane_on_ridge_mem`, `seamRm_ker_eq`); `ad_z` and a
> generic unforced `t` remain **observed-only**.

The corresponding recommendation is to edit that sentence in `NoAutonomousDynamics.lean` to cite
`SeamSpectrum.top_plane_on_ridge_mem` for the `L_z`/`R_z` ZD case and retain "NOT derived" for `ad_z`
and for generic `t`. That edit is **not** made in this commit (it touches an already-anchored file; it
is a separate, reviewable change), and no ledger anchor is added here.

---

## 4. Verification record

```
$ cd proofs && run-bounded 6G 1800 taskset -c 3-5 lake build QBP.Foundations.SeamSpectrum
EXIT=0            # 0 errors; 153 `#print axioms` lines emitted
```

* axiom audit: 150 declarations `[propext, Classical.choice, Quot.sound]`, 3 declarations `[propext]`
  only (`midIdx`, `midIdx_spec`, `seam_xor_idx` — pure `Fin`/ℤ `decide`). **No `sorryAx`, no
  `ofReduceBool`/native axiom, no user axiom.**
* `#print axioms` coverage: 153 declarations in the file, 153 audit lines, no gaps, no strays.
* `python3 scripts/check_lean_foundations.py --dir proofs/QBP/Foundations` → `Lean foundations gate PASSED`
  (sorry at baseline 0, vacuous-`: True :=` at baseline 0).
* `python3 scripts/check_layer_imports.py` → `layer imports clean`;
  `python3 scripts/test_check_layer_imports.py` → `23/23 tests passed`.

**Known local build limitation (pre-existing, not caused by this change).** A whole-aggregator
`lake build QBP.Foundations` in this worktree reaches 3548/3549 targets and then the pre-existing module
`QBP.Foundations.Octonion32Count` (heavy `decide +kernel`, `set_option maxHeartbeats 4000000`, imports
only Mathlib — it does **not** import `SeamSpectrum`) is OOM-killed at the 6 GB cgroup cap
(`run-bounded` exit 137), single-core as well as on 3 cores. Per the resource rule this was **not**
retried with a larger cap. `SeamSpectrum` itself builds green in isolation, and the aggregator change is
a one-line `import`.
