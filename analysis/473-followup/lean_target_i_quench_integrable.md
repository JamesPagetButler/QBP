# Lean target 6(i) — the rule's descent is INTEGRABLE in the Gram invariants

**Module:** `proofs/QBP/Substrate/RuleFlowInvariants.lean` (909 lines, 93 declarations, 0 `sorry`, 0 `native_decide`, 0 vacuous `True`).
**Branch:** `research/473-followup-6a` (worktree `probe-473-6a`, off master `6d87fdc`). Wired into `proofs/QBP/Substrate.lean`.
**Derivation of record:** `analysis/473-kill-attack/attack1_anneal_vs_quench.md` §3a (worktree `probe-kill-1`, read-only here).
**Upstream:** `QBP.Substrate.RuleFlow` (#635) — the rule is a POSTULATE there and stays one here.

---

## 1. What the file proves (traffic light)

| # | Claim | Lean name | Status |
|---|---|---|---|
| 1 | `V = 4(A·C − P²)` in the Gram invariants `A = N(Im a)`, `C = N(Im b)`, `P = ⟪Im a, Im b⟫` | `potential_eq_gram` | PROVED (restates `RuleFlow.potential_eq_cross`) |
| 2 | Sphere constraint `A + C + b₀² = 1`; `b₀² ≤ 1`; discriminant `V ≤ (1 − b₀²)²` | `gram_sum_eq_one`, `ellSq_le_one`, `potential_le_one_sub_ellSq_sq` | PROVED |
| 3 | Euler relation `⟪∇V(s), s⟫ = 4V(s)`; `(∇V)₀ = 0` | `bil_gradV_self`, `gradV_coord_zero` | PROVED |
| 4 | The four gradient pairings `⟪∂ₐV, Im a⟫ = ⟪∂_b V, Im b⟫ = 2V`, `⟪∂ₐV, Im b⟫ = ⟪∂_b V, Im a⟫ = 0` | `bil_cdLo_gradV_gramLo`, `bil_cdHi_gradV_gramHi`, `bil_cdLo_gradV_gramHi`, `bil_cdHi_gradV_gramLo` | PROVED |
| 5 | **The closed ODE system** along any integral curve: `Ȧ = 4V(2A−1)`, `Ċ = 4V(2C−1)`, `Ṗ = 8VP`, `ḃ₀ = 4Vb₀`, `d(b₀²)/dt = 8Vb₀²` | `hasDerivAt_gramA_along_flow`, `hasDerivAt_gramC_along_flow`, `hasDerivAt_gramP_along_flow`, `hasDerivAt_ellCoeff_along_flow`, `hasDerivAt_ellSq_along_flow` | PROVED (no state-sphere hypothesis) |
| 6 | Consistency `Ȧ + Ċ + d(b₀²)/dt = 0` on the state sphere | `gram_sum_hasDerivAt_zero` | PROVED |
| 7 | **`b₀²` is monotone non-decreasing** along any integral curve (since `V ≥ 0`) | `ellSq_monotone_along_flow` | PROVED |
| 8 | **Straight-ray motion**: every 2×2 minor of `(A−½, C−½, P, b₀²)(t)` against its value at `t₀` vanishes | `ray_minor_eq_zero`, `gram_ray`, `rayVec_collinear` | PROVED |
| 9 | **The conserved quadratic** `V·B₀² = B²(V₀ + 2B₀ − 1) − 2B₀²B + B₀²`, `B = b₀²`, at every time | `quench_relation`, `quench_relation_univ` | PROVED |
| 10 | Root selection: an admissible root `L ∈ [0,1]` satisfies `L(B₀ + √((1−B₀)² − V₀)) = B₀` | `quench_root_pick_aux`, `quench_root_pick` | PROVED (algebra, division-free) |
| 11 | The endpoint never falls below the start: `B₀ ≤ L` | `quench_root_ge_initial`, `ellSq_limit_ge_initial` | PROVED |
| 12 | **The endpoint** `b₀²(∞) = b₀²/(b₀² + √((1 − b₀²)² − V₀))` | `ellSq_tendsto_closed_form`, `ellSq_limit_eq_closed_form` | PROVED **CONDITIONAL** on `V(γ t) → 0` and `b₀²(γ t) → L` (both hypotheses; neither is proved) |
| — | Existence of integral curves (local or global) | — | **OPEN** (inherited FLAG-rule-flow-open, #635) |
| — | Convergence `V(γ t) → 0`, existence of the limit `L` | — | **OPEN** — carried as hypotheses, never discharged |
| — | The ensemble averages 0.1416 / ⅓ | — | **NUMERICAL ONLY** (see §4) |

Every theorem has the shape *"IF `γ` is an integral curve of `F` (and, where stated, is on `StateSphere` / converges), THEN …"*. The antecedent is never discharged. The rule itself is still the postulate of `RuleFlow`.

## 2. The statements that carry the target

Notation: `a = cdLo s`, `b = cdHi s`; `A = N(Im a)`, `C = N(Im b)`, `P = ⟪Im a, Im b⟫`, `b₀ = (cdHi s).coord 0` (= coordinate 8 of the sedenion); `V = Hosting.potential`; `F = ruleField`.

**(1) The ODE system.** For every `t` with `HasDerivAt γ (F (γ t)) t`:

```
hasDerivAt_gramA_along_flow  : HasDerivAt (fun r => gramA (γ r)) (4*V(γ t)*(2*gramA (γ t) - 1)) t
hasDerivAt_gramC_along_flow  : HasDerivAt (fun r => gramC (γ r)) (4*V(γ t)*(2*gramC (γ t) - 1)) t
hasDerivAt_gramP_along_flow  : HasDerivAt (fun r => gramP (γ r)) (8*V(γ t)*gramP (γ t)) t
hasDerivAt_ellCoeff_along_flow : HasDerivAt (fun r => ellCoeff (γ r)) (4*V(γ t)*ellCoeff (γ t)) t
hasDerivAt_ellSq_along_flow  : HasDerivAt (fun r => ellCoeff (γ r)^2) (8*V(γ t)*ellCoeff (γ t)^2) t
```

This is exactly the system of attack 1 §3a, with no state-sphere hypothesis: the rule closes on the four `G₂ × O(2)`-invariants on all of `CDAlg ℝ 4`.

**(2) The ray.** `IsRayCoord f` means `f` is continuous and `d/dt f(γ t) = 8V(γ t)·f(γ t)` along every integral curve. `A − ½`, `C − ½`, `P`, `b₀²` are all ray coordinates (`isRayCoord_gramA_sub`, `isRayCoord_gramC_sub`, `isRayCoord_gramP`, `isRayCoord_ellSq`), and

```
rayVec_collinear : ∀ i j : Fin 4, ∀ t ∈ Icc a b,
    rayVec (γ t) i * rayVec (γ t₀) j = rayVec (γ t) j * rayVec (γ t₀) i
```

i.e. the point moves on a straight ray through `(½, ½, 0, 0)` in **any** time parametrisation. The proof is `RuleFlow.scalar_linear_ode_zero` (Mathlib `ODE_solution_unique_of_mem_Icc`) applied to the minor `u(t) = f(γ t)g(γ t₀) − g(γ t)f(γ t₀)`, which satisfies `u' = 8V·u` and `u(t₀) = 0`. Note what is proved is *collinearity* (all pairwise minors vanish) — the existence of the ray parameter `λ = e^{2τ}` is a consequence, not an assumption, and the reparametrised time `dτ = 4V dt` of §3a is never used (it is not available without existence/positivity of `V` along the curve).

**(3) The endpoint (conditional).**

```
ellSq_tendsto_closed_form :
  (∀ t, HasDerivAt γ (ruleField (γ t)) t) → γ t₀ ∈ Hosting.StateSphere →
  Tendsto (fun t => V (γ t)) atTop (𝓝 0) → Tendsto (fun t => ellCoeff (γ t)^2) atTop (𝓝 L) →
  L * (ellCoeff (γ t₀)^2 + √((1 - ellCoeff (γ t₀)^2)^2 - V (γ t₀))) = ellCoeff (γ t₀)^2
```

with the division form `ellSq_limit_eq_closed_form` under a non-vanishing-denominator hypothesis (the denominator vanishes only in the degenerate case `b₀(t₀) = 0`, `V₀ = 1`). The root is *selected*, not assumed: `quench_root_pick` shows any `L ∈ [0,1]` solving the quadratic satisfies the "smaller root" relation, using `0 ≤ B₀`, `L ≤ 1` and the discriminant bound `V ≤ (1 − b₀²)²` proved in §1 of the module.

## 3. What is NOT proved (unchanged, and stated in the module docstring)

1. **Existence** of integral curves of `F` — local or global. Every theorem is conditional on a given curve. `ellSq_tendsto_closed_form` additionally assumes a curve defined on all of `ℝ`.
2. **Convergence** `V(γ t) → 0` as `t → ∞`, and existence of `lim b₀²(γ t)`. Both are hypotheses.
3. **The rule** — still the POSTULATE of `RuleFlow` (#635). Nothing here argues it is the right rule.
4. **Any measure or ensemble statement.** The file proves the per-orbit map that the quench average integrates; it does not prove that the Haar integral of that map is 0.1416, nor anything about the anneal.

## 4. The numerical leg and the 0.146 → 0.1416 correction (#675)

Attack 1 (`analysis/473-kill-attack/attack1_anneal_vs_quench.md`) established numerically, and issue **#675** carries the correction to the record:

* `⟨b₀²⟩_quench = E_Haar[B/(B + (1−B)√(1−4κ))] = **0.141587**` (3-d quadrature; 10⁷-point Haar MC gives 0.14162 ± 0.00005);
* the on-record **0.146** is `0.1416 + 0.0031`, a **renormalised-Euler `h = 0.02` discretisation bias** (RK4 ladder with h⁴ scaling and adaptive DP45 reproduce the closed form to 10⁻⁸–10⁻¹¹ per seed);
* the anneal limit is **⅓ exactly**, with finite-β law `⅓ − 0.5539 β^{−1/2}`.

This Lean module proves the **per-orbit closed form** those integrals use (item 12 above, conditionally on convergence) — it does **not** prove 0.1416, which remains a numerical quadrature result. The same numbers 0.146/0.1462/0.1454/0.1436 appear in Props 9, 12, 14, 16 of the AC1 record; correcting them is #675's business, not this module's.

## 5. Verification record

| Check | Command | Result |
|---|---|---|
| Build (module + aggregator) | `run-bounded 6G 1800 taskset -c 0-2 lake build QBP.Substrate` | **exit 0**, `Build completed successfully (3126 jobs)`; peak RSS **3.67 GB**, 17.6 s for the module |
| `#print axioms` (all 93 declarations, §8 of the module) | replayed in the build log | every one is exactly `[propext, Classical.choice, Quot.sound]` — 93/93 |
| Audit-block completeness | declarations vs `#print axioms` lines | 93 vs 93, no gaps |
| Foundations gate | `python3 scripts/check_lean_foundations.py --dir proofs/QBP/Foundations` | `Lean foundations gate PASSED` (exit 0) |
| Layer-import gate | `python3 scripts/check_layer_imports.py` | `layer imports clean` (exit 0) |
| Hygiene | grep | 0 `sorry`, 0 `native_decide`, 0 `: True :=` |

**Known resource obstacle (pre-existing, not from this change):** a *full* `lake build` in this worktree cannot finish under a 6 GB cgroup cap — `QBP.Foundations.Octonion32Count` and `QBP.Foundations.FanoGenesis` (kernel-`decide` enumerations, untouched here, last changed in master `5343521`) are OOM-killed with exit 137, `Octonion32Count` even when built alone on a single core (killed at 125 s). Their `.olean`s exist in the main worktree from earlier builds (2026-06-04 / 2026-08-21), so this is a per-worktree memory-headroom issue for those two modules, not a breakage. The cap was **not** raised.
