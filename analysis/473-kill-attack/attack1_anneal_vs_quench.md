# ATTACK 1 — anneal vs quench (Prop 9 of `docs/foundations/473-ac1-first-link-2026-09-04.md`)

**Branch:** `research/473-kill-attack-1` (worktree `probe-kill-1`, off master). Plan: #473 comment 5808096164.
**Target:** Prop 9 — "gradient-flow quench ⟨b₀²⟩ = 0.146; Gibbs anneal β → ∞ ⟨b₀²⟩ → ≈ 1/3, same N-measure".
**Kill condition for this leg (numerical only):** the two numbers coincide, or 0.146 is an artefact (integrator, stopping rule, sampling).
**Nothing here is a theory claim; nothing here touches `proofs/` or the ledger.**

Conventions (all on record): x ∈ ℝ¹⁶, x[0] = 0, ‖x‖ = 1; cdLo = x[0:8] = a (imaginary octonion), cdHi = x[8:16] = b = b₀ + c; ℓ = e₈, b₀ = x[8];
V(x) = ‖ab − ba‖² (octonion commutator) = 4(|a|²|c|² − ⟨a,c⟩²) = 4·det Gram(a, c) (`potential_eq_cross`; re-verified below to 7·10⁻¹⁶ against `flowlib.potential`).
Vacuum manifold M = {V = 0} = {a ∥ c}; r² = |a|² + |c|² = 1 − b₀².

---

## 0. Sealed expectations (written BEFORE any run; this section is not edited afterwards)

| Leg | Sealed expectation | Driver's sealed position |
|---|---|---|
| A analytic anneal | The Laplace factor det(H⊥)^{-1/2} = (8r²)^{-3} = 8⁻³ r⁻⁶ and the surface element of M in the round S¹⁴ metric, r⁶ dθ dΩ₆ db₀, cancel **exactly**; the β → ∞ density on the vacuum S² is dθ db₀ (Archimedes-uniform), so ⟨b₀²⟩_∞ = 1/3 exactly. A second, independent route (reduce Haar on S¹⁴ to the three invariants (b₀, t = |a|²/r², φ = ∠(a,c)) and take β → ∞ there) must give the same. Finite-β deficit 1/3 − ⟨b₀²⟩_β ∝ β^{-1/2} (the near-pole band r ≲ β^{-1/4} is outside the Laplace regime); the existing importance-sampling numbers 0.121/0.167/0.245/0.290 at β = 5/10/40/160 all give c = (1/3 − value)·√β ≈ 0.53–0.56, so I seal c ≈ 0.55. | factors cancel, uniform on S², 1/3 exactly — **held** if the algebra above survives the exact quadrature |
| A exact quadrature | 3-d quadrature of ⟨b₀²⟩_β must give 1/15 = 0.0667 at β = 0 and land within the MC errors of the on-record importance-sampling values at β = 5, 10, 40, 160 (their 1σ ≈ 0.001, 0.002, 0.007, 0.03); at β = 10⁴–10⁶ it must approach 1/3 from below with the β^{-1/2} law. | — |
| B MCMC anneal | Random-walk Metropolis on S¹⁴ with `flowlib.potential` (no reduction) at β = 10, 30, 100, 300, 1000: every value within 2σ of the quadrature; two different initial ensembles agree. | monotone toward 1/3 — **held** if so |
| B Hessian isotropy | At 50 random vacua (random b₀, θ, u ∈ S⁶): intrinsic 14×14 Hessian of V on T S¹⁴ has 8 eigenvalues = 0 (rank 6) and 6 eigenvalues = 8(1 − b₀²), each to < 10⁻⁶ (Richardson-corrected central differences; V is a quartic so the correction is exact up to rounding). | rank 6, single eigenvalue 8(1 − b₀²) — **held** if so |
| C quench, exact | **New analytic result derived before running (§3):** the G₂ × O(2)-invariants (A, C, D, B) = (|a|², |c|², ⟨a,c⟩, b₀²) close under the sphere-projected gradient flow and move on a straight ray, so the endpoint is closed-form: **b₀²_end = B₀ / (B₀ + √((1 − B₀)² − V₀))**, a function of the initial (b₀², V) only, independent of the integrator and of the time parametrisation. The quench number is therefore E_Haar[ B/(B + √((1−B)² − V)) ] — a 3-d integral. I seal its value in **[0.140, 0.150]** (crude estimate 2B/(1+B) at B = 1/15 gives 0.125 before Jensen; the on-record MC says 0.146 ± 0.001). If the quadrature gives 0.146 ± 0.001, "0.146" is exact and not an artefact. |  0.146 ± 0.003 |
| C quench, RK4 | Same 24 000 Haar seeds through renormalised Euler (h = 0.02, as flow_big) and RK4 (h = 0.02, 0.01, 0.005) on the same tangent field to T = 100: all four means within 0.002 of each other; RK4(h) − RK4(h/2) per seed scales as h⁴; per-seed agreement with the closed form < 10⁻⁶ for converged seeds; adaptive Dormand–Prince (rtol 10⁻⁹) on a 2000-seed subset agrees with RK4 h = 0.005 to < 10⁻⁷ per seed. Fraction of seeds not converged (V_end > 10⁻⁸) at T = 100 is < 1 % and lies at |b₀| > 0.97, so the stopping rule moves the mean by < 3·10⁻⁴. | 0.146 ± 0.003 — **held** if so |
| D verdict | Anneal (1/3, three independent routes) ≠ quench (0.146, two independent routes and a closed form). Prop 9 holds as a measure statement; **no crack** — unless one of the rows above fails. | — |

Sealed 2026-09-24 before the first `run-bounded` launch. Any later edit to this section would be a protocol violation.

