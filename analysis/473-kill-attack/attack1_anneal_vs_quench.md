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

---

## 1. Leg A — the anneal, analytically

### 1a. Tube / Laplace route (the one the driver asked for)

**Second-order expansion of V at a vacuum.** With A = |a|², C = |c|², D = ⟨a, c⟩: V = 4(AC − D²) = 4‖a ∧ c‖² (Gram determinant = squared area). A vacuum is (a, c) = r(cos θ u, sin θ u), u ∈ S⁶, r² = 1 − b₀². Perturb (δa, δc, δb₀). Since a ∧ c = 0 at the vacuum, δ(a ∧ c) = δa ∧ c + a ∧ δc = r(sin θ δa − cos θ δc) ∧ u to first order, so with w := sin θ δa − cos θ δc,

  V = 4 r² ‖w_⊥‖² + O(δ³),  w_⊥ = w − ⟨w, u⟩u,  i.e. D²V(v, v) = 8 r² ‖w_⊥‖².

**Tangent and normal spaces.** The tangent space of M at the vacuum (inside T S¹⁴, 8-dim) is spanned by ∂_θ = (−r sin θ u, r cos θ u, 0), ∂_{u_i} = (r cos θ e_i, r sin θ e_i, 0) (e_i ⊥ u, i = 1..6), ∂_{b₀} = (−(b₀/r) cos θ u, −(b₀/r) sin θ u, 1). On each of these w_⊥ = 0 (for ∂_θ, w = −r u ∥ u; for ∂_{u_i}, w = r(sin θ cos θ − cos θ sin θ) e_i = 0; for ∂_{b₀}, w ∥ u), so D²V annihilates T M. The 6-dim normal space is {n̂ = (sin θ n, −cos θ n, 0) : n ⊥ u}: it is orthogonal to all eight tangent vectors, unit-normalised when |n| = 1, and gives w = n, so

  **H_⊥ = 8 r² · I₆ = 8(1 − b₀²) I₆.**

Because V ≥ 0 vanishes on M, D²V at a vacuum is positive semi-definite; its kernel contains T M and its restriction to the normal space is positive definite (r > 0), so the kernel is exactly T M and there are no tangent–normal cross terms. Because M consists of global minima of V on all of ℝ¹⁶ (V ≥ 0 there too), the ambient gradient vanishes on M and the intrinsic Hessian of V|_{S¹⁴} equals the ambient Hessian restricted to T S¹⁴ (the second-fundamental-form term is multiplied by ∇V = 0). This matches PR #667's `hessQuad = 8(1−b₀²)‖Pv‖²` and transverse trace 48(1−b₀²), and is confirmed numerically to 5·10⁻¹⁴ in §2b.

**Laplace on a manifold with a minimum submanifold.** For a compact Riemannian manifold X (here S¹⁴, round metric), V ≥ 0 smooth with {V = 0} = M a submanifold of codimension k along which the normal Hessian is non-degenerate,

  ∫_X f e^{−βV} dvol_X = (2π/β)^{k/2} ∫_M f · det(H_⊥)^{−1/2} dvol_M · (1 + o(1)),

with H_⊥ in an orthonormal normal frame. Here k = 6 and det(H_⊥)^{−1/2} = (8r²)^{−3} = 8⁻³ (1 − b₀²)⁻³.

**Surface element of M in the round metric.** In the parametrisation x(θ, u, b₀) = (r cos θ u, r sin θ u, b₀), r = √(1 − b₀²), the three families of tangent vectors above are mutually orthogonal with |∂_θ|² = r², |∂_{u_i}|² = r², |∂_{b₀}|² = b₀²/r² + 1 = 1/r². So the induced metric is diag(r², r² I₆, r⁻²) and

  dvol_M = r · r⁶ · r⁻¹ dθ dΩ₆ db₀ = **(1 − b₀²)³ dθ db₀ dΩ_{S⁶}** = (1 − b₀²)³ dΩ_{S²} dΩ_{S⁶},

using that dθ db₀ is the round area element of the vacuum S² in (azimuth, height) coordinates (Archimedes). This is the driver's expected (α² + γ²)³ dΩ_{S²} dΩ_{S⁶}.

**Cancellation.** det(H_⊥)^{−1/2} dvol_M = 8⁻³ (1 − b₀²)⁻³ · (1 − b₀²)³ dθ db₀ dΩ₆ = 8⁻³ dθ db₀ dΩ₆. The β → ∞ Gibbs density on the vacuum S² is **exactly uniform in (θ, b₀)**, i.e. round-uniform on S², so

  **⟨b₀²⟩_anneal = ½ ∫₋₁¹ b₀² db₀ = 1/3 exactly.**

Every step checked; the cancellation does not fail. Two things the argument has to survive, both fine: (i) M is not smooth at the two poles r = 0 (its link there is (S¹ × S⁶)/ℤ₂, not S⁷), and H_⊥ → 0 there — but the limit density 8⁻³ dθ db₀ dΩ₆ is bounded, so the poles carry zero limiting mass, and the near-pole band r ≲ β^{−1/4} where the Gaussian approximation fails has S¹⁴-measure ∝ β^{−14/4} = β^{−3.5} against the bulk's β^{−3}: it is an O(β^{−1/2}) correction (this is the origin of the slow, from-below convergence seen at finite β — see §2a); (ii) the degenerate vacua a = 0 or c = 0 (θ ∈ {0, π/2} mod π) are ordinary points of M (the parametrisation is regular there), so nothing special happens.

### 1b. Independent route: reduce Haar on S¹⁴ to three invariants, then β → ∞

Write x = (a, b₀, c) with height coordinate b₀: dσ_{S¹⁴} = (1 − b₀²)⁶ db₀ dΩ₁₃ (general: (1 − z²)^{(n−2)/2} on Sⁿ). Put (a, c) = r ω, ω ∈ S¹³ ⊂ ℝ⁷ ⊕ ℝ⁷, ω = (√t p, √(1−t) q): under uniform ω, t = |â|² ~ Beta(7/2, 7/2), p, q independent uniform on S⁶, and cos φ = ⟨p, q⟩ has density ∝ sin⁵ φ on [0, π]. Then V = 4 r⁴ t(1 − t) sin² φ =: 4 r⁴ κ, and

  ⟨b₀²⟩_β = ∫ (1 − b₀²)⁶ b₀² I(β, (1 − b₀²)²) db₀ / ∫ (1 − b₀²)⁶ I(β, (1 − b₀²)²) db₀,
  I(β, x) = ∫₀¹ t^{5/2}(1 − t)^{5/2} J(4βx t(1 − t)) dt,  J(μ) = ∫₀^π sin⁵φ e^{−μ sin²φ} dφ = ∫₀¹ w²(1 − w)^{−1/2} e^{−μw} dw = B(3, ½) ₁F₁(3; 7/2; −μ).

As μ → ∞, J(μ) → 2/μ³ (both endpoints φ = 0, π contribute Γ(3)/(2μ³)); so I(β, x) → 2 (4βx)⁻³ ∫₀¹ (t(1 − t))^{5/2 − 3} dt = 2π/(4βx)³ = 2π/(64 β³ x³). With x = (1 − b₀²)², the b₀-density becomes (1 − b₀²)⁶ · (1 − b₀²)⁻⁶ · const = **const**: uniform in b₀, ⟨b₀²⟩ → 1/3. The θ-marginal in the same limit is ∝ t^{5/2}(1−t)^{5/2}/(t(1−t))³ dt = (t(1−t))^{−1/2} dt = 2 dθ (t = cos² θ): uniform in θ — the same S²-uniform statement as §1a, reached by a different split (r¹² vs r⁻¹² here, r⁶ vs r⁻⁶ there).

This route also gives the exact finite-β values by 3-d quadrature (`anneal_quadrature.py`, §2a), including the β⁻¹ᐟ² approach.

## 2. Leg A/B — the anneal, numerically

### 2a. Exact quadrature of the reduced integral (`anneal_quadrature.py` → `anneal_quadrature_out.txt`)

Composite Gauss–Legendre (32 nodes × 300 geometric panels per level) resolving the boundary layers t ~ 1/(βx) and 1 − b₀ ~ β⁻¹ᐟ². Self-checks: J(μ) against a reference quad to 10⁻⁹ over μ ∈ [0, 10⁶]; β = 0 gives 1/15 to 10 digits; the Laplace constant β³x³ I(β, x) → 2π/64 = 0.098175 is reproduced to 6 digits at β = 10³, 10⁵, 10⁷ for x = 1 and x = ¼ — this is the §1b limit "I → 2π/(64β³x³)" checked numerically, i.e. the cancellation of §1a/§1b seen directly.

| β | ⟨b₀²⟩_β exact | (1/3 − ⟨b₀²⟩_β)·√β | on record (`gibbs_check.py`, importance sampling) |
|---|---|---|---|
| 0 | 0.066667 | — | 1/15 |
| 5 | 0.121549 | 0.474 | 0.121 |
| 10 | 0.167532 | 0.524 | 0.167 |
| 40 | 0.247124 | 0.545 | 0.245 |
| 160 | 0.289832 | 0.550 | 0.290 ± 0.03 |
| 1000 | 0.315860 | 0.553 | — |
| 10⁴ | 0.327798 | 0.5535 | — |
| 10⁶ | 0.332779 | 0.5539 | — |
| 10⁷ | 0.333158 | 0.5539 | — |

Findings: (i) every on-record importance-sampling value is reproduced within its MC error; (ii) the approach to 1/3 is **exactly** of the form 1/3 − 0.5539·β⁻¹ᐟ² + o(β⁻¹ᐟ²) — the constant is flat to four digits from β = 10⁴ on — which is the near-pole (r ≲ β⁻¹ᐟ⁴) correction predicted in §1a, and nothing else; (iii) the b₀-density relative to b₀ = 0 is 1.0000 at b₀ = 0.3, 0.6, 0.9, 0.99 for β = 10⁶ (at β = 100 the b₀ = 0.9 point is still at 0.699 — the pole band is wide at small β). The limit is uniform in b₀ and ⟨b₀²⟩_∞ = 1/3, with no free constant left over.

Numerics failure caught and fixed (on record, not hidden): the first version used `scipy.integrate.quad` with algebraic end-point weights; it silently under-resolved the t-boundary layer for βx ≳ 10³ and returned I(β, x) 1–2 % low (visible as β³x³I → 0.0961 instead of 0.0982 and as a d·√β that *fell* at large β). Caught by the Laplace-constant check, replaced by the panelled Gauss–Legendre; the β ≤ 320 values were unaffected to 6 digits. The aborted first RK4 output (`quench_rk4_out_aborted_v1.txt`, Euler line only) is likewise kept.

### 2b. Hessian isotropy at 50 random vacua (`hessian_isotropy.py` → `hessian_isotropy_out.txt`)

Random b₀ ∈ (−0.95, 0.95) plus b₀ = 0, 0.99, −0.999; random θ and u ∈ S⁶; full 14 × 14 Hessian on T_x S¹⁴ by Richardson-corrected central differences (exact for a quartic). Result: **8 eigenvalues zero to 4.9·10⁻¹⁴, 6 eigenvalues equal to 8(1 − b₀²) to 4.9·10⁻¹⁴**, |∇V| ≤ 2.5·10⁻¹⁶ at every vacuum. Rank 6, single transverse eigenvalue — PR #667's `hessQuad` confirmed far beyond the 10⁻⁶ seal.

### 2c. MCMC anneal on S¹⁴ with the full sedenion potential (`anneal_mcmc.py` → `anneal_mcmc_out.txt`)

Random-walk Metropolis, 8192 independent chains, symmetric proposal x′ = normalise(x + εξ), ε adapted to acceptance 0.30 during burn-in, `flowlib.potential` (no reduction to invariants). Standard error from the spread of the 8192 independent chain means. Two initial ensembles: **Haar**, and **pole** (all chains within 0.045 of +ℓ, ⟨b₀²⟩_init = 0.998 — the worst start for mixing along the b₀ direction of M).

| β | ε | exact (quadrature, §2a) | MCMC, Haar init | MCMC, pole init | halves (pole): first / second |
|---|---|---|---|---|---|
| 10 | 0.20 | 0.167532 | 0.1676 ± 0.0002 | 0.1676 ± 0.0002 | 0.1675 / 0.1677 |
| 30 | 0.081 | 0.234149 | 0.2342 ± 0.0005 | 0.2338 ± 0.0005 | 0.2342 / 0.2334 |
| 100 | 0.042 | 0.278425 | 0.2777 ± 0.0010 | 0.2783 ± 0.0011 | 0.2774 / 0.2793 |
| 300 | 0.024 | 0.301502 | 0.3037 ± 0.0017 | 0.3001 ± 0.0017 | 0.3006 / 0.2995 |
| 1000 | 0.013 | 0.315860 | 0.3143 ± 0.0023 | 0.3150 ± 0.0023 | 0.3134 / 0.3165 |

All ten MCMC values lie within 1.3σ of the exact quadrature; the two initial ensembles agree with each other within 1.5σ at every β (the pole start forgets ⟨b₀²⟩ = 0.998 completely); the sequence is monotone toward 1/3 at the exact β⁻¹ᐟ² rate. Wall: 1630 s (Haar), 1083 s (pole), each under a 2 GB / 3600 s cap.

## 3. Leg C — the quench

### 3a. The quench endpoint has a closed form (derived before the runs)

The sphere-projected gradient flow ẋ = −(∇V − ⟨∇V, x⟩x) with V = 4(AC − D²), A = |a|², C = |c|², D = ⟨a, c⟩, B = b₀²:
∂V/∂a = 8(Ca − Dc), ∂V/∂c = 8(Ac − Da), ∂V/∂b₀ = 0, and ⟨∇V, x⟩ = 16(AC − D²) = 4V (degree-4 homogeneity). Hence

  ȧ = −8(Ca − Dc) + 4V a,  ċ = −8(Ac − Da) + 4V c,  ḃ₀ = 4V b₀,

and the G₂ × O(2)-invariants close:

  Ȧ = 2⟨a, ȧ⟩ = −4V + 8VA = 4V(2A − 1),  Ċ = 4V(2C − 1),  Ḋ = 8VD,  Ḃ = 8VB   (check: Ȧ + Ċ + Ḃ = 8V(A + C + B − 1) = 0).

In the reparametrised time dτ = 4V dt this is **linear**: A′ = 2A − 1, C′ = 2C − 1, D′ = 2D, B′ = 2B, so with λ = e^{2τ} ∈ [1, ∞)

  (A − ½, C − ½, D, B)(λ) = λ · (A₀ − ½, C₀ − ½, D₀, B₀):

the invariants move on a **straight ray** from the initial point, away from (½, ½, 0, 0), until V = 0, i.e. AC = D². Substituting, the stopping condition is the quadratic q(λ) = (A₀ − ½)(C₀ − ½)λ² − ... which, using A₀ + C₀ = 1 − B₀ and V₀ = 4(A₀C₀ − D₀²), collapses to

  (V₀ + 2B₀ − 1) λ² − 2B₀ λ + 1 = 0,  λ* = 1/(B₀ + √((1 − B₀)² − V₀))

(the smaller positive root, ≥ 1 since V₀ ≤ (1 − B₀)²; q(1) = V₀/4 > 0 so the flow reaches this root first). Therefore

  **b₀²_end = B₀ λ* = b₀² / ( b₀² + √((1 − b₀²)² − V₀) ),**

a function of the initial (b₀², V) only: the endpoint is independent of the integrator, of the time parametrisation, and of the stopping time (as long as the flow is followed to V = 0). Sanity: V₀ = 0 ⇒ unchanged; V₀ = (1 − B₀)² (a ⊥ c, |a| = |c| — the symmetric configuration) ⇒ b₀² → 1 (flows to the pole ±ℓ, cf. Prop 16); ḃ₀ = 4Vb₀ says |b₀| only grows (ln(b₀_end/b₀_init) = 4∫V dt, the "b₀ growth ratio" printed by `flow_big.py`).

With the Haar reduction of §1b (V₀ = 4(1 − B₀)² κ, κ = t(1 − t) sin²φ), the quench number is the 3-d integral

  **⟨b₀²⟩_quench = E_Haar[ B / (B + (1 − B)√(1 − 4κ)) ],**  B ~ (1 − b₀²)⁶ db₀, t ~ Beta(7/2, 7/2), φ ~ sin⁵φ dφ.

This is what `quench_exact.py` evaluates (quadrature, and 10⁷ Haar points using `flowlib.potential`, no reduction). The integrators in `quench_rk4.py` then have an exact per-seed target to be compared against.

### 3b. The exact quench number (`quench_exact.py`, output `quench_exact_out.txt`)

| Method | ⟨b₀²⟩_quench | Notes |
|---|---|---|
| 3-d quadrature of E_Haar[B/(B + (1−B)√(1−4κ))] | **0.141587** | 25 s; β = 0 check ∫ b₀² = 1/15 to 7 digits |
| 10⁷ Haar points, V from `flowlib.potential` (full sedenion commutator, no reduction), closed form per point | **0.14162 ± 0.00005** | max |V − 4(AC − D²)| = 9·10⁻¹⁶ over 10⁷ points; endpoint quantiles (10/25/50/75/90 %) = 0.0027 / 0.0174 / 0.076 / 0.208 / 0.386 |
| on record (renormalised Euler, h = 0.02, T = 100) | 0.1462 ± 0.0011 (#629), 0.1454 ± 0.0011, 0.1436 ± 0.0011 | three independent seed streams; their mean 0.1451 ± 0.0006 |

The exact value **0.1416** sits 3σ–4σ below the on-record Euler numbers taken individually and 5.5σ below their pooled mean. The integrator ladder in §3c decides whether that gap is the h = 0.02 Euler bias (sealed expectation: |Euler − RK4| < 0.002 — this row will test that seal).

### 3c. Integrator ladder on identical seeds (`quench_rk4.py` → `quench_rk4_out.txt`)

Seeds: 24 000 Haar states, `default_rng(20260924)` (a stream distinct from every on-record run; ⟨b₀²⟩_init = 0.06768 vs 1/15 = 0.06667, a 1σ fluctuation), all integrators started from the **same** states so that per-seed differences are integrator error only. Closed-form gradient checked against `flowlib.gradV_exact` to 2·10⁻¹⁶; field tangency 2·10⁻¹⁵.

| Integrator | seeds | ⟨b₀²⟩_end | vs closed form (paired): mean / max per seed | all seeds converged? |
|---|---|---|---|---|
| closed form b₀²/(b₀² + √((1−b₀²)² − V₀)) | 24 000 | 0.14215 ± 0.00108 | — | — |
| **renormalised Euler h = 0.02, T = 100** (flow_big's scheme) | 24 000 | **0.14525 ± 0.00110** | **+3.10·10⁻³** / 4.8·10⁻² | yes (max V 5·10⁻¹⁸) |
| `flowlib.step` h = 0.02 (the on-record integrator itself) | 1 000 | 0.14975 ± 0.0056 | +3.16·10⁻³ / 4.2·10⁻²; identical to my Euler to 3.9·10⁻¹⁵ | yes |
| RK4 + renormalise h = 0.02 | 24 000 | **0.14215 ± 0.00108** | +1.0·10⁻⁷ / 4.0·10⁻⁶ | yes (max V 9·10⁻¹⁹) |
| RK4 h = 0.01 | 6 000 | (subset) | +6.5·10⁻⁹ / 2.3·10⁻⁷ | yes |
| RK4 h = 0.005 | 6 000 | (subset) | +4.1·10⁻¹⁰ / 1.5·10⁻⁸ | yes |
| Dormand–Prince 5(4), rtol 10⁻⁹ (544 steps, 10 rejected) | 2 000 | (subset) | −5·10⁻¹³ / 3.9·10⁻¹¹ | yes (max V 9·10⁻²¹) |
| RK4 continued T = 100 → 400 from the DP45 endpoints | 2 000 | shift **+1.8·10⁻¹⁹** | — | max V 7·10⁻³¹ |

Richardson on the 6000-seed subset: mean|RK4(0.02) − RK4(0.01)| = 9.5·10⁻⁸, mean|RK4(0.01) − RK4(0.005)| = 6.1·10⁻⁹, **ratio 15.7** (h⁴ → 16). Paired Euler(0.02) − RK4(0.005): **+3.12·10⁻³ ± 0.05·10⁻³**, max per seed 4.2·10⁻².

Reading:
1. **The h → 0 quench limit is the closed form of §3a, to 10⁻¹¹ per seed**, by three integrators of different order (RK4 ladder with the right h⁴ scaling, adaptive DP45). The stopping rule is irrelevant (T = 100 → 400 changes nothing at 10⁻¹⁹; every seed is at V < 10⁻¹⁸ by T = 100, including the near-pole ones — the "unconverged fraction" of the seal is 0.0000, not < 1 %).
2. **Renormalised Euler at h = 0.02 carries a systematic bias of +0.0031 in ⟨b₀²⟩** (a 130σ paired effect; per-seed up to +0.048, always upward since Euler over-shoots along the ray and ḃ₀ = 4Vb₀ only grows |b₀|). This is exactly the gap between the on-record numbers (0.1462, 0.1454, 0.1436; pooled 0.1451 ± 0.0006) and the exact 0.1416 (0.1416 + 0.0031 = 0.1447). The on-record integrator (`flowlib.step`, and `flow_big.py`'s identical scheme) is the source — verified by running `flowlib.step` itself on the same seeds.
3. Hence: **"0.146" is 0.1416 + a first-order discretisation artefact of +0.003.** The quench number, correctly stated, is **0.1416 (exact: E_Haar[B/(B + (1−B)√(1−4κ))] = 0.141587)**, with the on-record MC scatter (±0.001) on top of that bias.

---

## 4. Verdict

| Question | Answer | Evidence |
|---|---|---|
| Does the β → ∞ Gibbs anneal give ⟨b₀²⟩ = 1/3? | **Yes, exactly.** | §1a tube/Laplace (Hessian 8r²·I₆ × surface element r⁶ cancel); §1b independent reduction to (b₀, t, φ); §2a exact quadrature → 1/3 − 0.5539 β⁻¹ᐟ², 0.333158 at β = 10⁷; §2c MCMC at 5 β's, 2 inits, all within 1.3σ; §2b Hessian isotropy to 5·10⁻¹⁴ |
| Does the gradient-flow quench give 0.146? | **No — it gives 0.1416; "0.146" = 0.1416 + a +0.003 Euler h = 0.02 artefact.** | §3a closed form b₀²/(b₀² + √((1−b₀²)² − V₀)); §3b quadrature 0.141587 and 10⁷-point MC 0.14162 ± 0.00005; §3c RK4/DP45 reproduce the closed form to 10⁻⁸–10⁻¹¹ per seed, Euler/`flowlib.step` are +0.0031 ± 0.0000(5) above it on the same seeds |
| Do the two numbers coincide? | **No.** 1/3 vs 0.1416 — the gap is 0.19, about 60× the size of the artefact found. | all of the above |
| Is Prop 9 cracked? | **Not as a measure statement; its quench number is wrong in the third decimal.** Two algebra-compatible rules on the same N-measure give two different, now *exactly known* numbers: anneal 1/3, quench 0.141587. | — |

**Driver's sealed positions:** (A) "factors cancel, uniform on S², 1/3 exactly" — **held**, and now with a second derivation and an exact finite-β law. (B) "monotone toward 1/3" — **held**. (B) "Hessian rank 6, single eigenvalue 8(1 − b₀²)" — **held** (to 5·10⁻¹⁴). (C) "0.146 ± 0.003" — **missed by 0.0044**: the exact quench value is 0.1416, and the on-record 0.146 is 0.1416 + 0.003 (renormalised-Euler bias at h = 0.02) + MC scatter.

**My own seals** (§0): all held except two, recorded honestly: "|Euler − RK4| < 0.002" **failed** (it is 0.0031); "unconverged fraction < 1 %" was too pessimistic (it is 0). The sealed range for the exact quench value [0.140, 0.150] held (0.1416).

**Findings beyond the target (numerical leg only; none is a theory claim):**
1. The quench endpoint is closed-form: b₀²_end = b₀²/(b₀² + √((1 − b₀²)² − V₀)) — the invariants move on a straight ray under the flow. Hence ⟨b₀²⟩_quench = E_Haar[B/(B + (1 − B)√(1 − 4κ))] = **0.141587**, no ODE needed. This also makes Prop 9's two numbers *both* integrals over the same 3-dim invariant space with the same Haar weights (1 − b₀²)⁶ · t^{5/2}(1−t)^{5/2} · sin⁵φ — one with weight → uniform-on-S², the other with the ray map — which is a sharper form of "same measure, two rules, two numbers".
2. The finite-β anneal obeys ⟨b₀²⟩_β = 1/3 − 0.5539 β⁻¹ᐟ² + o(β⁻¹ᐟ²) (the near-pole band r ≲ β⁻¹ᐟ⁴), so any finite-β "anneal" number quoted without this correction is not the limit.
3. Corrections owed to the record (for the driver, not made here — nothing outside `analysis/473-kill-attack/` was touched): Prop 9's "quench 0.146" → "quench 0.1416 (exact 0.141587; the on-record 0.146 carried a +0.003 renormalised-Euler h = 0.02 bias)"; the same 0.146/0.1462/0.1454/0.1436 numbers appear in Props 12, 14, 16 and the one-line result. `gibbs_check.py`'s "≈ 1/3" can be upgraded to "= 1/3 exactly, approach 1/3 − 0.554/√β".

## 5. Resource log (every compute run under `run-bounded`; ledger `~/.federation-watcher/run-bounded.ledger`)

| Run | Estimate (RAM / wall) | Cap | Actual wall | Exit |
|---|---|---|---|---|
| `hessian_isotropy.py` | <200 MB / ~5 s | 1G / 300 s | ~5 s | 0 |
| `anneal_quadrature.py` v1 (scipy quad; superseded, result kept in §2a note) | <200 MB / 1–5 min | 1G / 1800 s | ~3 min | 0 |
| `anneal_quadrature.py` v2 (panelled GL; the recorded one) | <200 MB / ~5 min | 1G / 900 s | ~8 min | 0 |
| `anneal_quadrature` at the five MCMC β's | <200 MB / <5 min | 1G / 900 s | ~2 min | 0 |
| `quench_exact.py` | <1 GB / ~2 min | 2G / 900 s | ~1.5 min | 0 |
| `quench_rk4.py` v1 (aborted by me after the Euler line — the 24 000-seed h = 0.005 RK4 + T = 400 continuation would have exceeded the cap; output kept as `quench_rk4_out_aborted_v1.txt`) | <500 MB / ~21 min | 2G / 3600 s | killed at ~6 min | 144 (SIGTERM by me) |
| `quench_rk4.py` v2 | <500 MB / ~40 min | 2G / 5400 s | ~45 min | 0 |
| `anneal_mcmc.py haar` | <300 MB / ~22 min | 2G / 3600 s | 1630 s | 0 |
| `anneal_mcmc.py pole` | <300 MB / ~22 min | 2G / 3600 s | 1083 s | 0 |

No run approached its memory cap; none timed out. Files: `attack1_anneal_vs_quench.md` (this report), `flowlib.py` (verbatim copy from `research/635-analysis-records`), `anneal_quadrature.py`, `hessian_isotropy.py`, `anneal_mcmc.py`, `quench_exact.py`, `quench_rk4.py`, and the raw outputs `*_out.txt`, `anneal_quadrature_mcmc_betas.txt`, `quench_rk4_out_aborted_v1.txt`.
