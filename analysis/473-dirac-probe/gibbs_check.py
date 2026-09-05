"""#473 AC1 v0.3, Prop 9 (corrected after PR #631 review) — quench ≠ Gibbs β → ∞.

Same N-Haar measure on S¹⁴, two algebra-compatible rules, two different vacuum statistics:
  * gradient-flow QUENCH (flow_big.py / s3_check.py):  ⟨b₀²⟩ = 0.146
  * Gibbs ANNEAL μ_β ∝ e^{−βV}·Haar, β → ∞:            ⟨b₀²⟩ → ≈ 1/3
The Laplace argument (Red Team, Gemini re-derived): near a vacuum at radius r = √(1 − b₀²) the
transverse Hessian of V is ∝ r² on a 6-dimensional normal space, so the Laplace weight is
(det H⊥)^{-1/2} ∝ r⁻⁶, while the vacuum manifold's surface element in (b₀, θ, u ∈ S⁶) is ∝ r⁶;
the product is constant in b₀, so the β → ∞ limit density is uniform in b₀ and ⟨b₀²⟩ → 1/3.

This script importance-samples the Gibbs family at increasing β (chunked Haar sampling,
weights e^{−β(V − V_min)}) and reports ⟨b₀²⟩_β with the effective sample size, to show the
monotone climb away from the quench's 0.146 toward 1/3.  Numerical flashlight only — the
Laplace limit is NOT formalised (it would need a Mathlib measure-theory argument on the
vacuum manifold; out of scope for #631).
"""

import numpy as np

exec(open("flow_big.py").read().split("# --- FD check")[0])  # omul, V

rng = np.random.default_rng(9)
NTOT, CHUNK = 4_000_000, 250_000
betas = [0, 2, 5, 10, 20, 40, 80, 160]
acc = {b: np.zeros(3) for b in betas}  # Σw, Σw·b0², Σw²
for _ in range(NTOT // CHUNK):
    s = rng.normal(size=(CHUNK, 15))
    s /= np.linalg.norm(s, axis=1, keepdims=True)
    a = np.concatenate([np.zeros((CHUNK, 1)), s[:, :7]], 1)
    b = s[:, 7:]
    v = V(a, b)
    b0sq = b[:, 0] ** 2
    for beta in betas:
        w = np.exp(-beta * v)  # V ≥ 0 with min 0, so no shift needed
        acc[beta] += [w.sum(), (w * b0sq).sum(), (w * w).sum()]
print("Gibbs μ_β ∝ e^{-βV}·Haar on S¹⁴, %d Haar points:" % NTOT)
print("  β        <b0²>_β     ESS")
for beta in betas:
    sw, swb, sww = acc[beta]
    print("  %5d    %.4f    %9.0f" % (beta, swb / sw, sw * sw / sww))
print(
    "  β=0 exact 1/15 = %.4f;  quench (flow) 0.146;  β→∞ Laplace ≈ 1/3 = 0.3333"
    % (1 / 15)
)
