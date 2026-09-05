"""#473 AC1 v0.3, Prop 7′ — what the Cayley–Dickson norm does and does not lose at dim 16.

Committed form of the "one-liners" cited in docs/foundations/473-ac1-first-link-2026-09-04.md
(PR #631 Red Team finding 7: the quoted "0.891" was a single random draw).

  (1) positive-definiteness survives every doubling:  x x̄ = (N(x), 0, …, 0) with N(x) = Σ xᵢ²
      at dims 8 and 16 (exact to rounding);
  (2) what breaks at dim 16 is MULTIPLICATIVITY: the ratio N(xy) / (N(x) N(y)) is identically 1
      at dim 8 and a random variable at dim 16 — report mean / std / min / max over Haar pairs.
Numerical flashlight only; the Lean statement of (1) is `NormForm.N_eq_zero_iff` and of the
dim-8 half of (2) `NormForm.octonion_norm_form_composition`; the dim-16 failure is
`Breakdown.sedenion_norm_not_multiplicative`.
"""

import numpy as np

exec(open("dirac_probe.py").read().split("def spec")[0])  # cd_mul, conj, basis

rng = np.random.default_rng(473)
NPAIRS = 2000


def N(x):
    return (x * x).sum()


for dim in (8, 16):
    xs = rng.normal(size=(NPAIRS, dim))
    ys = rng.normal(size=(NPAIRS, dim))
    # (1) x x̄ = (N, 0, ..., 0)
    pd_res = max(
        np.abs(cd_mul(x, conj(x)) - np.eye(dim)[0] * N(x)).max() for x in xs[:200]
    )
    # (2) multiplicativity ratio
    ratio = np.array([N(cd_mul(x, y)) / (N(x) * N(y)) for x, y in zip(xs, ys)])
    print(
        f"dim {dim:2d}: |x x̄ − (N(x),0,…)|_max = {pd_res:.1e}   "
        f"N(xy)/(N(x)N(y)) over {NPAIRS} Haar pairs: mean {ratio.mean():.4f}  "
        f"std {ratio.std():.4f}  min {ratio.min():.3f}  max {ratio.max():.3f}"
    )
