"""TEST 2 — link 4 (the bridge): is the induced hosted frame continuous along the flow, and does the
trajectory ever approach a POLE (where the hosted algebra collapses ℍ → ℂ and matter cannot be hosted)?
Also: the renormalised step's non-merging (finite-time injectivity of what the scripts run).
"""

import numpy as np, sys

sys.path.insert(0, ".")
from flowlib import *

rng = np.random.default_rng(639)
n = 500
h = 0.01
T = 3000
s = random_states(n, rng)
u, alpha = direction_u(s)
maxjump = np.zeros(n)
minnp = nonpole(s).copy()
minalpha = alpha.copy()
# twin seeds for the merging check
d0 = 1e-6
s2 = s + d0 * rng.normal(size=s.shape)
s2[:, 0] = 0
s2 /= np.linalg.norm(s2, axis=1, keepdims=True)
dist0 = np.linalg.norm(s - s2, axis=1)
for k in range(T):
    s = step(s, h)
    s2 = step(s2, h)
    u2, alpha2 = direction_u(s)
    ang = np.arccos(np.clip(np.sum(u * u2, axis=1), -1, 1))
    maxjump = np.maximum(maxjump, ang)
    u = u2
    minnp = np.minimum(minnp, nonpole(s))
    minalpha = np.minimum(minalpha, alpha2)
dist = np.linalg.norm(s - s2, axis=1)
print(f"seeds {n}, h={h}, T={T*h}")
print(
    f"(a) pole approach: min_t (1-b0^2) over all seeds = {minnp.min():.4f}; seeds with min < 0.05: {(minnp<0.05).mean():.4f}; endpoints with b0^2 > 0.99 (pole crystals, hosted algebra = C): {(b0(s)**2>0.99).mean():.4f}"
)
print(
    f"(b) direction u(t) continuity: max angular change per step = {maxjump.max():.4f} rad (h={h}; a jump > 0.5 rad would be a frame discontinuity); 95th pct {np.percentile(maxjump,95):.4f}"
)
print(
    f"(c) min_t |cdLo s| (u well-defined iff > 0): {minalpha.min():.4f}; seeds with min < 1e-3: {(minalpha<1e-3).mean():.4f}"
)
print(
    f"(d) hosted algebra at endpoint: quaternion (non-pole) fraction {(b0(s)**2<0.99).mean():.4f}"
)
print(
    f"(e) renormalised-step non-merging: twin distance end/start: min {np.min(dist/dist0):.3e}, median {np.median(dist/dist0):.3e}; any merged (dist < 1e-14): {(dist<1e-14).sum()}"
)
