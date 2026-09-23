import numpy as np
from fast import *

rng = np.random.default_rng(77)
n = 2000
S = rng.normal(size=(n, 16))
S[:, 0] = 0
S /= np.linalg.norm(S, axis=1, keepdims=True)
for k in range(6000):
    S = S + 0.02 * F(S)
    S[:, 0] = 0
    S /= np.linalg.norm(S, axis=1, keepdims=True)
v = V(S)
print("n=%d quench, 6000 steps h=0.02:" % n)
for thr in [1e-4, 1e-6, 1e-8]:
    print("   frac V<%.0e : %.4f" % (thr, (v < thr).mean()))
print(
    "   V quantiles:",
    np.round(np.quantile(v, [0, 0.01, 0.05, 0.25, 0.5, 0.75, 0.95, 0.99, 1]), 6),
)
nf = np.linalg.norm(F(S), axis=1)
print("   ||F|| quantiles:", np.round(np.quantile(nf, [0, 0.5, 0.95, 1]), 8))
stuck = v > 1e-6
print(
    "   non-crystal endpoints: %d (%.3f) ; their V mean %.4f, ||F|| max %.2e"
    % (
        stuck.sum(),
        stuck.mean(),
        v[stuck].mean() if stuck.any() else 0,
        nf[stuck].max() if stuck.any() else 0,
    )
)
