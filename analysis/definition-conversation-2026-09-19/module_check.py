"""Round-8 runner verification of the confirmer's datum-free reading:
is H_s^perp (12-dim) a LEFT H_s-module, i.e. H_s^perp = H_s^3 ?"""

import numpy as np, sys

sys.path.insert(
    0,
    "/home/prime/Documents/QBP/.claude/worktrees/probe-encode-bundle/analysis/473-dirac-probe",
)
from dirac_probe import cd_mul

N = 16
e = lambda i: np.eye(N)[i]
ELL = e(8)


def orth(M, tol=1e-9):
    U, S, Vt = np.linalg.svd(np.array(M, float), full_matrices=False)
    r = int((S > tol * max(1, S[0])).sum())
    return Vt[:r]


rng = np.random.default_rng(808)
worst = 0.0
dims = set()
free = 0
for _ in range(10):
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    U = np.zeros(N)
    U[:8] = u
    H = orth([e(0), ELL, U, cd_mul(ELL, U)])
    P = np.eye(N) - H.T @ H  # projector onto H^perp
    B = orth(P)  # basis of H_s^perp
    dims.add(B.shape[0])
    for g in [U, ELL, cd_mul(U, ELL), cd_mul(ELL, U)]:
        for w in B:
            gw = cd_mul(g, w)
            worst = max(worst, np.linalg.norm(gw - P @ gw))
    # rank-1 free check: H_s . w spans 4 dims for random w in H^perp
    w = B[rng.integers(0, B.shape[0])]
    L = orth([cd_mul(h, w) for h in [e(0), ELL, U, cd_mul(ELL, U)]])
    if L.shape[0] == 4:
        free += 1
print("dim H_s^perp:", dims, "(expect {12} = 3 x 4)")
print(
    "max ||g.w - proj_perp(g.w)|| over g in {U, ell, U*ell, ell*U}, 10 crystals: %.2e"
    % worst
)
print("H_s . w is 4-dimensional (free rank-1) for a random w: %d/10" % free)
