"""ROUND 6 verification of Gemini's parametrisation claim:
(1) O'_v = O'_{uv}?  and more generally O'_{a v + b (uv)} = O'_v  (=> family = C_u-lines in u^perp => CP^2)
(2) distinct C_u-lines give distinct subalgebras (so the family is exactly CP^2, 4 real dims)
(3) is the whole family rho-invariant (re-confirm) and does it contain H_s
"""

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


def inter(A, B):
    return A.shape[0] + B.shape[0] - orth(np.vstack([A, B])).shape[0]


def lift(x8):
    v = np.zeros(N)
    v[:8] = x8
    return v


def Ov(u, v):
    # H'_v = span{1,u,v,uv} in O_low, then double by ell
    U, V = lift(u), lift(v)
    H = [e(0), U, V, cd_mul(U, V)]
    B = H + [cd_mul(h, ELL) for h in H]
    return orth(B)


rng = np.random.default_rng(41)
same = 0
diff = 0
rhoinv = 0
contains = 0
# rho
c, s = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)
R = np.zeros((N, N))
R[0, 0] = 1
R[8, 8] = 1
for k in range(1, 8):
    R[k, k] = c
    R[k + 8, k] = s
    R[k, k + 8] = -s
    R[k + 8, k + 8] = c
for k in range(1, 8):
    if cd_mul(e(k), e(8))[k + 8] < 0:
        R[k + 8, k] = -s
        R[k, k + 8] = s
for _ in range(20):
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    v = rng.normal(size=8)
    v[0] = 0
    v -= (v @ u) * u
    v /= np.linalg.norm(v)
    A = Ov(u, v)
    # (1) C_u-line: a v + b (uv)
    uv = cd_mul(lift(u), lift(v))[:8]
    a, b = rng.normal(size=2)
    w = a * v + b * uv
    w /= np.linalg.norm(w)
    if inter(A, Ov(u, w)) == 8:
        same += 1
    # (2) a random other v'
    v2 = rng.normal(size=8)
    v2[0] = 0
    v2 -= (v2 @ u) * u
    v2 -= (v2 @ v) * v
    v2 -= (v2 @ uv) * uv
    v2 /= np.linalg.norm(v2)
    if inter(A, Ov(u, v2)) < 8:
        diff += 1
    # (3) rho-invariance + contains H_s
    Ar = orth([R @ x for x in A])
    if inter(A, Ar) == 8:
        rhoinv += 1
    H = orth([e(0), ELL, lift(u), cd_mul(ELL, lift(u))])
    if inter(A, H) == 4:
        contains += 1
print("O'_{a v + b (uv)} == O'_v :", same, "/20")
print("O'_{v2} != O'_v for v2 off the C_u-line:", diff, "/20")
print("rho(O'_v) == O'_v :", rhoinv, "/20;   H_s subset O'_v :", contains, "/20")
