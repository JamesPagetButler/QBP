"""RUNNER-SIDE CHECK for round 5:
(1) verify Gemini's closed form V = 4(|a|^2 |Im b|^2 - <a, Im b>^2);
(2) does rho fix any crystal?  (if yes, a canonical *assignment* s -> O'(s) must give a
    rho-invariant octonion subalgebra at that s, which is the only place Gemini's
    non-existence argument can bite);
(3) is H_s rho-invariant (setwise) for a rho-fixed crystal?
(4) search: is there an 8-dim rho-invariant subalgebra containing H_s?
"""

import numpy as np, sys

sys.path.insert(
    0,
    "/home/prime/Documents/QBP/.claude/worktrees/probe-encode-bundle/analysis/473-dirac-probe",
)
from dirac_probe import cd_mul

N = 16


def V(s):
    a = np.r_[s[:8], np.zeros(8)]
    b = np.r_[s[8:], np.zeros(8)]
    return float(np.sum((cd_mul(a, b)[:8] - cd_mul(b, a)[:8]) ** 2))


def Vform(s):
    a = s[:8].copy()
    b = s[8:].copy()
    imb = b.copy()
    imb[0] = 0.0
    return 4 * (a @ a * (imb @ imb) - (a @ imb) ** 2)


rng = np.random.default_rng(5)
worst = 0
for _ in range(200):
    s = rng.normal(size=N)
    s[0] = 0
    s /= np.linalg.norm(s)
    worst = max(worst, abs(V(s) - Vform(s)))
print("(1) max |V - 4(|a|^2|Imb|^2 - <a,Imb>^2)| over 200 random states: %.2e" % worst)

# rho matrix (same construction as p2_cell_torsor_check.py)
c, sn = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)
R = np.zeros((N, N))
R[0, 0] = 1
R[8, 8] = 1
e = lambda i: np.eye(N)[i]
for k in range(1, 8):
    R[k, k] = c
    R[k + 8, k] = sn
    R[k, k + 8] = -sn
    R[k + 8, k + 8] = c
for k in range(1, 8):
    prod = cd_mul(e(k), e(8))
    if prod[k + 8] < 0:
        R[k + 8, k] = -sn
        R[k, k + 8] = sn
rho = lambda x: R @ x
# check automorphism
w = max(
    np.linalg.norm(rho(cd_mul(x, y)) - cd_mul(rho(x), rho(y)))
    for x, y in [(rng.normal(size=N), rng.normal(size=N)) for _ in range(50)]
)
print(
    "   rho automorphism residual %.1e ; order3 %.1e"
    % (w, np.linalg.norm(np.linalg.matrix_power(R, 3) - np.eye(N)))
)
# (2) fixed states of rho on the imaginary sphere
ev, evec = np.linalg.eig(R)
fixed = [evec[:, i].real for i in range(N) if abs(ev[i] - 1) < 1e-9]
Fx = np.array(fixed)
Fx = Fx[:, :] if Fx.ndim == 2 else Fx
print(
    "(2) dim of rho-fixed subspace of S (incl. 1):",
    np.linalg.matrix_rank(Fx, tol=1e-9),
    "-> spanned by coords",
    [int(np.argmax(abs(v))) for v in Fx],
)
# imaginary fixed states: only multiples of ell?
imfix = [v for v in Fx if abs(v[0]) < 1e-9]
print("   imaginary rho-fixed directions:", len(imfix), "(ell only if 1)")
pole = np.zeros(N)
pole[8] = 1.0
print(
    "   pole is a crystal:",
    V(pole) < 1e-20,
    "; rho(pole)=pole:",
    np.allclose(rho(pole), pole),
)


# (3) generic crystal: is H_s rho-invariant setwise?
def orth(M, tol=1e-9):
    U, S, Vt = np.linalg.svd(np.array(M, float), full_matrices=False)
    r = int((S > tol * max(1, S[0])).sum())
    return Vt[:r]


def inter_dim(A, B):
    return A.shape[0] + B.shape[0] - orth(np.vstack([A, B])).shape[0]


u = rng.normal(size=8)
u[0] = 0
u /= np.linalg.norm(u)
p = rng.normal(size=3)
p /= np.linalg.norm(p)
s = np.zeros(N)
s[:8] = p[0] * u
s[8] = p[2]
s[8:] += p[1] * u
assert V(s) < 1e-20
ul = np.zeros(N)
ul[:8] = u
H = orth([e(0), e(8), ul, cd_mul(e(8), ul)])
Hr = orth([rho(v) for v in H])
print(
    "(3) generic crystal: dim(H_s)=%d, dim(H_s ∩ rho H_s)=%d, rho(s)=s? %s"
    % (H.shape[0], inter_dim(H, Hr), np.allclose(rho(s), s))
)
# (4) at the pole (the only rho-fixed crystal): H_pole = span{1, ell}; is there a rho-invariant
#     octonion subalgebra containing it?
low = np.eye(N)[:8]
print("(4) rho-invariance of O_low:", inter_dim(orth(low), orth([rho(v) for v in low])))
# rho-invariant subspaces: {1, ell} + sums of the 2-planes (e_k, e_k ell); test closure of a few triples
import itertools

found = []
for trip in itertools.combinations(range(1, 8), 3):
    B = [e(0), e(8)]
    for k in trip:
        B += [e(k), e(k + 8)]
    Bo = orth(B)
    prods = [cd_mul(x, y) for x in Bo for y in Bo]
    closed = orth(np.vstack([Bo, np.array(prods)])).shape[0] == Bo.shape[0]
    if closed:
        found.append(trip)
print(
    "   rho-invariant 8-dim candidates {1,ell}+3 planes that are CLOSED under multiplication:",
    found if found else "NONE",
    "(out of %d triples)" % len(list(itertools.combinations(range(1, 8), 3))),
)
