import numpy as np, sys, itertools

sys.path.insert(
    0,
    "/home/prime/Documents/QBP/.claude/worktrees/probe-encode-bundle/analysis/473-dirac-probe",
)
from dirac_probe import cd_mul

N = 16
e = lambda i: np.eye(N)[i]
rng = np.random.default_rng(3)


def basis(trip):
    B = [e(0), e(8)]
    for k in trip:
        B += [e(k), e(k + 8)]
    return np.array(B)


for trip in [(1, 2, 3), (2, 4, 6)]:
    B = basis(trip)
    # composition: |xy| = |x||y| ?
    worstN = 0
    worstAlt = 0
    zd = 0
    for _ in range(300):
        c1 = rng.normal(size=8)
        c2 = rng.normal(size=8)
        x = c1 @ B
        y = c2 @ B
        p = cd_mul(x, y)
        worstN = max(
            worstN, abs(np.linalg.norm(p) - np.linalg.norm(x) * np.linalg.norm(y))
        )
        worstAlt = max(
            worstAlt, np.linalg.norm(cd_mul(cd_mul(x, x), y) - cd_mul(x, cd_mul(x, y)))
        )
        if (
            np.linalg.norm(p) < 1e-8
            and np.linalg.norm(x) > 1e-3
            and np.linalg.norm(y) > 1e-3
        ):
            zd += 1
    print(
        trip,
        "max |‖xy‖-‖x‖‖y‖| = %.2e ; max alternator = %.2e ; zero-divisor hits %d"
        % (worstN, worstAlt, zd),
    )


# does a generic H_s sit inside any of the 7?
def orth(M, tol=1e-9):
    U, S, Vt = np.linalg.svd(np.array(M, float), full_matrices=False)
    r = int((S > tol * max(1, S[0])).sum())
    return Vt[:r]


def inter_dim(A, Bm):
    return A.shape[0] + Bm.shape[0] - orth(np.vstack([A, Bm])).shape[0]


fano = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)]
hits = 0
for _ in range(20):
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    ul = np.zeros(N)
    ul[:8] = u
    H = orth([e(0), e(8), ul, cd_mul(e(8), ul)])
    if any(inter_dim(H, orth(basis(t))) == 4 for t in fano):
        hits += 1
print(
    "generic H_s contained in one of the 7 rho-invariant 8-dim subalgebras: %d/20"
    % hits
)
# and for the pole (H = span{1, ell})?
P = orth([e(0), e(8)])
print(
    "pole H = span{1,ell} contained in all 7:",
    all(inter_dim(P, orth(basis(t))) == 2 for t in fano),
)
