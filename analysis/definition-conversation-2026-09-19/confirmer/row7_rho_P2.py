"""Row 7 re-test: does the rho check actually kill the P2 encoding candidate?
P2's encoding octonions are (repo's own boundary_octonion_check.py):  O'_v = H'_v + H'_v*ell,
H'_v = span{1,u,v,uv}.  Test rho-invariance of O'_v and equivariance of E_v : H_s -> O'_v, x |-> x.
"""

import numpy as np

rng = np.random.default_rng(639)


def conj(x):
    y = -x.astype(float).copy()
    y[0] = x[0]
    return y


def cd(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate([cd(a, c) - cd(conj(d), b), cd(d, a) + cd(b, conj(c))])


N = 16
e = lambda i: np.eye(N)[i]
ell = e(8)


def lo(a8):
    z = np.zeros(N)
    z[:8] = a8
    return z


c3, s3 = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)


def rho(x):
    a = np.r_[x[:8], np.zeros(8)]
    a[0] = 0.0
    W = np.zeros(N)
    W[:8] = x[8:]
    W[0] = 0.0
    out = np.zeros(N)
    out[0] = x[0]
    out[8] = x[8]
    return out + c3 * a + s3 * cd(a, ell) + (-s3) * W + c3 * cd(W, ell)


def unit_im(perp=()):
    a = rng.normal(size=8)
    a[0] = 0
    for p in perp:
        a -= np.dot(a, p) * p
    return a / np.linalg.norm(a)


print(
    f"{'trial':>5} {'O_v closed':>12} {'H_s in O_v':>12} {'rho(O_v)=O_v':>14} {'rho.E - E.rho':>15} {'gap dim':>8}"
)
for t in range(6):
    u = unit_im()
    v = unit_im((u,))
    uv = cd(lo(u), lo(v))[:8]
    H4 = [e(0), lo(u), lo(v), lo(uv)]
    Ov = np.array(H4 + [cd(x, ell) for x in H4])
    B = np.linalg.qr(Ov.T)[0].T
    P = lambda z: B.T @ (B @ z)
    clo = max(np.linalg.norm(cd(a, b) - P(cd(a, b))) for a in B for b in B)
    Hs = np.array([e(0), ell, lo(u), cd(lo(u), ell)])
    cont = max(np.linalg.norm(z - P(z)) for z in Hs)
    rinv = max(np.linalg.norm(rho(z) - P(rho(z))) for z in B)
    # E_v is the inclusion H_s -> O_v ; equivariance residual on random x in H_s
    QH = np.linalg.qr(Hs.T)[0].T
    eq = 0.0
    for _ in range(100):
        x = QH.T @ rng.normal(size=4)
        eq = max(
            eq, np.linalg.norm(rho(x) - P(rho(x)))
        )  # E(rho x) defined iff rho x in O_v
    gap = 8 - np.linalg.matrix_rank(np.vstack([B, Hs]), tol=1e-9) + 4 - 4
    gapdim = 8 - 4
    print(f"{t:5d} {clo:12.2e} {cont:12.2e} {rinv:14.2e} {eq:15.2e} {gapdim:8d}")
# P2' side: is the CD low half rho-invariant?
low = np.eye(N)[:8]
Bl = low
Pl = lambda z: Bl.T @ (Bl @ z)
print(
    "\nP2' side: max ||rho(x) - proj_{O_low} rho(x)|| over the low-half basis:",
    f"{max(np.linalg.norm(rho(z)-Pl(rho(z))) for z in low):.3f}",
    "-> O_low is NOT rho-invariant (matches Lean rotAut3_moves_lowHalf)",
)
print(
    "H_s inside O_low?  ell in O_low:",
    np.linalg.norm(ell - Pl(ell)) < 1e-12,
    "(so under P2' the encoding octonion does NOT contain H_s; gap = 8-2 = 6, not 4)",
)
