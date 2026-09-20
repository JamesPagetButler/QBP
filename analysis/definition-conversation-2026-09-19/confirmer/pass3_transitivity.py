"""Pass 3: test Stab(s)-transitivity on Fam(s) by CONSTRUCTING G2 elements explicitly.
An automorphism of O is fixed by an orthonormal basis triple (p,q,r), p,q imaginary orthonormal,
r imaginary unit perp span{1,p,q,pq}.  Build phi1:(e1,e2,e4)->(u,v1,w1), phi2:->(u,v2,w2);
psi = phi2 . phi1^-1 fixes u and carries v1 to v2, hence O'_v1 -> O'_v2.  Extend to S diagonally.
"""

import numpy as np, sys

rng = np.random.default_rng(88)


def conj(x):
    y = -x.astype(float).copy()
    y[0] = x[0]
    return y


def cdr(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate([cdr(a, c) - cdr(conj(d), b), cdr(d, a) + cdr(b, conj(c))])


o = lambda x, y: cdr(x, y)  # octonion product (8)
S = lambda x, y: cdr(x, y)  # sedenion product (16)
e8 = lambda i: np.eye(8)[i]
e16 = lambda i: np.eye(16)[i]
ell = e16(8)


def lo(a):
    z = np.zeros(16)
    z[:8] = a
    return z


def frame_auto(p, q, r):
    """linear map on O sending e1,e2,e4 -> p,q,r (and the induced words)."""
    M = np.zeros((8, 8))
    M[:, 0] = e8(0)
    img = {1: p, 2: q, 4: r}
    img[3] = o(p, q)
    img[5] = o(p, r)
    img[6] = o(q, r)
    img[7] = o(o(p, q), r)
    # match signs/indices to the actual basis products
    for i, j, k, val in [
        (1, 2, 3, img[3]),
        (1, 4, 5, img[5]),
        (2, 4, 6, img[6]),
        (3, 4, 7, img[7]),
    ]:
        pr = o(e8(i), e8(j))
        idx = int(np.argmax(np.abs(pr)))
        sgn = np.sign(pr[idx])
        img[idx] = val * sgn
    for k in range(1, 8):
        M[:, k] = img[k]
    return M


def rand_frame(u=None):
    p = (
        u
        if u is not None
        else (lambda a: a / np.linalg.norm(a))(np.r_[0, rng.normal(size=7)])
    )
    q = np.r_[0, rng.normal(size=7)]
    q -= (q @ p) * p
    q /= np.linalg.norm(q)
    pq = o(p, q)
    r = np.r_[0, rng.normal(size=7)]
    for b in [e8(0), p, q, pq]:
        r -= (r @ b) * b
    r /= np.linalg.norm(r)
    return p, q, r


# sanity: frame maps are octonion automorphisms
worst = 0.0
for _ in range(30):
    p, q, r = rand_frame()
    M = frame_auto(p, q, r)
    for _ in range(10):
        x, y = rng.normal(size=8), rng.normal(size=8)
        worst = max(worst, np.linalg.norm(M @ o(x, y) - o(M @ x, M @ y)))
print(f"frame-built maps are octonion automorphisms: max residual {worst:.2e}")
sys.stdout.flush()


def Ov(u, v):
    uv = o(u, v)
    H4 = [e16(0), lo(u), lo(v), lo(uv)]
    B = np.array(H4 + [S(x, ell) for x in H4])
    Q, _ = np.linalg.qr(B.T)
    return Q[:, :8].T


def lift(M8):
    """G2 element of Aut(S): a + b*ell -> phi(a) + phi(b)*ell"""
    L = np.zeros((16, 16))
    L[:8, :8] = M8
    L[8:, 8:] = M8
    return L


print(
    "\n--- transitivity test: for random v1,v2 perp u, find Psi in Stab(s) with Psi(O'_v1)=O'_v2 ---"
)
okA = okS = okF = 0
TR = 20
for t in range(TR):
    u = (lambda a: a / np.linalg.norm(a))(np.r_[0, rng.normal(size=7)])
    p1, v1, w1 = rand_frame(u)
    p2, v2, w2 = rand_frame(u)
    M1 = frame_auto(u, v1, w1)
    M2 = frame_auto(u, v2, w2)
    psi = M2 @ np.linalg.inv(M1)
    Psi = lift(psi)
    # (1) Psi is an automorphism of S
    ra = max(
        np.linalg.norm(Psi @ S(x, y) - S(Psi @ x, Psi @ y))
        for x, y in [(rng.normal(size=16), rng.normal(size=16)) for _ in range(20)]
    )
    okA += ra < 1e-9
    # (2) Psi fixes every crystal with direction u  (s = a*u + b0*ell + g*u*ell)
    a_, b0, g = rng.normal(size=3)
    n = np.sqrt(a_**2 + b0**2 + g**2)
    a_, b0, g = a_ / n, b0 / n, g / n
    s = a_ * lo(u) + b0 * ell + g * S(lo(u), ell)
    okS += np.linalg.norm(Psi @ s - s) < 1e-9
    # (3) Psi carries O'_v1 onto O'_v2
    B1, B2 = Ov(u, v1), Ov(u, v2)
    P2_ = B2.T @ B2
    okF += max(np.linalg.norm(Psi @ b - P2_ @ (Psi @ b)) for b in B1) < 1e-9
print(f"Psi is an automorphism of S        : {okA}/{TR}")
print(f"Psi fixes the crystal s (Stab(s))  : {okS}/{TR}")
print(f"Psi(O'_v1) = O'_v2  (TRANSITIVITY) : {okF}/{TR}")
