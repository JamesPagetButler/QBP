"""#473 kill-attack 2 — shared helpers: canonical zero divisors, state-sphere maps, G₂ elements,
exact-rational product (for artefact checks).  Product/potential from flowlib.py (CD convention
(a,b)(c,d) = (ac − conj(d) b, da + b conj(c)); V(x) = N([cdLo x, cdHi x])).  Numerical flashlight.
"""

from fractions import Fraction

import numpy as np

from flowlib import N, conj, mul, potential

E = np.eye(16)
ELL = E[8]


def im(x):
    y = x.copy()
    y[..., 0] = 0.0
    return y


def nrm(x):
    return np.linalg.norm(x, axis=-1, keepdims=True)


def norm_im(x):
    """state-sphere projection: Im x / ‖Im x‖ (returns also ‖Im x‖ so degenerate words can be flagged)."""
    y = im(x)
    n = nrm(y)
    return y / np.maximum(n, 1e-300), n[..., 0]


def L_matrix(z):
    """matrix of x ↦ z·x on coordinates (columns z·e_k)."""
    return np.array([mul(z, E[k]) for k in range(16)]).T


def R_matrix(z):
    return np.array([mul(E[k], z) for k in range(16)]).T


def basis_sum_zds(tol=1e-9):
    """all e_i ± e_j (1 ≤ i < j ≤ 15) with rank L_z < 16.  Returns list of (i, j, sign, vector, kernel dim)."""
    out = []
    for i in range(1, 16):
        for j in range(i + 1, 16):
            for sg in (+1.0, -1.0):
                z = E[i] + sg * E[j]
                sv = np.linalg.svd(L_matrix(z), compute_uv=False)
                k = int(np.sum(sv < tol))
                if k > 0:
                    out.append((i, j, int(sg), z, k))
    return out


def stratified_states(n, rng, vmin=0.005, vmax=0.995, tol=1e-4, maxit=2000):
    """n imaginary unit states with V spread evenly over (vmin, vmax): random start, then projected
    gradient steps on the sphere toward the target V (line search on step size)."""
    from flowlib import gradV_exact

    targets = np.linspace(vmin, vmax, n)
    S = np.zeros((n, 16))
    for k, vt in enumerate(targets):
        s = rng.normal(size=16)
        s[0] = 0
        s /= np.linalg.norm(s)
        h = 0.05
        for _ in range(maxit):
            v = potential(s)
            if abs(v - vt) < tol:
                break
            g = gradV_exact(s)
            g[0] = 0
            g -= np.dot(g, s) * s
            d = np.sign(vt - v) * g / max(np.linalg.norm(g), 1e-12)
            # backtracking so we do not overshoot
            hh = h
            for _ in range(30):
                t = s + hh * d
                t[0] = 0
                t /= np.linalg.norm(t)
                if abs(potential(t) - vt) < abs(v - vt):
                    s = t
                    break
                hh *= 0.5
        S[k] = s
    return S


# ---- automorphisms ---------------------------------------------------------------------------
def octonion_derivation_basis():
    """D(x,y) = [L_x,L_y]+[L_x,R_y]+[R_x,R_y] on 𝕆 for basis pairs — spans Der(𝕆) = g₂ (14-dim)."""
    e8 = np.eye(8)

    def Lm(x):
        return np.array([mul(x, e8[k]) for k in range(8)]).T

    def Rm(x):
        return np.array([mul(e8[k], x) for k in range(8)]).T

    ders = []
    for i in range(1, 8):
        for j in range(i + 1, 8):
            x, y = e8[i], e8[j]
            D = (
                (Lm(x) @ Lm(y) - Lm(y) @ Lm(x))
                + (Lm(x) @ Rm(y) - Rm(y) @ Lm(x))
                + (Rm(x) @ Rm(y) - Rm(y) @ Rm(x))
            )
            ders.append(D)
    return ders


def random_g2_sedenion_aut(rng, ders=None):
    """a random element of G₂ ⊂ Aut(𝕊) acting diagonally on 𝕆 ⊕ 𝕆ℓ: φ(a,b) = (g a, g b), g = exp(D)."""
    from scipy.linalg import expm

    if ders is None:
        ders = octonion_derivation_basis()
    D = sum(c * d for c, d in zip(rng.normal(size=len(ders)), ders))
    g = expm(D)
    Phi = np.zeros((16, 16))
    Phi[:8, :8] = g
    Phi[8:, 8:] = g
    return Phi


def aut_residual(Phi):
    """max over the 256 basis pairs of |Φ(e_i e_j) − Φ(e_i) Φ(e_j)| — exact check, not sampled."""
    I, J = np.meshgrid(np.arange(16), np.arange(16), indexing="ij")
    X, Y = E[I.ravel()], E[J.ravel()]  # all 256 pairs, vectorised
    return float(np.abs(mul(X, Y) @ Phi.T - mul(X @ Phi.T, Y @ Phi.T)).max())


# ---- exact rational product (artefact check) ---------------------------------------------------
def conj_q(x):
    return [x[0]] + [-c for c in x[1:]]


def mul_q(x, y):
    n = len(x)
    if n == 1:
        return [x[0] * y[0]]
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    ac = mul_q(a, c)
    db = mul_q(conj_q(d), b)
    da = mul_q(d, a)
    bc = mul_q(b, conj_q(c))
    return [p - q for p, q in zip(ac, db)] + [p + q for p, q in zip(da, bc)]


def V_q(x):
    """V of an exact 16-vector (unnormalised): N([a,b])."""
    a, b = x[:8], x[8:]
    c = [p - q for p, q in zip(mul_q(a, b), mul_q(b, a))]
    return sum(t * t for t in c)


def to_q(v, den=1000):
    return [Fraction(int(round(float(t) * den)), den) for t in v]
