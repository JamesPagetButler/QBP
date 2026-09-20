import numpy as np
from fast import *

rng = np.random.default_rng(11)
# A) general s (real part free, any norm): sv(L_s)^2 = {N-sqrt(V) x4, N x8, N+sqrt(V) x4} ?
err = 0.0
for _ in range(200):
    s = rng.normal(size=16) * rng.uniform(0.1, 3)
    sv2 = np.sort(np.linalg.svd(Lmat(s), compute_uv=False) ** 2)
    N = float(s @ s)
    r = np.sqrt(float(V(s)))
    pred = np.sort(np.array([N - r] * 4 + [N] * 8 + [N + r] * 4))
    err = max(err, np.abs(sv2 - pred).max() / max(1, N))
print("A) max rel err over 200 general s:", err)
# also right multiplication
err2 = 0.0
for _ in range(100):
    s = rng.normal(size=16)
    R = np.einsum("j,ijk->ki", s, M16)  # (y*s)_k
    sv2 = np.sort(np.linalg.svd(R, compute_uv=False) ** 2)
    N = float(s @ s)
    r = np.sqrt(float(V(s)))
    err2 = max(
        err2,
        np.abs(sv2 - np.sort(np.array([N - r] * 4 + [N] * 8 + [N + r] * 4))).max()
        / max(1, N),
    )
print("A') same for right mult R_s:", err2)


# B) dimension of the zero-divisor locus in S^14, by Jacobian rank of (V-1) at a ZD point
def num_jac(f, s, h=1e-6):
    return np.array(
        [
            (f(s + h * np.eye(16)[k]) - f(s - h * np.eye(16)[k])) / (2 * h)
            for k in range(16)
        ]
    )


a = rng.normal(size=8)
a[0] = 0
a /= np.linalg.norm(a)
b = rng.normal(size=8)
b[0] = 0
b -= (a @ b) * a
b /= np.linalg.norm(b)
s = np.concatenate([a, b]) / np.sqrt(2)
print(
    "B) at a ZD: V=%.9f, grad V =" % V(s),
    np.round(num_jac(V, s), 6)[:4],
    "... norm",
    np.linalg.norm(num_jac(V, s)),
)


# tangent-space dim of {V=1} near s by sampling the set directly:
def sample_zd(r):
    a = r.normal(size=8)
    a[0] = 0
    a /= np.linalg.norm(a)
    b = r.normal(size=8)
    b[0] = 0
    b -= (a @ b) * a
    b /= np.linalg.norm(b)
    return np.concatenate([a, b]) / np.sqrt(2)


base = sample_zd(np.random.default_rng(5))
pts = []
for k in range(400):
    r = np.random.default_rng(1000 + k)
    # perturb base slightly within the ZD family
    aa = base[:8] * np.sqrt(2) + 0.01 * r.normal(size=8)
    aa[0] = 0
    aa /= np.linalg.norm(aa)
    bb = base[8:] * np.sqrt(2) + 0.01 * r.normal(size=8)
    bb[0] = 0
    bb -= (aa @ bb) * aa
    bb /= np.linalg.norm(bb)
    pts.append(np.concatenate([aa, bb]) / np.sqrt(2) - base)
Pm = np.array(pts)
sv = np.linalg.svd(Pm, compute_uv=False)
print(
    "B') local tangent dims (sv of 400 in-set perturbations):",
    np.round(sv[:16] / sv[0], 4),
)
print("   rank at 1e-2 rel:", int((sv / sv[0] > 1e-2).sum()))
