import numpy as np
from fast import *

rng = np.random.default_rng(0)
s = rng.normal(size=16)
s[0] = 0
h = 1e-6
g = gradV(s)
fd = np.array(
    [(V(s + h * np.eye(16)[k]) - V(s - h * np.eye(16)[k])) / (2 * h) for k in range(16)]
)
print("analytic grad == FD:", np.allclose(g, fd, atol=1e-5), np.abs(g - fd).max())


def climb(s, n=3000, lr=0.05, sign=+1):
    for _ in range(n):
        s = s + sign * lr * F(s) * (-1 if sign < 0 else 1) * (1)
        s[0] = 0
        s /= np.linalg.norm(s)
    return s


# ascent = move along +tangential gradient = -F
res = []
for seed in range(8):
    r = np.random.default_rng(seed)
    s = r.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    for _ in range(4000):
        s = s - 0.05 * F(s)
        s[0] = 0
        s /= np.linalg.norm(s)
    res.append((float(V(s)), float(np.linalg.norm(F(s))), s.copy()))
for v, nf, _ in res:
    print("Vmax=%.9f |F|=%.2e" % (v, nf))
v, nf, s = max(res, key=lambda t: t[0])
print("argmax rounded:", np.round(s, 4))
print("N=", float((s * s).sum()), "coord0=", s[0])
sv = np.linalg.svd(Lmat(s), compute_uv=False)
print("maximiser L_s smin,smax=", sv.min(), sv.max())
