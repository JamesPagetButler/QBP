import numpy as np
from fast import *

rng = np.random.default_rng(3)
S = rng.normal(size=(300, 16))
S[:, 0] = 0
S /= np.linalg.norm(S, axis=1, keepdims=True)
rows = []
for s in S:
    sv = np.linalg.svd(Lmat(s), compute_uv=False)
    rows.append((float(V(s)), sv.min(), sv.max(), sv))
v = np.array([r[0] for r in rows])
smin = np.array([r[1] for r in rows])
smax = np.array([r[2] for r in rows])
print("max|smin^2 - (1-V)| =", np.abs(smin**2 - (1 - v)).max())
print("max|smax^2 - (1+V)| =", np.abs(smax**2 - (1 + v)).max())
print(
    "sample:",
    [
        (round(float(a), 5), round(float(b), 5), round(float(c), 5))
        for a, b, c in zip(v[:5], smin[:5] ** 2, smax[:5] ** 2)
    ],
)
sv = rows[0][3]
print("full sv^2 of one L_s, V=%.5f:" % v[0], np.round(sv**2, 5))
# also off-sphere: does it need N(s)=1?
x = rng.normal(size=16)
x[0] = 0
svx = np.linalg.svd(Lmat(x), compute_uv=False)
Nx = float(x @ x)
print(
    "off-sphere N=%.4f V=%.5f smin^2=%.5f  N-sqrt(V)=%.5f"
    % (Nx, float(V(x)), svx.min() ** 2, Nx - np.sqrt(float(V(x))))
)
# with real part nonzero?
y = rng.normal(size=16)
svy = np.linalg.svd(Lmat(y), compute_uv=False)
print(
    "real-part-nonzero: N=%.4f V=%.5f smin^2=%.5f"
    % (float(y @ y), float(V(y)), svy.min() ** 2)
)
