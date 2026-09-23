import numpy as np
from fast import *

rng = np.random.default_rng(41)


def dF(s, h=1e-5):
    J = np.zeros((16, 16))
    for k in range(16):
        e = np.zeros(16)
        e[k] = h
        J[:, k] = (F(s + e) - F(s - e)) / (2 * h)
    return J


def tang(s):
    A = np.delete(np.eye(16), 0, axis=1)
    A = A - np.outer(s, s @ A)
    q, _ = np.linalg.qr(A)
    return q[:, :14]


V_, D_ = [], []
for _ in range(400):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    T = tang(s)
    V_.append(float(V(s)))
    D_.append(float(np.trace(T.T @ dF(s) @ T)))
V_ = np.array(V_)
D_ = np.array(D_)
print(
    "N=400 random on S^14:  V range %.3f-%.3f  div range %+.2f..%+.2f"
    % (V_.min(), V_.max(), D_.min(), D_.max())
)
print(
    "corr(V,div) = %.4f ; div<0 count = %d/400"
    % (np.corrcoef(V_, D_)[0, 1], (D_ < 0).sum())
)
for lo, hi in [(0, 0.3), (0.3, 0.5), (0.5, 0.7), (0.7, 0.85), (0.85, 1.01)]:
    m = (V_ >= lo) & (V_ < hi)
    if m.sum():
        print(
            "  V in [%.2f,%.2f): n=%3d  mean div=%+8.3f  frac div<0 = %.2f"
            % (lo, hi, m.sum(), D_[m].mean(), (D_[m] < 0).mean())
        )
# threshold: fit sign change
from numpy.polynomial import polynomial as P

c = np.polyfit(V_, D_, 1)
print("linear fit div = %.3f*V + %.3f -> zero at V=%.4f" % (c[0], c[1], -c[1] / c[0]))
# and near crystals: sample low-V points by partial descent
lowV = []
for seed in range(20):
    r = np.random.default_rng(900 + seed)
    s = r.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    for _ in range(300):
        s = s + 0.02 * F(s)
        s[0] = 0
        s /= np.linalg.norm(s)
    T = tang(s)
    lowV.append((float(V(s)), float(np.trace(T.T @ dF(s) @ T))))
print("after 300 descent steps:", [(round(v, 4), round(d, 2)) for v, d in lowV[:8]])
print("  frac div<0 among descended:", np.mean([d < 0 for _, d in lowV]))
