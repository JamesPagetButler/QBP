import numpy as np, cdx

rng = np.random.default_rng(7)


# --- spectrum of L_s^T L_s on 60 random UNIT s, and 60 random unconstrained s
def check(s):
    L = cdx.Lmat(s)
    R = cdx.Rmat(s)
    eL = np.sort(np.linalg.eigvalsh(L.T @ L))
    eR = np.sort(np.linalg.eigvalsh(R.T @ R))
    n = cdx.N(s)
    v = cdx.V(s)
    rt = np.sqrt(max(v, 0.0))
    pred = np.sort(np.array([n - rt] * 4 + [n] * 8 + [n + rt] * 4))
    return np.abs(eL - pred).max() / max(n, 1e-30), np.abs(eR - pred).max() / max(
        n, 1e-30
    )


errs = []
for k in range(60):
    s = rng.normal(size=16)
    s /= np.linalg.norm(s)
    errs.append(check(s))
errs = np.array(errs)
print(
    "UNIT s (n=60): max rel err spec(L^T L) = %.3e ; spec(R^T R) = %.3e"
    % (errs[:, 0].max(), errs[:, 1].max())
)
errs = []
for k in range(200):
    s = rng.normal(size=16) * rng.uniform(0.2, 4)
    errs.append(check(s))
errs = np.array(errs)
print(
    "ARBITRARY s (n=200): max rel err L = %.3e ; R = %.3e"
    % (errs[:, 0].max(), errs[:, 1].max())
)
# --- V <= N^2 on 5000 samples (unconstrained) and 5000 on StateSphere
s = rng.normal(size=(5000, 16)) * rng.uniform(0.1, 3, size=(5000, 1))
m = cdx.N(s) ** 2 - cdx.V(s)
print(
    "V <= N^2 unconstrained (5000): min(N^2 - V) = %.6f ; violations = %d"
    % (m.min(), (m < -1e-9).sum())
)
t = rng.normal(size=(5000, 16))
t[:, 0] = 0
t /= np.linalg.norm(t, axis=1, keepdims=True)
vt = cdx.V(t)
print(
    "StateSphere (5000): V in [%.6f, %.6f] ; max V <= 1? %s"
    % (vt.min(), vt.max(), vt.max() <= 1 + 1e-12)
)
