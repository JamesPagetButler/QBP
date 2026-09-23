import numpy as np, cdf as cd

rng = np.random.default_rng(0)
e = lambda i: np.eye(16)[i]
w = e(1) + e(10)
print("rank L_(e1+e10) =", np.linalg.matrix_rank(cd.Lmat(w), tol=1e-9))
s = rng.normal(size=16)
s[0] = 0.0
s /= np.linalg.norm(s)
g = cd.gradV(s)
h = 1e-6
fd = np.array([(cd.V(s + h * e(i)) - cd.V(s - h * e(i))) / (2 * h) for i in range(16)])
print(
    "gradV vs FD max err: %.3e  |gradV|=%.4f"
    % (np.max(np.abs(g - fd)), np.linalg.norm(g))
)


def proj(s, v):
    v = v.copy()
    v[0] = 0.0
    return v - (v @ s) * s


best = []
for trial in range(30):
    s = rng.normal(size=16)
    s[0] = 0.0
    s /= np.linalg.norm(s)
    for it in range(4000):
        s = s + 0.02 * proj(s, cd.gradV(s))
        s[0] = 0.0
        s /= np.linalg.norm(s)
    best.append((cd.V(s), np.linalg.norm(cd.ruleField(s)), s.copy()))
vals = sorted(b[0] for b in best)
print(
    "V over 30 ascents: min %.6f  max %.6f  (ties at max: %d)"
    % (vals[0], vals[-1], sum(1 for v in vals if v > vals[-1] - 1e-6))
)
top = max(best, key=lambda b: b[0])
print(
    "best V=%.8f  ||F||=%.3e  rank L_s=%d"
    % (top[0], top[1], np.linalg.matrix_rank(cd.Lmat(top[2]), tol=1e-9))
)
np.save("maximiser.npy", top[2])
# Gemini's candidate: s = (e1 + e2*l)/sqrt2  -> lo=e1/sqrt2, hi=e2/sqrt2 => coords 1 and 8+2=10
g2 = np.zeros(16)
g2[1] = 1 / np.sqrt(2)
g2[10] = 1 / np.sqrt(2)
print(
    "Gemini cand: N=%.6f V=%.6f ||F||=%.3e  gradV/s ratio=%s"
    % (
        cd.N(g2),
        cd.V(g2),
        np.linalg.norm(cd.ruleField(g2)),
        np.round(cd.gradV(g2)[[1, 10]] / g2[[1, 10]], 6),
    )
)
print("  rank L_cand =", np.linalg.matrix_rank(cd.Lmat(g2), tol=1e-9))
