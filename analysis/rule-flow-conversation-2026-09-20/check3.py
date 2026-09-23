import numpy as np, cdf as cd

rng = np.random.default_rng(7)


def proj(s, v):
    v = v.copy()
    v[0] = 0.0
    return v - (v @ s) * s


def smin(s):
    return np.linalg.svd(cd.Lmat(s), compute_uv=False)[-1]


# G. minimise sigma_min(L_s) over S14; where does it land in V?
print("G. minimise sigma_min(L_s) on S14 (finite-diff descent):")
for k in range(6):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    h = 1e-5
    for it in range(1500):
        g = np.zeros(16)
        f0 = smin(s)
        for i in range(1, 16):
            sp = s.copy()
            sp[i] += h
            sp /= np.linalg.norm(sp)
            g[i] = (smin(sp) - f0) / h
        s = s - 0.3 * proj(s, g)
        s[0] = 0
        s /= np.linalg.norm(s)
    print(
        "   sigma_min=%.6f  V=%.6f  rank=%d"
        % (smin(s), cd.V(s), np.linalg.matrix_rank(cd.Lmat(s), tol=1e-9))
    )
# H. minimise ||F||^2 on S14 -> find all critical values (saddles?)
print("H. critical values of V found by minimising ||F||^2:")
vals = []
for k in range(40):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    h = 1e-6
    for it in range(1200):
        f0 = cd.ruleField(s)
        F0 = f0 @ f0
        g = np.zeros(16)
        for i in range(1, 16):
            sp = s.copy()
            sp[i] += h
            sp /= np.linalg.norm(sp)
            fp = cd.ruleField(sp)
            g[i] = (fp @ fp - F0) / h
        s = s - 0.05 * proj(s, g)
        s[0] = 0
        s /= np.linalg.norm(s)
    if np.linalg.norm(cd.ruleField(s)) < 1e-5:
        vals.append(round(cd.V(s), 6))
import collections

print("   ", collections.Counter(vals))
# I. descent flow endpoints (the rule itself), 200 seeds
print("I. rule descent (Euler h=0.01, 20000 steps, renormalised), 200 seeds:")
ends = []
for k in range(200):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    for it in range(20000):
        s = s + 0.01 * cd.ruleField(s)
        s[0] = 0
        s /= np.linalg.norm(s)
    ends.append(cd.V(s))
ends = np.array(ends)
print(
    "   V_end: max %.3e  mean %.3e  frac>1e-6: %.3f"
    % (ends.max(), ends.mean(), (ends > 1e-6).mean())
)
