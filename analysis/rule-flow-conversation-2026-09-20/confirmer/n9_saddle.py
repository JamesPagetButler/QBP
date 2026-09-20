import numpy as np, cdx, flow
from scipy.optimize import minimize

rng = np.random.default_rng(101)


def proj(s):
    s = s.copy()
    s[0] = 0
    return s / np.linalg.norm(s)


def obj(x):
    s = proj(x)
    return float((flow.F(s) ** 2).sum())


found = {}
for k in range(120):
    x0 = proj(rng.normal(size=16))
    r = minimize(
        obj,
        x0,
        method="Nelder-Mead",
        options={"maxiter": 20000, "fatol": 1e-18, "xatol": 1e-12},
    )
    s = proj(r.x)
    nf = np.linalg.norm(flow.F(s))
    v = cdx.V(s)
    if nf < 1e-7:
        key = round(v, 6)
        found[key] = found.get(key, 0) + 1
print("critical points of V|_S14 located by minimising ||F||^2 (120 starts, tol 1e-7):")
for v, c in sorted(found.items()):
    print("   V = %.6f   count %d" % (v, c))
print("any with 0 < V < 1 ?", any(1e-6 < v < 1 - 1e-6 for v in found))
