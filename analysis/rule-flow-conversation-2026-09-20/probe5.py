import numpy as np
from fast import *
from cd import mul, conj

rng = np.random.default_rng(21)


# A) the norm defect: Delta = N(sx) - N(s)N(x).  Test candidate closed forms.
def oc(x):
    y = x.copy()
    y[0] = x[0]
    y[1:] = -x[1:]
    return y


cands = {}
tot = {
    k: 0.0 for k in ["2<Kc,d>", "-2<Kc,d>", "2<cK,d>", "-2<cK,d>", "2<Kd,c>", "2<dK,c>"]
}
for _ in range(200):
    s = rng.normal(size=16)
    x = rng.normal(size=16)
    a, b = s[:8], s[8:]
    c, d = x[:8], x[8:]
    K = o(a, b) - o(b, a)
    D = float((mul(s, x) ** 2).sum() - (s @ s) * (x @ x))
    tot["2<Kc,d>"] = max(tot["2<Kc,d>"], abs(D - 2 * float(o(K, c) @ d)))
    tot["-2<Kc,d>"] = max(tot["-2<Kc,d>"], abs(D + 2 * float(o(K, c) @ d)))
    tot["2<cK,d>"] = max(tot["2<cK,d>"], abs(D - 2 * float(o(c, K) @ d)))
    tot["-2<cK,d>"] = max(tot["-2<cK,d>"], abs(D + 2 * float(o(c, K) @ d)))
    tot["2<Kd,c>"] = max(tot["2<Kd,c>"], abs(D - 2 * float(o(K, d) @ c)))
    tot["2<dK,c>"] = max(tot["2<dK,c>"], abs(D - 2 * float(o(d, K) @ c)))
print("A) max |Delta - candidate| over 200:", {k: round(v, 6) for k, v in tot.items()})
# B) the load-bearing inequality N(sx) >= (N(s)-sqrt(V(s))) N(x)
worst = 1e9
for _ in range(3000):
    s = rng.normal(size=16)
    x = rng.normal(size=16)
    lhs = float((mul(s, x) ** 2).sum())
    rhs = (float(s @ s) - np.sqrt(float(V(s)))) * float(x @ x)
    worst = min(worst, lhs - rhs)
print("B) min over 3000 of N(sx)-(N-sqrtV)N(x):", worst)
# C) elementary bound V <= N^2
w = 1e9
for _ in range(5000):
    s = rng.normal(size=16)
    w = min(w, float(s @ s) ** 2 - float(V(s)))
print("C) min over 5000 of N^2 - V:", w)


# D) dimension of the crystal set {V=0} in S^14
def samp_cry(r):
    u = r.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    g = r.normal(size=3)
    g /= np.linalg.norm(g)
    al, b0, ga = g
    return np.concatenate([al * u, b0 * np.eye(8)[0] + ga * u])


base = samp_cry(np.random.default_rng(2))
P = []
for k in range(600):
    r = np.random.default_rng(5000 + k)
    u = base[:8].copy()
    nu = np.linalg.norm(u)
    u = u / nu
    u2 = u + 0.01 * r.normal(size=8)
    u2[0] = 0
    u2 /= np.linalg.norm(u2)
    g = np.array([nu, base[8], float(base[8:] @ u)])
    g = g / np.linalg.norm(g)
    g2 = g + 0.01 * r.normal(size=3)
    g2 /= np.linalg.norm(g2)
    s2 = np.concatenate([g2[0] * u2, g2[1] * np.eye(8)[0] + g2[2] * u2])
    P.append(s2 - base)
sv = np.linalg.svd(np.array(P), compute_uv=False)
print("D) crystal-set local tangent sv (rel):", np.round(sv[:14] / sv[0], 4))
print(
    "   rank at 1e-2:",
    int((sv / sv[0] > 1e-2).sum()),
    " max V on samples:",
    float(V(np.array([base + p for p in P])).max()),
)
