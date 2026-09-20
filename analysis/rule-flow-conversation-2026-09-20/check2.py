import numpy as np, cdf as cd

rng = np.random.default_rng(1)


def rk(s):
    return np.linalg.matrix_rank(cd.Lmat(s), tol=1e-9)


def unit_im8(r):
    v = r.normal(size=8)
    v[0] = 0.0
    return v / np.linalg.norm(v)


# A. crystals: s = loOf(a*u) + hiOf(b0*1 + g*u), u imaginary octonion unit
print("A. crystals (vacua): V, rank L_s, sigma_min")
for k in range(6):
    u = unit_im8(rng)
    p = rng.normal(size=3)
    p /= np.linalg.norm(p)
    al, g, b0 = p
    a = al * u
    b = b0 * np.eye(8)[0] + g * u
    s = np.concatenate([a, b])
    sv = np.linalg.svd(cd.Lmat(s), compute_uv=False)
    print("   V=%.2e N=%.4f rank=%d sigma_min=%.4f" % (cd.V(s), cd.N(s), rk(s), sv[-1]))
# B. candidate ZD family: a,b imaginary octonions, |a|=|b|=1/sqrt2, a.b=0
print("B. a,b in Im O, |a|=|b|=1/sqrt2, a perp b:")
for k in range(6):
    a = unit_im8(rng)
    b = unit_im8(rng)
    b = b - (b @ a) * a
    b /= np.linalg.norm(b)
    a /= np.sqrt(2)
    b /= np.sqrt(2)
    s = np.concatenate([a, b])
    print(
        "   V=%.6f rank=%d ||F||=%.2e"
        % (cd.V(s), rk(s), np.linalg.norm(cd.ruleField(s)))
    )
# C. generic sphere points
print("C. generic points on S14:")
for k in range(6):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    print("   V=%.6f rank=%d" % (cd.V(s), rk(s)))
# D. is {V=1} == ZD locus? maximise V from random starts, check rank + structure
print("D. maximisers of V:")


def proj(s, v):
    v = v.copy()
    v[0] = 0.0
    return v - (v @ s) * s


for k in range(8):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    for it in range(6000):
        s = s + 0.02 * proj(s, cd.gradV(s))
        s[0] = 0
        s /= np.linalg.norm(s)
    a, b = s[:8], s[8:]
    print(
        "   V=%.8f rank=%d |a|^2=%.4f |b|^2=%.4f a.b=%.2e a0=%.2e b0=%.2e"
        % (cd.V(s), rk(s), a @ a, b @ b, a @ b, a[0], b[0])
    )
# E. does V ever exceed 1 on the sphere? random search
mx = 0.0
for k in range(20000):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    mx = max(mx, cd.V(s))
print("E. max V over 20000 random sphere points: %.6f" % mx)
# F. rank vs V on random points (is low rank only at V=1?)
lows = [
    (cd.V(s), rk(s))
    for s in [
        (lambda t: (t.__setitem__(0, 0), t / np.linalg.norm(t))[1])(rng.normal(size=16))
        for _ in range(200)
    ]
]
print("F. any rank<16 among 200 generic points:", [x for x in lows if x[1] < 16][:5])
