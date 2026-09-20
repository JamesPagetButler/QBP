import numpy as np
from fast import *

rng = np.random.default_rng(7)


def smin_kdim(s):
    sv = np.linalg.svd(Lmat(s), compute_uv=False)
    return sv.min(), int((sv < 1e-9).sum())


# 1) maximisers: kernel dim
print("--- maximisers of V (projected ascent) ---")
for seed in range(5):
    r = np.random.default_rng(100 + seed)
    s = r.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    for _ in range(4000):
        s = s - 0.05 * F(s)
        s[0] = 0
        s /= np.linalg.norm(s)
    a, b = s[:8], s[8:]
    sm, kd = smin_kdim(s)
    print(
        "V=%.9f |F|=%.1e  smin=%.2e kerdim=%d | b0=%.3e  <a,b>=%.3e |a|^2=%.4f |b|^2=%.4f"
        % (
            V(s),
            np.linalg.norm(F(s)),
            sm,
            kd,
            b[0],
            float(a @ b),
            float(a @ a),
            float(b @ b),
        )
    )
# 2) constructed zero divisors: a,b imaginary orthogonal equal norm
print("--- constructed a,b in Im O, a_|_b, |a|=|b|=1/sqrt2 ---")
for t in range(5):
    a = rng.normal(size=8)
    a[0] = 0
    a /= np.linalg.norm(a)
    b = rng.normal(size=8)
    b[0] = 0
    b -= (a @ b) * a
    b /= np.linalg.norm(b)
    s = np.concatenate([a, b]) / np.sqrt(2)
    sm, kd = smin_kdim(s)
    print("V=%.9f smin=%.2e kerdim=%d |F|=%.1e" % (V(s), sm, kd, np.linalg.norm(F(s))))
# 3) do V=1 <=> zero divisor?  scan random points
print("--- random points on S^14: V vs smin ---")
S = rng.normal(size=(2000, 16))
S[:, 0] = 0
S /= np.linalg.norm(S, axis=1, keepdims=True)
vs = V(S)
sms = np.array([smin_kdim(x)[0] for x in S])
print("max V over 2000 random:", vs.max(), " min smin:", sms.min())
print("corr(V, -log smin):", np.corrcoef(vs, -np.log(sms))[0, 1])
# 4) crystals: are they zero divisors?  s = alpha u + (b0 + gamma u) l
print("--- crystals ---")
for t in range(6):
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    c = rng.normal(size=3)
    c /= np.linalg.norm(c)
    al, b0, ga = c
    a = al * u
    b = b0 * np.eye(8)[0] + ga * u
    s = np.concatenate([a, b])
    sm, kd = smin_kdim(s)
    print(
        "V=%.2e N=%.4f smin=%.3e kerdim=%d b0=%.3f" % (V(s), (s * s).sum(), sm, kd, b0)
    )
