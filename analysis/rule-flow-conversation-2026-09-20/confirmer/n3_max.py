import numpy as np, cdx, flow

rng = np.random.default_rng(11)


def proj(s):
    s = s.copy()
    s[..., 0] = 0
    return s / np.linalg.norm(s, axis=-1, keepdims=True)


# ---- ascent to maximisers of V on StateSphere
res = []
for k in range(12):
    s = proj(rng.normal(size=16))
    for it in range(4000):
        s = proj(s + 0.02 * (-flow.F(s)))  # ascent: +tangential grad
    L = cdx.Lmat(s)
    sv = np.linalg.svd(L, compute_uv=False)
    kd = int((sv < 1e-7).sum())
    g = flow.gradV(s)
    # algebraic identity test: gradV = 4V s + (gradV)_0 * 1 ?
    resid = g - 4 * cdx.V(s) * s
    resid[0] -= g[0]
    res.append(
        (
            cdx.V(s),
            np.linalg.norm(flow.F(s)),
            kd,
            sv.min(),
            np.abs(resid).max(),
            s[8],
            float((s[:8] * s[:8]).sum()),
            float((s[8:] * s[8:]).sum()),
            float((s[1:8] * s[9:16]).sum()),
        )
    )
import statistics

print("maximisers (12 independent ascents):")
print(
    " V            |F|        kerdim  sigma_min   |gradV-4Vs-c1|   b0        |a|^2    |b|^2   <a,Im b>"
)
for r in res[:6]:
    print(" %.12f %.2e  %d      %.2e   %.2e   %+.2e  %.4f  %.4f  %+.2e" % r)
print(" all V:", ["%.10f" % r[0] for r in res])
print(" all kernel dims:", [r[2] for r in res])
print(
    " max |F| :",
    max(r[1] for r in res),
    " max algebraic residual:",
    max(r[4] for r in res),
)
np.save("maxpt.npy", s)
# ---- random crystals: s = alpha*u + (b0 + gamma*u) l  , u in Im O unit
print()
ks = []
for k in range(200):
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    al, ga, b0 = rng.normal(size=3)
    a = al * u
    b = b0 * np.eye(8)[0] + ga * u
    s = np.concatenate([a, b])
    s /= np.linalg.norm(s)
    sv = np.linalg.svd(cdx.Lmat(s), compute_uv=False)
    ks.append((cdx.V(s), sv.min(), int((sv < 1e-8).sum()), np.linalg.norm(flow.F(s))))
ks = np.array(ks)
print(
    "random crystals (200): max V = %.3e  min sigma_min = %.6f  max kernel dim = %d  max |F| = %.3e"
    % (ks[:, 0].max(), ks[:, 1].min(), int(ks[:, 2].max()), ks[:, 3].max())
)
