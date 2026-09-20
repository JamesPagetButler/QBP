import numpy as np, itertools, cdx, flow

# Lean's `witness` = loOf e1 + hiOf e2 = e1 + e10 ; N = 2, V = 4 -> V/N^2 = 1 : ON the ZD locus
w = np.zeros(16)
w[1] = 1
w[10] = 1
print(
    "Lean witness e1+e10:  N=%.1f  V=%.1f  V/N^2=%.3f  |F(w/sqrt2)|=%.2e  ker dim=%d"
    % (
        cdx.N(w),
        cdx.V(w),
        cdx.V(w) / cdx.N(w) ** 2,
        np.linalg.norm(flow.F(w / np.sqrt(2))),
        int((np.linalg.svd(cdx.Lmat(w), compute_uv=False) < 1e-10).sum()),
    )
)
# search small integer-support in-flight witnesses 0 < V < N^2 with F != 0
best = []
for supp in itertools.combinations(range(1, 16), 3):
    s = np.zeros(16)
    for i in supp:
        s[i] = 1
    n = cdx.N(s)
    v = cdx.V(s)
    r = v / n**2
    if 1e-9 < r < 1 - 1e-9:
        u = s / np.sqrt(n)
        best.append(
            (supp, round(v, 4), round(n, 4), round(r, 6), np.linalg.norm(flow.F(u)))
        )
best.sort(key=lambda t: -t[4])
print("3-term in-flight witnesses found:", len(best))
for b in best[:5]:
    print("  e%s  V=%s N=%s V/N^2=%s |F|=%.4f" % (b[0], b[1], b[2], b[3], b[4]))
# 2-term
b2 = []
for i, j in itertools.combinations(range(1, 16), 2):
    s = np.zeros(16)
    s[i] = 1
    s[j] = 1
    r = cdx.V(s) / cdx.N(s) ** 2
    if 1e-9 < r < 1 - 1e-9:
        b2.append((i, j, r))
print("2-term in-flight witnesses:", len(b2))
