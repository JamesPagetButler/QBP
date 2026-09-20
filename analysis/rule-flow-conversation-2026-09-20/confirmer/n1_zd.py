import numpy as np, cdx

np.set_printoptions(precision=4, suppress=True)
# --- 1. enumerate rank-2 zero divisors e_i + e_j and their V
zds = []
for i in range(1, 16):
    for j in range(i + 1, 16):
        s = np.zeros(16)
        s[i] = 1
        s[j] = 1
        sv = np.linalg.svd(cdx.Lmat(s), compute_uv=False)
        if sv.min() < 1e-10:
            zds.append((i, j, cdx.V(s), cdx.N(s), (sv < 1e-10).sum()))
print("rank-2 zero divisors e_i+e_j :", len(zds))
print("  V values:", sorted(set(round(z[2], 10) for z in zds)), " N^2 =", 4.0)
print("  kernel dims:", sorted(set(z[4] for z in zds)))
print("  sample:", zds[:4])
# how many non-ZD pairs and their V
nonzd = []
for i in range(1, 16):
    for j in range(i + 1, 16):
        s = np.zeros(16)
        s[i] = 1
        s[j] = 1
        sv = np.linalg.svd(cdx.Lmat(s), compute_uv=False)
        if sv.min() >= 1e-10:
            nonzd.append((i, j, round(cdx.V(s), 6), round(sv.min(), 6)))
print(
    "  non-ZD pairs:", len(nonzd), "  their V values:", sorted(set(z[2] for z in nonzd))
)
