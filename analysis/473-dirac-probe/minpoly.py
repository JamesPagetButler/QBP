import numpy as np

exec(open("delta_formula.py").read().split("# check symmetric")[0])
rng = np.random.default_rng(7)
ok = True
ok0 = True
for _ in range(20):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    a, b = s[:8], s[8:]
    d2 = (lambda c: c @ c)(cd_mul(a, b) - cd_mul(b, a))
    Ts = T(s)
    ok &= np.allclose(Ts @ Ts @ Ts, d2 * Ts)
    # also for non-unit s (homogeneity): T_s^3 = ||[a,b]||^2 |s|^2 T_s ?
    s2 = s * 2.7
    a2, b2 = s2[:8], s2[8:]
    d22 = (lambda c: c @ c)(cd_mul(a2, b2) - cd_mul(b2, a2))
    T2 = T(s2)
    ok0 &= np.allclose(T2 @ T2 @ T2, d22 * T2)
print(
    "T_s^3 == ||[a,b]||^2 T_s (unit s):", ok, " (any imaginary s, no |s| factor):", ok0
)
# is T_s = 0 iff [a,b]=0 ; check rank when [a,b]!=0 : rank 8
s = rng.normal(size=16)
s[0] = 0
print("rank T_s generic:", np.linalg.matrix_rank(T(s)))
# Haar mean of delta^2 on S^14 (uniform on unit sphere in Im S)
vals = []
for _ in range(4000):
    s = rng.normal(size=15)
    s /= np.linalg.norm(s)
    a = np.concatenate([[0], s[:7]])
    b = s[7:]
    c = cd_mul(a, b) - cd_mul(b, a)
    vals.append(c @ c)
print("Haar <delta^2> = %.4f   predicted 56/85 = %.4f" % (np.mean(vals), 56 / 85))
