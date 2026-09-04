import numpy as np

exec(open("dirac_probe.py").read().split("np.set_printoptions")[0])
n = 16
rng = np.random.default_rng(3)


def T(s):  # x -> [s,s,x] = (ss)x - s(sx)
    ss = cd_mul(s, s)
    return np.column_stack([cd_mul(ss, e) - cd_mul(s, cd_mul(s, e)) for e in basis(n)])


def delta(s):
    w = np.linalg.eigvalsh((T(s) + T(s).T) / 2)
    return w.max()


# check symmetric & traceless
s = rng.normal(size=16)
s[0] = 0
s /= np.linalg.norm(s)
print("T symmetric:", np.allclose(T(s), T(s).T), " trace:", round(np.trace(T(s)), 8))
print("spec T:", np.round(np.unique(np.round(np.linalg.eigvalsh(T(s)), 6)), 4))
# structure: s = (a, b), a in Im O (7), b in O (8)
rows = []
for _ in range(6):
    a = rng.normal(size=8)
    a[0] = 0
    b = rng.normal(size=8)
    s = np.concatenate([a, b])
    s /= np.linalg.norm(s)
    a, b = s[:8], s[8:]
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    # candidate invariants
    ab = cd_mul(a, b)
    ba = cd_mul(b, a)
    comm = ab - ba
    # b = b0 + bIm ; cross-like: Im(a * bIm)
    bIm = b.copy()
    bIm[0] = 0
    axb = (cd_mul(a, bIm) - cd_mul(bIm, a)) / 2
    rows.append(
        (
            delta(s),
            na,
            nb,
            b[0],
            np.linalg.norm(axb),
            np.linalg.norm(comm),
            na * np.linalg.norm(bIm),
        )
    )
print("delta | |a| | |b| | b0 | |a x bIm| | |[a,b]| | |a||bIm|")
for r in rows:
    print(" ".join(f"{v:8.4f}" for v in r))
# hypotheses: delta = 2|a x bIm| ? delta = |[a,b]| ?
for r in rows:
    print("2|a x bIm|=%.4f  |[a,b]|=%.4f  delta=%.4f" % (2 * r[4], r[5], r[0]))
