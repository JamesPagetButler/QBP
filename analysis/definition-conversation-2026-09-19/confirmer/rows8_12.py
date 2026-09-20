import numpy as np

rng = np.random.default_rng(7)


def conj(x):
    y = -x.astype(float).copy()
    y[0] = x[0]
    return y


def cd(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate([cd(a, c) - cd(conj(d), b), cd(d, a) + cd(b, conj(c))])


N = 16
e = lambda i: np.eye(N)[i]
ell = e(8)


def lift(o):
    z = np.zeros(N)
    z[:8] = o
    return z


def Hs_basis(u7):
    u = np.zeros(8)
    u[1:] = u7
    return np.array([e(0), ell, lift(u), cd(lift(u), ell)])


def dim_inter(A, B, tol=1e-9):
    QA = np.linalg.qr(A.T)[0]
    QB = np.linalg.qr(B.T)[0]
    sv = np.linalg.svd(QA.T @ QB, compute_uv=False)
    return int(np.sum(sv > 1 - 1e-7)), sv


print("=== row 8: generic pair intersection of hosted quaternion spans ===")
dims = {}
for _ in range(200):
    u1 = rng.normal(size=7)
    u1 /= np.linalg.norm(u1)
    u2 = rng.normal(size=7)
    u2 /= np.linalg.norm(u2)
    d, _ = dim_inter(Hs_basis(u1), Hs_basis(u2))
    dims[d] = dims.get(d, 0) + 1
print("generic pairs: dim histogram", dims, "(expect all 2 = span{1,ell})")
# same-u distinct crystals
u = rng.normal(size=7)
u /= np.linalg.norm(u)
d, _ = dim_inter(Hs_basis(u), Hs_basis(u))
print("same-u pair dim:", d)
# pole vs generic: pole H = span{1,ell}
pole = np.array([e(0), ell])
d, _ = dim_inter(pole, Hs_basis(u))
print("pole vs generic dim:", d, "(= 100% of the pole's algebra)")

print("\n=== row 12: does spec(Hess V) separate same-u crystals? ===")


def V(s):
    a = np.r_[s[:8], np.zeros(8)]
    b = np.r_[s[8:], np.zeros(8)]
    return float(np.sum((cd(a, b) - cd(b, a)) ** 2))


def vac(u7, b0, ph):
    r = np.sqrt(max(0.0, 1 - b0**2))
    al, ga = r * np.cos(ph), r * np.sin(ph)
    s = np.zeros(N)
    s[1:8] = al * u7
    s[8] = b0
    s[9:16] = ga * u7
    return s


def spec(s, h=1e-5):
    amb = np.eye(N)[1:]
    amb = amb - np.outer(amb @ s, s)
    Q, _ = np.linalg.qr(amb.T)
    T = Q[:, :14].T
    H = np.zeros((14, 14))
    f = lambda x: V(x / np.linalg.norm(x))
    for i in range(14):
        for j in range(i, 14):
            H[i, j] = H[j, i] = (
                f(s + h * T[i] + h * T[j])
                - f(s + h * T[i] - h * T[j])
                - f(s - h * T[i] + h * T[j])
                + f(s - h * T[i] - h * T[j])
            ) / (4 * h * h)
    return np.sort(np.linalg.eigvalsh(H))


b0 = 0.5
s1 = vac(u, b0, 0.0)
s2 = vac(u, b0, 1.3)
s3 = vac(u, -b0, 2.1)
e1, e2, e3 = spec(s1), spec(s2), spec(s3)
print(
    "||s1-s2|| =",
    round(np.linalg.norm(s1 - s2), 4),
    " max|spec1-spec2| =",
    f"{np.abs(e1-e2).max():.2e}",
    " -> phase circle NOT separated",
)
print(
    "||s1-s3|| =",
    round(np.linalg.norm(s1 - s3), 4),
    " max|spec1-spec3| =",
    f"{np.abs(e1-e3).max():.2e}",
    " -> b0 vs -b0 NOT separated",
)
s4 = vac(u, 0.8, 0.0)
print(
    "b0=0.5 vs b0=0.8 max eig:",
    round(spec(s1).max(), 4),
    "vs",
    round(spec(s4).max(), 4),
    " -> different |b0| IS separated",
)

print("\n--- debug: full spectra ---")
for tag, ss in [("b0=0.5 ph=0.0", s1), ("b0=0.5 ph=1.3", s2), ("b0=-0.5 ph=2.1", s3)]:
    print(tag, np.round(spec(ss), 4))
