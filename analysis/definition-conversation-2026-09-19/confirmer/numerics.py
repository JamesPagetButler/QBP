"""Confirmer's INDEPENDENT recomputation. No repo imports.
(i) V closed form; (ii) transverse Hessian at a vacuum; (iii) rho-invariant octonion subalgebras.
"""

import numpy as np

rng = np.random.default_rng(20260919)


# ---------- independent Cayley-Dickson product: (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c))
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


# ---------- independent octonion product from the Fano triples (cross-check of cd at n=8)
FANO = [(1, 2, 3), (1, 4, 5), (1, 7, 6), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 6, 5)]


def omul_fano(x, y):
    z = np.zeros(8)
    z[0] = x[0] * y[0]
    for i in range(1, 8):
        z[0] -= x[i] * y[i]
        z[i] += x[0] * y[i] + x[i] * y[0]
    for i, j, k in FANO:
        for p, q, r, s_ in [
            (i, j, k, 1),
            (j, k, i, 1),
            (k, i, j, 1),
            (j, i, k, -1),
            (k, j, i, -1),
            (i, k, j, -1),
        ]:
            z[r] += s_ * x[p] * y[q]
    return z


# sanity: Fano octonions are norm-multiplicative & alternative
w = 0.0
for _ in range(200):
    x, y = rng.normal(size=8), rng.normal(size=8)
    w = max(
        w, abs(np.linalg.norm(omul_fano(x, y)) - np.linalg.norm(x) * np.linalg.norm(y))
    )
print("[check] Fano-built octonion norm-multiplicativity residual:", w)
w = 0.0
for _ in range(200):
    x, y = rng.normal(size=8), rng.normal(size=8)
    w = max(
        w, np.linalg.norm(omul_fano(x, omul_fano(x, y)) - omul_fano(omul_fano(x, x), y))
    )
print("[check] Fano-built octonion alternativity residual:", w)
w = 0.0
for _ in range(200):
    x, y = rng.normal(size=8), rng.normal(size=8)
    w = max(w, abs(np.linalg.norm(cd(x, y)) - np.linalg.norm(x) * np.linalg.norm(y)))
print("[check] CD-built octonion (n=8) norm-multiplicativity residual:", w)
# level 16 must FAIL multiplicativity (sedenions)
w = 0.0
for _ in range(200):
    x, y = rng.normal(size=16), rng.normal(size=16)
    w = max(w, abs(np.linalg.norm(cd(x, y)) - np.linalg.norm(x) * np.linalg.norm(y)))
print("[check] sedenion norm-multiplicativity DEVIATION (must be large):", w)

N = 16
ell = np.eye(N)[8]


def V(s):
    a = np.r_[s[:8], np.zeros(8)]
    b = np.r_[s[8:], np.zeros(8)]
    return float(np.sum((cd(a, b) - cd(b, a)) ** 2))


def Vclosed(s):
    a = s[:8]
    b = s[8:]
    c = b.copy()
    c[0] = 0.0
    return 4 * (a @ a * (c @ c) - (a @ c) ** 2)


print("\n===== (i) closed form V = 4(|a|^2|Im b|^2 - <a,Im b>^2) =====")
worst = 0.0
for _ in range(2000):
    s = rng.normal(size=N)
    s[0] = 0.0
    s /= np.linalg.norm(s)
    worst = max(worst, abs(V(s) - Vclosed(s)))
print("max |V_cdmul - V_closedform| over 2000 imaginary unit sedenions:", worst)

print("\n===== (ii) transverse Hessian at a vacuum =====")


def random_vacuum(rng, b0=None):
    u = rng.normal(size=7)
    u /= np.linalg.norm(u)  # unit in Im O_low
    if b0 is None:
        b0 = rng.uniform(-0.95, 0.95)
    r = np.sqrt(1 - b0**2)
    ph = rng.uniform(0, 2 * np.pi)
    al, ga = r * np.cos(ph), r * np.sin(ph)
    s = np.zeros(N)
    s[1:8] = al * u
    s[8] = b0
    s[9:16] = ga * u
    return s, b0, u


def hess_on_sphere(s, h=1e-5):
    # tangent basis of S^14 inside {coord0 = 0}
    amb = np.eye(N)[1:]  # 15 dirs (drop coord 0)
    amb = amb - np.outer(amb @ s, s)  # project off radial
    Q, _ = np.linalg.qr(amb.T)
    T = Q[:, :14].T  # 14 x 16 orthonormal tangent basis
    n = 14
    H = np.zeros((n, n))

    def f(x):
        return V(x / np.linalg.norm(x))

    for i in range(n):
        for j in range(i, n):
            vp = (
                f(s + h * T[i] + h * T[j])
                - f(s + h * T[i] - h * T[j])
                - f(s - h * T[i] + h * T[j])
                + f(s - h * T[i] - h * T[j])
            ) / (4 * h * h)
            H[i, j] = H[j, i] = vp
    return H


print(
    f"{'b0':>8} {'rank':>5} {'nonzero eigs (min..max)':>30} {'8(1-b0^2)':>12} {'trace':>10} {'48(1-b0^2)':>12}"
)
for b0 in [0.0, 0.3, 0.5, 0.70710678, 0.866, 0.95, 0.999999]:
    s, b0_, u = random_vacuum(rng, b0)
    H = hess_on_sphere(s)
    ev = np.sort(np.linalg.eigvalsh(H))
    nz = ev[np.abs(ev) > 1e-3]
    print(
        f"{b0:8.4f} {len(nz):5d} {(nz.min() if len(nz) else 0):14.6f}..{(nz.max() if len(nz) else 0):<14.6f} {8*(1-b0**2):12.6f} {H.trace():10.4f} {48*(1-b0**2):12.6f}"
    )
# u/phase independence
tr = []
for _ in range(4):
    s, _, _ = random_vacuum(rng, 0.5)
    tr.append(hess_on_sphere(s).trace())
print(
    "traces at b0=0.5, 4 random (u, phase):",
    np.round(tr, 6),
    " expected",
    48 * (1 - 0.25),
)

print("\n===== (iii) rho-invariant octonion subalgebras =====")
c3, s3 = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)


def rho(x):
    # on Im O_low: a -> c3*a + s3*(a*ell); on Im O_low * ell: al -> -s3*a + c3*(a*ell); 1, ell fixed
    a = np.r_[x[:8], np.zeros(8)]
    a[0] = 0.0
    b = np.r_[x[8:], np.zeros(8)]
    b0 = b[0]
    b[0] = 0.0  # b = Im part gives the "a*ell" component
    al = cd(a, ell)  # a*ell  (lives in high half)
    bl = np.zeros(N)
    bl[:8] = b[:8]  # this is the octonion w with x_high = w*ell... careful below
    out = np.zeros(N)
    out[0] = x[0]
    out[8] = b0
    # x = x0 + a + b0*ell + (w)*ell  where w = Im part of cdHi, embedded as high coords
    W = np.zeros(N)
    W[:8] = b[:8]
    Wl = cd(W, ell)
    out = out + c3 * a + s3 * al + (-s3) * W + c3 * Wl
    return out


# verify rho is an automorphism of order 3 fixing ell
w = 0.0
for _ in range(300):
    x, y = rng.normal(size=N), rng.normal(size=N)
    w = max(w, np.linalg.norm(rho(cd(x, y)) - cd(rho(x), rho(y))))
print("rho automorphism residual:", w)
R = np.column_stack([rho(np.eye(N)[i]) for i in range(N)])
print(
    "||rho^3 - I||:",
    np.linalg.norm(np.linalg.matrix_power(R, 3) - np.eye(N)),
    " rho(ell)=ell:",
    np.linalg.norm(rho(ell) - ell),
    " rho != I:",
    np.linalg.norm(R - np.eye(N)),
)
Vr = 0.0
for _ in range(300):
    s = rng.normal(size=N)
    s[0] = 0
    s /= np.linalg.norm(s)
    Vr = max(Vr, abs(V(rho(s)) - V(s)))
print("max |V(rho s) - V(s)|:", Vr)


def lift(o):  # octonion (len 8) -> low half of sedenion
    z = np.zeros(N)
    z[:8] = o
    return z


def subalg_report(basis, tag):
    B = np.linalg.qr(np.array(basis).T)[0].T  # orthonormal rows
    k = np.linalg.matrix_rank(np.array(basis), tol=1e-9)

    def proj(v):
        return B.T @ (B @ v)

    clo = max(np.linalg.norm(cd(a, b) - proj(cd(a, b))) for a in B for b in B)
    rinv = max(np.linalg.norm(rho(a) - proj(rho(a))) for a in B)
    nm, alt, zd = 0.0, 0.0, 1e9
    for _ in range(300):
        cc, dd = rng.normal(size=k), rng.normal(size=k)
        x, y = B.T @ cc, B.T @ dd
        nm = max(
            nm, abs(np.linalg.norm(cd(x, y)) - np.linalg.norm(x) * np.linalg.norm(y))
        )
        alt = max(alt, np.linalg.norm(cd(x, cd(x, y)) - cd(cd(x, x), y)))
        zd = min(zd, np.linalg.norm(cd(x, y)) / (np.linalg.norm(x) * np.linalg.norm(y)))
    print(
        f"{tag:52s} dim={k} closure={clo:.2e} rho-resid={rinv:.2e} normmult={nm:.2e} alt={alt:.2e} min|xy|/|x||y|={zd:.3f}"
    )
    return clo, rinv


# (a) the 7 coordinate-aligned Fano doubles
e = lambda i: np.eye(N)[i]
for i, j, k in FANO:
    H4 = [e(0), e(i), e(j), e(k)]
    base = H4 + [cd(v, ell) for v in H4]
    subalg_report(base, f"Fano double H_{{{i},{j},{k}}} + H*ell")

# (b) a RANDOM (non-coordinate-aligned) quaternion subalgebra of O, doubled
print()
for t in range(5):
    p = np.zeros(8)
    p[1:] = rng.normal(size=7)
    p /= np.linalg.norm(p)
    q = np.zeros(8)
    q[1:] = rng.normal(size=7)
    q -= (q @ p) * p
    q /= np.linalg.norm(q)
    pq = omul_fano(
        p, q
    )  # built with the INDEPENDENT Fano product... must use cd for consistency
    pq = cd(lift(p), lift(q))[:8]
    H4 = [e(0), lift(p), lift(q), lift(pq)]
    base = H4 + [cd(v, ell) for v in H4]
    subalg_report(base, f"random quaternion subalgebra H_rand#{t} doubled by ell")

# (c) does a GENERIC crystal's H_s sit inside a rho-invariant octonion subalgebra?
print("\n--- row 11 test: is H_s contained in a rho-invariant octonion subalgebra? ---")
insideFano, insideAny = 0, 0
for t in range(20):
    s, b0, u7 = random_vacuum(rng)
    u = np.zeros(8)
    u[1:] = u7  # u in Im O_low
    Hs = np.array([e(0), ell, lift(u), cd(lift(u), ell)])
    # (c1) inside one of the 7 coordinate-aligned Fano doubles?
    hit7 = False
    for i, j, k in FANO:
        H4 = [e(0), e(i), e(j), e(k)]
        B = np.linalg.qr(np.array(H4 + [cd(v, ell) for v in H4]).T)[0].T
        if max(np.linalg.norm(v - B.T @ (B @ v)) for v in Hs) < 1e-9:
            hit7 = True
    insideFano += hit7
    # (c2) inside SOME rho-invariant octonion subalgebra: build H = span{1,u,v,uv} for v _|_ u
    vv = np.zeros(8)
    vv[1:] = rng.normal(size=7)
    vv -= (vv @ u) * u
    vv /= np.linalg.norm(vv)
    uv = cd(lift(u), lift(vv))[:8]
    H4 = [e(0), lift(u), lift(vv), lift(uv)]
    base = np.array(H4 + [cd(x, ell) for x in H4])
    B = np.linalg.qr(base.T)[0].T
    clo = max(np.linalg.norm(cd(a, b) - B.T @ (B @ cd(a, b))) for a in B for b in B)
    rin = max(np.linalg.norm(rho(a) - B.T @ (B @ rho(a))) for a in B)
    cont = max(np.linalg.norm(v - B.T @ (B @ v)) for v in Hs)
    insideAny += clo < 1e-9 and rin < 1e-9 and cont < 1e-9
print(f"H_s inside one of the SEVEN coordinate-aligned Fano doubles: {insideFano}/20")
print(f"H_s inside a CONSTRUCTED rho-invariant octonion subalgebra  : {insideAny}/20")

# (d) how big is the family? dimension of the set of quaternion subalgebras of O containing u
print(
    "\n--- family size: distinct rho-invariant octonion subalgebras containing one fixed H_s ---"
)
s, b0, u7 = random_vacuum(rng)
u = np.zeros(8)
u[1:] = u7
subs = []
for t in range(200):
    vv = np.zeros(8)
    vv[1:] = rng.normal(size=7)
    vv -= (vv @ u) * u
    vv /= np.linalg.norm(vv)
    uv = cd(lift(u), lift(vv))[:8]
    H4 = [e(0), lift(u), lift(vv), lift(uv)]
    B = np.linalg.qr(np.array(H4 + [cd(x, ell) for x in H4]).T)[0].T
    P = B.T @ B
    if all(np.linalg.norm(P - Q) > 1e-6 for Q in subs):
        subs.append(P)
print(
    "distinct such subalgebras found from 200 random v:",
    len(subs),
    "(a finite set of 7 would give <= 7)",
)
