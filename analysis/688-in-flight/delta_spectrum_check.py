import numpy as np

rng = np.random.default_rng(688)


# Cayley-Dickson doubling (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c)), gamma=-1
def conj(x):
    y = -x.copy()
    y[0] = x[0]
    return y


def mul(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b = x[:h], x[h:]
    c, d = y[:h], y[h:]
    return np.concatenate([mul(a, c) - mul(conj(d), b), mul(d, a) + mul(b, conj(c))])


E = np.eye(16)


def L(s):
    return np.column_stack([mul(s, E[:, k]) for k in range(16)])


def Delta(s):  # Delta(s)x = s(sx) + N(s) x
    Ls = L(s)
    return Ls @ Ls + (s @ s) * np.eye(16)


def V(s):
    a, b = s[:8], s[8:]
    c = mul(a, b) - mul(b, a)
    return c @ c


def randstate():
    s = rng.normal(size=16)
    s[0] = 0
    return s / np.linalg.norm(s)


print("check imaginary_sq: s*s = -N(s):", end=" ")
s = randstate()
print(np.allclose(mul(s, s), -np.eye(16)[:, 0]))
print(
    "\n V        skew?   rank  kerdim  nonzero-eig-moduli (unique)          max|Δ³ - VΔ|   tr(Δ²)+8V"
)
for _ in range(8):
    s = randstate()
    D = Delta(s)
    v = V(s)
    ev = np.linalg.eigvals(D)
    mods = np.unique(np.round(np.abs(ev), 6))
    skew = np.allclose(D, -D.T, atol=1e-10)
    rk = np.linalg.matrix_rank(D, tol=1e-9)
    t2b = np.max(np.abs(D @ D @ D - v * D))
    print(
        f"{v:.5f}   {skew}   {rk:2d}   {16-rk:2d}   {mods}  sqrtV={np.sqrt(v):.6f}   {t2b:.2e}   {np.trace(D@D)+8*v:.2e}"
    )
# ridge point (zero divisor): s=(e1+e10)/sqrt2 -> V=1
s = np.zeros(16)
s[1] = 1
s[10] = 1
s /= np.sqrt(2)
D = Delta(s)
v = V(s)
print(
    "\nridge s=(e1+e10)/√2: V=",
    round(v, 6),
    " rank",
    np.linalg.matrix_rank(D, tol=1e-9),
    " |eig|",
    np.unique(np.round(np.abs(np.linalg.eigvals(D)), 6)),
    " |Δ³-VΔ|",
    np.max(np.abs(D @ D @ D - v * D)),
)
# operator-norm bound: ||Δ(s)||_op vs sqrt(V)
print("\n||Δ||_op / sqrt(V) over 200 random states: min,max =", end=" ")
r = []
for _ in range(200):
    s = randstate()
    D = Delta(s)
    v = V(s)
    r.append(np.linalg.norm(D, 2) / np.sqrt(v))
print(round(min(r), 8), round(max(r), 8))


# rank of the differential of s -> Delta(s) restricted to the tangent space at random in-flight s
def tangent_basis(s):
    # tangent to sphere within imaginary part: orthonormal complement of {s, e0} in R^16
    M = np.column_stack([s, E[:, 0]])
    Q, _ = np.linalg.qr(np.column_stack([M, rng.normal(size=(16, 16))]))
    return Q[:, 2:16]


print("\nrank of dΔ|_T (14 tangent dirs) at random in-flight states:", end=" ")
rks = []
for _ in range(5):
    s = randstate()
    T = tangent_basis(s)
    h = 1e-6
    J = np.column_stack(
        [
            ((Delta(s + h * T[:, i]) - Delta(s - h * T[:, i])) / (2 * h)).ravel()
            for i in range(14)
        ]
    )
    rks.append(np.linalg.matrix_rank(J, tol=1e-6))
print(rks)
# and at a vacuum (e.g. s = e1): rank of dΔ
s = E[:, 1]
T = tangent_basis(s)
h = 1e-6
J = np.column_stack(
    [
        ((Delta(s + h * T[:, i]) - Delta(s - h * T[:, i])) / (2 * h)).ravel()
        for i in range(14)
    ]
)
print(
    "rank of dΔ|_T at the vacuum e1:",
    np.linalg.matrix_rank(J, tol=1e-6),
    "(vacuum manifold has dim 8, so expect 14-8=6 if Δ is 'first order transverse')",
)


# does the spectrum see anything beyond V? compare two states with equal V but different (A,C,P,b0^2)
def invariants(s):
    a, b = s[:8], s[8:]
    bi = b.copy()
    bi[0] = 0
    return a @ a, bi @ bi, a @ bi, b[0] ** 2


print(
    "\ntwo states on one level set (V matched by bisection along a path), invariants and eigenvalue moduli:"
)
s1 = randstate()
v1 = V(s1)
# find s2 with V(s2)=v1 along segment between two random states
p, q = randstate(), randstate()


def Vt(t):
    x = (1 - t) * p + t * q
    x /= np.linalg.norm(x)
    return V(x), x


lo, hi = 0.0, 1.0
flo = Vt(lo)[0] - v1
fhi = Vt(hi)[0] - v1
if flo * fhi > 0:
    ts = np.linspace(0, 1, 2001)
    vals = [Vt(t)[0] - v1 for t in ts]
    i = np.argmax(np.sign(vals[:-1]) != np.sign(vals[1:]))
    lo, hi = ts[i], ts[i + 1]
for _ in range(60):
    m = (lo + hi) / 2
    if (Vt(lo)[0] - v1) * (Vt(m)[0] - v1) <= 0:
        hi = m
    else:
        lo = m
s2 = Vt((lo + hi) / 2)[1]
for s in (s1, s2):
    D = Delta(s)
    print(
        f"  V={V(s):.8f} (A,C,P,b0²)={tuple(round(x,4) for x in invariants(s))} |eig|={np.unique(np.round(np.abs(np.linalg.eigvals(D)),6))}"
    )

print("\n--- extra: symmetry, eigenvalue signs, null directions of dΔ ---")
s = randstate()
D = Delta(s)
v = V(s)
print(
    "Δ symmetric?",
    np.allclose(D, D.T, atol=1e-10),
    " eigenvalues (real parts, sorted):",
    np.round(np.sort(np.linalg.eigvals(D).real), 5),
)
T = tangent_basis(s)
h = 1e-6
J = np.column_stack(
    [
        ((Delta(s + h * T[:, i]) - Delta(s - h * T[:, i])) / (2 * h)).ravel()
        for i in range(14)
    ]
)
U, S, Wt = np.linalg.svd(J)
print("singular values of dΔ|_T:", np.round(S, 4))
null = T @ Wt[11:].T  # 3 null directions in R^16
ell = E[:, 8]
for k in range(3):
    n = null[:, k] / np.linalg.norm(null[:, k])
    print(
        f" null dir {k}: |lo-half|={np.linalg.norm(n[:8]):.3f} |hi-half|={np.linalg.norm(n[8:]):.3f} <n,ℓ>={n@ell:.3f}  dV·n={((V(s+h*n)-V(s-h*n))/(2*h)):.1e}"
    )
# is the (a,-b) rescaling direction (projected to T) null? and is the ℓ (b0) direction null?
a_mb = np.concatenate([s[:8], -s[8:]])
a_mb -= (a_mb @ s) * s
a_mb /= np.linalg.norm(a_mb)
lp = ell - (ell @ s) * s
lp /= np.linalg.norm(lp)
for name, d in (("(a,-b)⊥", a_mb), ("ℓ⊥", lp)):
    dd = (Delta(s + h * d) - Delta(s - h * d)) / (2 * h)
    print(f" |dΔ[{name}]| = {np.linalg.norm(dd):.3e}")
# Gauge check: G2 acts by conjugation on Δ -> spectrum constant; also confirm N(s)!=1 T2b: T^3 = V T
s2 = 2.5 * randstate()
D2 = L(s2) @ L(s2) + (s2 @ s2) * np.eye(16)
print(" off-sphere Δ³-VΔ:", np.max(np.abs(D2 @ D2 @ D2 - V(s2) * D2)))

print("\n--- Δ as a function of a∧Im b ---")
a = rng.normal(size=8)
a[0] = 0
c = rng.normal(size=8)
c[0] = 0


def S(a, c, b0):
    b = c.copy()
    b[0] = b0
    return np.concatenate([a, b])


def Dl(s):
    return L(s) @ L(s) + (s @ s) * np.eye(16)


D0 = Dl(S(a, c, 0.3))
print(
    " change b0 only (0.3->-0.9):        max|ΔΔ| =",
    np.max(np.abs(Dl(S(a, c, -0.9)) - D0)),
)
print(
    " shear (a,c)->(a+0.7c, c):          max|ΔΔ| =",
    np.max(np.abs(Dl(S(a + 0.7 * c, c, 0.3)) - D0)),
)
print(
    " shear (a,c)->(a, c-1.3a):          max|ΔΔ| =",
    np.max(np.abs(Dl(S(a, c - 1.3 * a, 0.3)) - D0)),
)
print(
    " scale (a,c)->(2a, c/2):            max|ΔΔ| =",
    np.max(np.abs(Dl(S(2 * a, c / 2, 0.3)) - D0)),
)
print(
    " control: (a,c)->(a, 1.1c):         max|ΔΔ| =",
    np.max(np.abs(Dl(S(a, 1.1 * c, 0.3)) - D0)),
)

print("\n--- the 8-dim kernel of Δ(s) in flight ---")
for trial in range(3):
    s = randstate()
    D = Delta(s)
    w, Vv = np.linalg.eigh(D)
    K = Vv[:, np.abs(w) < 1e-9]
    P = K @ K.T

    def inK(x):
        return np.linalg.norm(P @ x - x) < 1e-8

    a, b = s[:8], s[8:]
    c = b.copy()
    c[0] = 0
    A = np.concatenate([a, np.zeros(8)])
    Cc = np.concatenate([c, np.zeros(8)])
    AC = np.concatenate([mul(a, c), np.zeros(8)])
    print(
        f" trial {trial}: dim ker={K.shape[1]}  1∈ker:{inK(E[:,0])} s∈ker:{inK(s)} ℓ∈ker:{inK(E[:,8])} a∈ker:{inK(A)} Im b∈ker:{inK(Cc)} a·Im b∈ker:{inK(AC)}",
        end=" ",
    )
    closed = all(inK(mul(K[:, i], K[:, j])) for i in range(8) for j in range(8))
    print(" subalgebra:", closed)
    # is ker = H ⊕ Hℓ for H=span{1,a,c,ac} ⊂ O ?
    H = np.column_stack([E[:, 0], A, Cc, AC])
    Hl = np.column_stack([mul(H[:, i], E[:, 8]) for i in range(4)])
    B = np.column_stack([H, Hl])
    print(
        "   ker == span{1,a,c,ac} ⊕ span{1,a,c,ac}·ℓ ?",
        np.linalg.matrix_rank(np.column_stack([K, B]), tol=1e-8) == 8,
    )

print("\n--- in flight: is span{1,s,ℓ,sℓ} a 4-dim associative subalgebra? ---")
for trial in range(3):
    s = randstate()
    l = E[:, 8]
    sl = mul(s, l)
    B = np.column_stack([E[:, 0], s, l, sl])
    r = np.linalg.matrix_rank(B, tol=1e-9)
    Pb = B @ np.linalg.pinv(B)
    closed = all(
        np.linalg.norm(Pb @ mul(B[:, i], B[:, j]) - mul(B[:, i], B[:, j])) < 1e-9
        for i in range(4)
        for j in range(4)
    )
    assoc_ok = all(
        np.linalg.norm(
            mul(mul(B[:, i], B[:, j]), B[:, k]) - mul(B[:, i], mul(B[:, j], B[:, k]))
        )
        < 1e-9
        for i in range(4)
        for j in range(4)
        for k in range(4)
    )
    print(
        f" trial {trial}: V={V(s):.3f} dim span={r} closed={closed} associative={assoc_ok}  s·ℓ = -ℓ·s? {np.allclose(mul(s,l),-mul(l,s))}  (sℓ)²=-1? {np.allclose(mul(sl,sl),-E[:,0])}"
    )
