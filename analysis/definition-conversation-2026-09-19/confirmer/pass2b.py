import numpy as np, sys
from scipy.optimize import minimize

rng = np.random.default_rng(84)


def conj(x):
    y = -x.astype(float).copy()
    y[0] = x[0]
    return y


def cdr(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate([cdr(a, c) - cdr(conj(d), b), cdr(d, a) + cdr(b, conj(c))])


N = 16
T = np.zeros((N, N, N))
for i in range(N):
    for j in range(N):
        T[i, j] = cdr(np.eye(N)[i], np.eye(N)[j])


def cd(x, y):
    return np.einsum("i,j,ijk->k", x, y, T)


e = lambda i: np.eye(N)[i]
ell = e(8)


def lo(a8):
    z = np.zeros(N)
    z[:8] = a8
    return z


c3, s3 = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)
Rm = np.zeros((N, N))


def rho_build():
    M = np.zeros((N, N))
    M[:, 0] = e(0)
    M[:, 8] = ell
    for k in range(1, 8):
        a = e(k)
        al = cd(a, ell)
        M[:, k] = c3 * a + s3 * al
        W = e(k + 8 - 8 + 8)  # placeholder
    return M


# build rho as a matrix from the basis-free rule
Rm = np.zeros((N, N))
Rm[:, 0] = e(0)
Rm[:, 8] = ell
for k in range(1, 8):
    a = e(k)
    Rm[:, k] = c3 * a + s3 * cd(a, ell)
for k in range(1, 8):
    # basis of the high imaginary part: e_{8+k} = W*ell with W=e_k
    W = e(k)
    Wl = cd(W, ell)
    col = (-s3) * W + c3 * Wl
    idx = int(np.argmax(np.abs(Wl)))
    Rm[:, idx] = col * np.sign(Wl[idx])
rho = lambda x: Rm @ x
print(
    "rho auto residual:",
    max(
        np.linalg.norm(rho(cd(x, y)) - cd(rho(x), rho(y)))
        for x, y in [(rng.normal(size=N), rng.normal(size=N)) for _ in range(100)]
    ),
)
print(
    "rho^3=I:",
    np.linalg.norm(np.linalg.matrix_power(Rm, 3) - np.eye(N)),
    " rho(ell)=ell:",
    np.linalg.norm(rho(ell) - ell),
)
sys.stdout.flush()


def onb(M):
    M = np.asarray(M)
    Q, _ = np.linalg.qr(M.T)
    r = np.linalg.matrix_rank(M, tol=1e-9)
    return Q[:, :r].T


def unit_im(perp=()):
    a = rng.normal(size=8)
    a[0] = 0
    for p in perp:
        a -= np.dot(a, p) * p
    return a / np.linalg.norm(a)


u = unit_im()
Hs = np.array([e(0), ell, lo(u), cd(lo(u), ell)])
QHs = onb(Hs)
Q, _ = np.linalg.qr(np.eye(N) - QHs.T @ QHs)
perpB = onb(np.array([q for q in Q.T if np.linalg.norm(QHs @ q) < 1e-9])[:12])


def Ov(v):
    H4 = [e(0), lo(u), lo(v), lo(cd(lo(u), lo(v))[:8])]
    return onb(np.array(H4 + [cd(x, ell) for x in H4]))


def Pof(B):
    return B.T @ B


print("\n===== (C1) generic family =====")
sys.stdout.flush()
v0 = unit_im((u,))
P0 = Pof(Ov(v0))
uv = cd(lo(u), lo(v0))[:8]
same = sum(
    1
    for _ in range(20)
    if np.linalg.norm(
        Pof(
            Ov((lambda w: w / np.linalg.norm(w))(rng.normal() * v0 + rng.normal() * uv))
        )
        - P0
    )
    < 1e-9
)
off = sum(
    1 for _ in range(20) if np.linalg.norm(Pof(Ov(unit_im((u, v0, uv)))) - P0) > 1e-6
)
rinv = max(np.linalg.norm(rho(b) - P0 @ rho(b)) for b in Ov(v0))
print(
    f"O'_(a v+b uv)=O'_v: {same}/20 ; v2 off the line differs: {off}/20 ; rho-invariant: {rinv:.2e}"
)
Lu = np.column_stack([cd(lo(u), lo(np.eye(8)[i]))[:8] for i in range(8)])
Bp = onb(np.array([(lambda x: x - (x @ u) * u)(np.eye(8)[i]) for i in range(1, 8)]))
print(
    f"L_u^2=-Id on u-perp (dim {Bp.shape[0]}): {max(np.linalg.norm(Lu@(Lu@b)+b) for b in Bp):.2e}  -> u-perp is C^3"
)
cols = []
for _ in range(60):
    d = unit_im((u,))
    w = v0 + 1e-5 * d
    w /= np.linalg.norm(w)
    cols.append(((Pof(Ov(w)) - P0) / 1e-5).ravel())
sv = np.linalg.svd(np.array(cols), compute_uv=False)
print(
    f"generic family tangent dim = {int(np.sum(sv>sv[0]*1e-6))}  (CP^2 => 4)  sv/sv0={np.round(sv[:7]/sv[0],5)}"
)
sys.stdout.flush()

print("\n===== (C2) pole family =====")
sys.stdout.flush()


def Opole(p, q):
    H4 = [e(0), lo(p), lo(q), lo(cd(lo(p), lo(q))[:8])]
    return onb(np.array(H4 + [cd(x, ell) for x in H4]))


p0 = unit_im()
q0 = unit_im((p0,))
Bp0 = Opole(p0, q0)
Pp = Pof(Bp0)
print(
    f"closure {max(np.linalg.norm(cd(a,b)-Pp@cd(a,b)) for a in Bp0 for b in Bp0):.2e}  rho {max(np.linalg.norm(rho(b)-Pp@rho(b)) for b in Bp0):.2e}  contains span(1,ell) {max(np.linalg.norm(z-Pp@z) for z in [e(0),ell]):.2e}"
)
cols = []
for _ in range(120):
    pp = p0 + 1e-5 * unit_im()
    pp /= np.linalg.norm(pp)
    qq = q0 + 1e-5 * unit_im()
    qq -= (qq @ pp) * pp
    qq /= np.linalg.norm(qq)
    cols.append(((Pof(Opole(pp, qq)) - Pp) / 1e-5).ravel())
sv = np.linalg.svd(np.array(cols), compute_uv=False)
print(
    f"pole family tangent dim = {int(np.sum(sv>sv[0]*1e-6))}  (claimed 8; Gr_3(7) would be 12)  sv/sv0={np.round(sv[:13]/sv[0],5)}"
)
sys.stdout.flush()

print(
    "\n===== (B) completeness search: closed 8-dim O with H_s < O, O not of the H+H*ell form ====="
)
sys.stdout.flush()


def cost(x):
    W = x.reshape(4, 12) @ perpB
    B = onb(np.vstack([QHs, W]))
    if B.shape[0] != 8:
        return 1e3
    P = B.T @ B
    prod = np.einsum("ai,bj,ijk->abk", B, B, T)
    res = prod - np.einsum("abk,kl->abl", prod, P)
    return float(np.sum(res**2))


found = []
for trial in range(200):
    r = minimize(
        cost,
        rng.normal(size=48),
        method="L-BFGS-B",
        options={"maxiter": 600, "ftol": 1e-20, "gtol": 1e-16},
    )
    if r.fun < 1e-14:
        W = r.x.reshape(4, 12) @ perpB
        B = onb(np.vstack([QHs, W]))
        if B.shape[0] == 8:
            found.append(B.T @ B)
print(f"converged closed subalgebras: {len(found)}/200 restarts (residual^2 < 1e-14)")
sys.stdout.flush()
lowP = np.zeros((N, N))
lowP[:8, :8] = np.eye(8)
ok = bad = 0
ex = []
for P in found:
    B = onb(np.array([P @ e(i) for i in range(N)]))
    graded = np.linalg.norm(P @ lowP - lowP @ P) < 1e-6
    dl = float(np.trace(lowP @ P))
    rr = max(np.linalg.norm(rho(b) - P @ rho(b)) for b in B)
    isOv = False
    if graded and abs(dl - 4) < 1e-3:
        Ol = lowP @ P
        for _ in range(40):
            vv = (Ol @ rng.normal(size=N))[:8]
            vv[0] = 0
            if np.linalg.norm(vv) < 1e-7:
                continue
            vv -= (vv @ u) * u
            if np.linalg.norm(vv) < 1e-7:
                continue
            vv /= np.linalg.norm(vv)
            if np.linalg.norm(Pof(Ov(vv)) - P) < 1e-6:
                isOv = True
                break
    if isOv:
        ok += 1
    else:
        bad += 1
        ex.append((graded, round(dl, 3), rr))
print(f"  exactly some O'_v: {ok}   NOT of that form: {bad}")
for g, dl, rr in ex[:8]:
    print(f"    NON-O'_v: CD-graded={g} dim(O cap O_low)={dl} rho-resid={rr:.2e}")
