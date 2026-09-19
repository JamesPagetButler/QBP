import numpy as np, sys
from scipy.optimize import minimize

rng = np.random.default_rng(87)


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
Rm[:, 0] = e(0)
Rm[:, 8] = ell
for k in range(1, 8):
    a = e(k)
    Rm[:, k] = c3 * a + s3 * cd(a, ell)
    Wl = cd(a, ell)
    idx = int(np.argmax(np.abs(Wl)))
    Rm[:, idx] = ((-s3) * a + c3 * Wl) * np.sign(Wl[idx])
rho = lambda x: Rm @ x


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
U = lo(u)
Ul = cd(U, ell)
HsB = np.array([e(0), ell, U, Ul])
QHs = onb(HsB)
Q, _ = np.linalg.qr(np.eye(N) - QHs.T @ QHs)
perpB = onb(np.array([q for q in Q.T if np.linalg.norm(QHs @ q) < 1e-9])[:12])
print("dim Hs^perp =", perpB.shape[0])
sys.stdout.flush()
# is Hs^perp a left Hs-module?
print(
    "left Hs-module residual on Hs^perp:",
    f"{max(np.linalg.norm(cd(g,w)-(np.eye(N)-QHs.T@QHs)@cd(g,w)) for g in [U,ell,Ul] for w in perpB):.2e}",
)
sys.stdout.flush()


def Wline(w):
    return onb(np.array([w, cd(U, w), cd(ell, w), cd(Ul, w)]))


def Ofrom(w):
    Wl_ = Wline(w)
    if Wl_.shape[0] != 4:
        return None
    return onb(np.vstack([QHs, Wl_]))


def resid(B):
    P = B.T @ B
    pr = np.einsum("ai,bj,ijk->abk", B, B, T)
    return float(np.sum((pr - np.einsum("abk,kl->abl", pr, P)) ** 2))


def cost(x):
    w = x @ perpB
    n = np.linalg.norm(w)
    if n < 1e-6:
        return 1e3
    B = Ofrom(w / n)
    return 1e3 if (B is None or B.shape[0] != 8) else resid(B)


def Ov(v):
    H4 = [e(0), U, lo(v), lo(cd(U, lo(v))[:8])]
    return onb(np.array(H4 + [cd(x, ell) for x in H4]))


# random scan of the landscape
sc = [cost(rng.normal(size=12)) for _ in range(3000)]
print(
    f"random w in Hs-perp: closure resid^2  min={min(sc):.3e} median={np.median(sc):.3e}  -> generic w does NOT close"
)
sys.stdout.flush()
print("\n--- optimisation over the H_s-line space (~HP^2, 8 real dims) ---")
sys.stdout.flush()
found = []
for t in range(400):
    r = minimize(
        cost,
        rng.normal(size=12),
        method="Nelder-Mead",
        options={"maxiter": 4000, "xatol": 1e-12, "fatol": 1e-20},
    )
    if r.fun < 1e-16:
        w = r.x @ perpB
        w /= np.linalg.norm(w)
        B = Ofrom(w)
        if B is not None and B.shape[0] == 8:
            found.append(B.T @ B)
print(f"closed 8-dim subalgebras found: {len(found)}/400 restarts")
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
        for _ in range(60):
            vv = ((lowP @ P) @ rng.normal(size=N))[:8]
            vv[0] = 0
            if np.linalg.norm(vv) < 1e-7:
                continue
            vv -= (vv @ u) * u
            if np.linalg.norm(vv) < 1e-7:
                continue
            vv /= np.linalg.norm(vv)
            if np.linalg.norm(Ov(vv).T @ Ov(vv) - P) < 1e-6:
                isOv = True
                break
    if isOv:
        ok += 1
    else:
        bad += 1
        ex.append((graded, round(dl, 4), rr))
print(f"  exactly some O'_v: {ok} ;  NOT of that form: {bad}")
for g, dl, rr in ex[:10]:
    print(f"    NON-O'_v: CD-graded={g} dim(O∩O_low)={dl} rho-resid={rr:.2e}")
