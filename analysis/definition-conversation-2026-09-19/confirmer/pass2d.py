import numpy as np, sys, time
from scipy.optimize import minimize

rng = np.random.default_rng(871)


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


def q8(M):  # orthonormal rows, no rank call
    Q, _ = np.linalg.qr(np.asarray(M).T)
    return Q.T


def unit_im(perp=()):
    a = rng.normal(size=8)
    a[0] = 0
    for p in perp:
        a -= np.dot(a, p) * p
    return a / np.linalg.norm(a)


u = unit_im()
U = lo(u)
Ul = cd(U, ell)
QHs = q8([e(0), ell, U, Ul])
PHs = QHs.T @ QHs
Q, _ = np.linalg.qr(np.eye(N) - PHs)
perpB = q8(np.array([q for q in Q.T if np.linalg.norm(QHs @ q) < 1e-9])[:12])
LU, LL, LUl = [np.column_stack([cd(g, e(i)) for i in range(N)]) for g in (U, ell, Ul)]


def OfromW(w):
    W = np.array([w, LU @ w, LL @ w, LUl @ w])
    B = np.vstack([QHs, W])
    Q2, R2 = np.linalg.qr(B.T)
    if np.min(np.abs(np.diag(R2)[:8])) < 1e-7:
        return None
    return Q2[:, :8].T


def resid(B):
    P = B.T @ B
    pr = np.einsum("ai,bj,ijk->abk", B, B, T)
    return float(np.sum((pr - np.einsum("abk,kl->abl", pr, P)) ** 2))


def cost(x):
    w = x @ perpB
    n = np.linalg.norm(w)
    if n < 1e-6:
        return 1e3
    B = OfromW(w / n)
    return 1e3 if B is None else resid(B)


def Ov(v):
    H4 = [e(0), U, lo(v), lo(cd(U, lo(v))[:8])]
    return q8(np.array(H4 + [cd(x, ell) for x in H4]))


t0 = time.time()
found = []
nconv = 0
NR = 120
for t in range(NR):
    r = minimize(
        cost,
        rng.normal(size=12),
        method="L-BFGS-B",
        options={"maxiter": 400, "ftol": 1e-20, "gtol": 1e-16},
    )
    if r.fun < 1e-16:
        nconv += 1
        w = r.x @ perpB
        w /= np.linalg.norm(w)
        B = OfromW(w)
        if B is not None:
            found.append(B.T @ B)
    if (t + 1) % 20 == 0:
        print(
            f"  restart {t+1}/{NR}  converged so far {nconv}  ({time.time()-t0:.0f}s)"
        )
        sys.stdout.flush()
print(f"closed 8-dim subalgebras found: {len(found)}/{NR} restarts")
sys.stdout.flush()
lowP = np.zeros((N, N))
lowP[:8, :8] = np.eye(8)
ok = bad = 0
ex = []
for P in found:
    B = (
        q8(np.array([P @ e(i) for i in range(N)])[:8])
        if False
        else q8(np.linalg.svd(P)[0][:, :8].T)
    )
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
            Bv = Ov(vv)
            if np.linalg.norm(Bv.T @ Bv - P) < 1e-6:
                isOv = True
                break
    if isOv:
        ok += 1
    else:
        bad += 1
        ex.append((graded, round(dl, 4), rr))
print(f"  exactly some O'_v: {ok} ;  NOT of that form: {bad}")
for g, dl, rr in ex[:10]:
    print(f"    NON-O'_v: CD-graded={g} dim(O cap O_low)={dl} rho-resid={rr:.2e}")
