"""Pass-2 confirmer numerics: completeness conjecture, family dimensions, CP^2 structure."""

import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(84)


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


def lo(a8):
    z = np.zeros(N)
    z[:8] = a8
    return z


c3, s3 = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)


def rho(x):
    a = np.r_[x[:8], np.zeros(8)]
    a[0] = 0.0
    W = np.zeros(N)
    W[:8] = x[8:]
    W[0] = 0.0
    out = np.zeros(N)
    out[0] = x[0]
    out[8] = x[8]
    return out + c3 * a + s3 * cd(a, ell) + (-s3) * W + c3 * cd(W, ell)


def onb(M):
    Q, _ = np.linalg.qr(np.asarray(M).T)
    return Q[:, : np.linalg.matrix_rank(np.asarray(M), tol=1e-9)].T


def closure(B):
    P = B.T @ B
    return max(np.linalg.norm(cd(a, b) - P @ cd(a, b)) for a in B for b in B)


def unit_im(perp=()):
    a = rng.normal(size=8)
    a[0] = 0
    for p in perp:
        a -= np.dot(a, p) * p
    return a / np.linalg.norm(a)


# ---------- setup: one generic crystal
u = unit_im()
Hs = np.array([e(0), ell, lo(u), cd(lo(u), ell)])
QHs = onb(Hs)
perp = []  # orthonormal basis of Hs^perp inside R^16 (12-dim)
M = np.eye(N) - QHs.T @ QHs
Q, _ = np.linalg.qr(M)
perpB = np.array([q for q in Q.T if np.linalg.norm(QHs @ q) < 1e-9])[:12]
perpB = onb(perpB)
print("dim Hs =", QHs.shape[0], " dim Hs^perp =", perpB.shape[0])


def Ov(v):
    H4 = [e(0), lo(u), lo(v), lo(cd(lo(u), lo(v))[:8])]
    return onb(np.array(H4 + [cd(x, ell) for x in H4]))


print("\n===== (C1) the family for a GENERIC crystal =====")
v0 = unit_im((u,))
P0 = Ov(v0).T @ Ov(v0)
# C_u-line invariance: v and a*v + b*(uv) give the same algebra
uv = cd(lo(u), lo(v0))[:8]
same = 0
for _ in range(20):
    a, b = rng.normal(size=2)
    w = a * v0 + b * uv
    w /= np.linalg.norm(w)
    if np.linalg.norm(Ov(w).T @ Ov(w) - P0) < 1e-9:
        same += 1
print(f"O'_(a v + b uv) == O'_v : {same}/20")
off = sum(
    1
    for _ in range(20)
    if np.linalg.norm(Ov(unit_im((u, v0, uv))).T @ Ov(unit_im((u, v0, uv))) - P0) > 1e-6
)
print(f"v2 off the C_u-line gives a DIFFERENT algebra: {off}/20")
# complex structure: L_u^2 = -1 on u^perp within Im O ?
Lu = np.column_stack([cd(lo(u), lo(np.eye(8)[i]))[:8] for i in range(8)])
basis_uperp = []
for i in range(1, 8):
    x = np.eye(8)[i].copy()
    x -= (x @ u) * u
    basis_uperp.append(x)
Bp = onb(np.array(basis_uperp))
resid = max(np.linalg.norm(Lu @ (Lu @ b) + b) for b in Bp)
print(
    f"L_u^2 = -Id on u-perp (dim {Bp.shape[0]}) residual: {resid:.2e}  -> u-perp is C^3"
)


# tangent dimension of the family {P_v}
def tangent_dim(Pfun, base, sampler, eps=1e-5, k=40):
    Pb = Pfun(base)
    cols = []
    for _ in range(k):
        d = sampler()
        w = base + eps * d
        w /= np.linalg.norm(w)
        cols.append(((Pfun(w) - Pb) / eps).ravel())
    sv = np.linalg.svd(np.array(cols), compute_uv=False)
    return int(np.sum(sv > sv[0] * 1e-6)), sv[:10] / sv[0]


d, sv = tangent_dim(lambda v: Ov(v).T @ Ov(v), v0, lambda: unit_im((u,)))
print(
    f"tangent dimension of the generic family: {d}  (CP^2 => 4)   normalised sv: {np.round(sv[:7],4)}"
)

print("\n===== (C2) the family at the POLE =====")
Hp = np.array([e(0), ell])


def Opole(p, q):
    pq = cd(lo(p), lo(q))[:8]
    H4 = [e(0), lo(p), lo(q), lo(pq)]
    return onb(np.array(H4 + [cd(x, ell) for x in H4]))


p0 = unit_im()
q0 = unit_im((p0,))
Pp = Opole(p0, q0).T @ Opole(p0, q0)
print(
    "closure:",
    f"{closure(Opole(p0,q0)):.2e}",
    " rho-resid:",
    f"{max(np.linalg.norm(rho(b)-Pp@rho(b)) for b in Opole(p0,q0)):.2e}",
    " contains span{1,ell}:",
    f"{max(np.linalg.norm(z-Pp@z) for z in Hp):.2e}",
)
cols = []
for _ in range(80):
    dp = unit_im()
    dq = unit_im()
    pp = p0 + 1e-5 * dp
    pp /= np.linalg.norm(pp)
    qq = q0 + 1e-5 * dq
    qq -= (qq @ pp) * pp
    qq /= np.linalg.norm(qq)
    cols.append(((Opole(pp, qq).T @ Opole(pp, qq) - Pp) / 1e-5).ravel())
sv = np.linalg.svd(np.array(cols), compute_uv=False)
print(
    f"tangent dimension of the POLE family: {int(np.sum(sv>sv[0]*1e-6))}  (claimed 8; Gr_3(7) would be 12)  sv/sv0: {np.round(sv[:12]/sv[0],4)}"
)

print(
    "\n===== (B) COMPLETENESS CONJECTURE: search for O superset Hs, O NOT of the H+H*ell form ====="
)


# parametrise O = Hs + W, W a 4-dim subspace of Hs^perp (12-dim): 4x12 params
def build(x):
    W = x.reshape(4, 12) @ perpB
    return onb(np.vstack([QHs, W]))


def cost(x):
    B = build(x)
    if B.shape[0] != 8:
        return 1e3
    P = B.T @ B
    s = 0.0
    for a in B:
        for b in B:
            r = cd(a, b)
            s += np.sum((r - P @ r) ** 2)
    return s


found = []
for trial in range(60):
    x0 = rng.normal(size=48)
    r = minimize(
        cost,
        x0,
        method="L-BFGS-B",
        options={"maxiter": 800, "ftol": 1e-18, "gtol": 1e-14},
    )
    if r.fun < 1e-12:
        B = build(r.x)
        P = B.T @ B
        found.append(P)
print(
    f"closed 8-dim subalgebras containing H_s found: {len(found)}/60 restarts (residual < 1e-12)"
)
# classify each: is it O'_v for some v?  test dim(O cap O_low) and rho-invariance
lowP = np.zeros((N, N))
lowP[:8, :8] = np.eye(8)
cnt_ok = cnt_bad = 0
examples = []
for P in found:
    B = onb(np.array([P @ e(i) for i in range(N)]))
    dl = int(
        round(np.trace(lowP @ P))
    )  # dim of O cap O_low (P and lowP commute iff graded)
    graded = np.linalg.norm(P @ lowP - lowP @ P) < 1e-7
    rinv = max(np.linalg.norm(rho(b) - P @ rho(b)) for b in B)
    # is it exactly some O'_v?  v = a unit vector in (O cap O_low) perp to u
    ok = False
    if graded and dl == 4:
        Ol = onb(np.array([(lowP @ P) @ e(i) for i in range(8)] + [np.zeros(N)]))
        for _ in range(30):
            vv = Ol.T @ rng.normal(size=Ol.shape[0])
            vv = vv[:8]
            vv[0] = 0
            if np.linalg.norm(vv) < 1e-8:
                continue
            vv -= (vv @ u) * u
            if np.linalg.norm(vv) < 1e-8:
                continue
            vv /= np.linalg.norm(vv)
            if np.linalg.norm(Ov(vv).T @ Ov(vv) - P) < 1e-7:
                ok = True
                break
    if ok:
        cnt_ok += 1
    else:
        cnt_bad += 1
        examples.append((graded, dl, rinv))
print(f"  of these: {cnt_ok} are exactly some O'_v ;  {cnt_bad} are NOT")
for g, dl, ri in examples[:6]:
    print(
        f"    NON-O'_v candidate: CD-graded={g}  dim(O cap O_low)={dl}  rho-residual={ri:.2e}"
    )
