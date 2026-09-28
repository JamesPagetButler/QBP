"""Round-4 numerics (Red Team, #688): stabiliser count, Hessian isotropy + cubic anisotropy, exceptional-divisor
endpoint map, Fix(Stab(s)) = O_s = ker Delta(s), flow confinement to O_s, SU(3)-relative invariants.
CD doubling convention = repo's (flowlib / delta_spectrum_check)."""

import numpy as np
from flowlib import mul, conj, potential, ruleField

rng = np.random.default_rng(6884)
E8 = np.eye(8)
E16 = np.eye(16)


def L16(s):
    return np.column_stack([mul(s, E16[:, k]) for k in range(16)])


def Delta(s):
    Ls = L16(s)
    return Ls @ Ls + (s @ s) * np.eye(16)


V = lambda s: float(potential(s))


def randstate():
    s = rng.normal(size=16)
    s[0] = 0
    return s / np.linalg.norm(s)


def cross(a, c):  # imaginary part of a*c for imaginary a,c  (= (ac-ca)/2)
    return (mul(a, c) - mul(c, a)) / 2


# ---------- g2 = Der(O) ----------
rows = []
for i in range(8):
    for j in range(8):
        M = np.zeros((8, 64))
        prod = mul(E8[:, i], E8[:, j])
        for k in range(8):
            for m in range(8):
                Dk = np.zeros((8, 8))
                Dk[k, m] = 1
                M[:, k * 8 + m] = (
                    Dk @ prod
                    - mul(Dk @ E8[:, i], E8[:, j])
                    - mul(E8[:, i], Dk @ E8[:, j])
                )
        rows.append(M)
_, S, Wt = np.linalg.svd(np.vstack(rows))
g2 = [v.reshape(8, 8) for v in Wt[np.sum(S > 1e-10) :]]


def hat(D):
    Z = np.zeros((16, 16))
    Z[:8, :8] = D
    Z[8:, 8:] = D
    return Z


def stab_of(vectors):
    K = np.vstack([np.array([D @ v for D in g2]).T for v in vectors])  # (8k) x 14
    _, Sk, Wk = np.linalg.svd(K)
    r = np.sum(Sk > 1e-10)
    return [sum(c * D for c, D in zip(Wk[k], g2)) for k in range(r, 14)]


print("dim g2 =", len(g2))
# ---------- 1. stabiliser of a crystal ----------
u = rng.normal(size=8)
u[0] = 0
u /= np.linalg.norm(u)
su3 = stab_of([u])
print("dim Stab_g2(u) =", len(su3), "(SU(3) has dim 8)")
al, ga = 0.5, 0.6
b0 = np.sqrt(1 - al * al - ga * ga)


def crystal(u, al, ga, b0):
    return np.concatenate([al * u, b0 * E8[:, 0] + ga * u])


s0 = crystal(u, al, ga, b0)
print("V(s0)=%.1e" % V(s0))
print(
    "  su(3) kills s0:",
    all(np.allclose(hat(D) @ s0, 0) for D in su3),
    "| fixes H_s0=span{1,u,l,ul} pointwise:",
    all(
        np.allclose(hat(D) @ w, 0)
        for D in su3
        for w in [
            E16[:, 0],
            np.r_[u, np.zeros(8)],
            E16[:, 8],
            mul(np.r_[u, np.zeros(8)], E16[:, 8]),
        ]
    ),
)
# SO(4) = stabiliser of the quaternion SUBALGEBRA H=span{1,u,v,uv} (setwise): derivations D with D(H) ⊆ H
v = rng.normal(size=8)
v[0] = 0
v -= (v @ u) * u
v /= np.linalg.norm(v)
uv = mul(u, v)
Hb = np.column_stack([E8[:, 0], u, v, uv])
PH = Hb @ Hb.T
Pperp = np.eye(8) - PH
K = np.vstack([Pperp @ D @ Hb for D in g2]).reshape(14, -1).T
_, Sk, Wk = np.linalg.svd(K)
so4 = [sum(c * D for c, D in zip(Wk[k], g2)) for k in range(np.sum(Sk > 1e-10), 14)]
print(
    "  dim {D in g2 : D(H) ⊆ H} =",
    len(so4),
    "(SO(4) has dim 6) -- a different object from Stab(u)",
)
# orbit ranks on a level set
print(
    "  random in-flight s: rank of su(3)-orbit | g2-orbit  (level set dim 13):",
    [
        (
            np.linalg.matrix_rank(np.array([hat(D) @ s for D in su3]).T, tol=1e-9),
            np.linalg.matrix_rank(np.array([hat(D) @ s for D in g2]).T, tol=1e-9),
        )
        for s in [randstate() for _ in range(4)]
    ],
)


# ---------- 2. which functions are the SU(3)-relative invariants? ----------
def invs(s):
    a, b = s[:8], s[8:]
    c = b.copy()
    c[0] = 0
    return np.array([b[0], a @ a, c @ c, a @ c, a @ u, c @ u, u @ cross(a, c)])


def tangent(s):
    Q, _ = np.linalg.qr(np.column_stack([s, E16[:, 0], rng.normal(size=(16, 16))]))
    return Q[:, 2:16]


s = randstate()
T = tangent(s)
h = 1e-6
J = np.column_stack(
    [(invs(s + h * T[:, i]) - invs(s - h * T[:, i])) / (2 * h) for i in range(14)]
)  # 7 x 14
print(
    "rank of d(b0,|a|²,|c|²,<a,c>,<a,u>,<c,u>,<u,a×c>) on the 14-dim tangent:",
    np.linalg.matrix_rank(J, tol=1e-6),
    "(expect 6: one relation |a|²+|c|²+b0²=1)",
)
orb = np.array([hat(D) @ s for D in su3]).T
print(
    "  su(3)-orbit directions annihilated by dInvs:",
    np.max(np.abs(J @ (T.T @ orb))),
    "(expect ~0) ; so on a level set {V=c}: 6-1 = 5 invariants, of which 2 are G2-invariants (b0, one of |a|²,|c|²,<a,c> given V) and 3 are RELATIVE to u",
)


# ---------- 3. Hessian isotropy (corrected normal space) + cubic anisotropy ----------
def crystal_tangent(u, al, ga, b0, h=1e-5):
    cols = []
    for i in range(1, 8):
        du = E8[:, i] - (E8[:, i] @ u) * u
        if np.linalg.norm(du) < 1e-8:
            continue
        du /= np.linalg.norm(du)
        cols.append(
            (crystal(u + h * du, al, ga, b0) - crystal(u - h * du, al, ga, b0))
            / (2 * h)
        )
    th = np.arctan2(ga, al)
    r = np.sqrt(al * al + ga * ga)
    cols.append(
        (
            crystal(u, r * np.cos(th + h), r * np.sin(th + h), b0)
            - crystal(u, r * np.cos(th - h), r * np.sin(th - h), b0)
        )
        / (2 * h)
    )
    bb = lambda t: (np.sqrt(1 - t * t) * np.cos(th), np.sqrt(1 - t * t) * np.sin(th), t)
    cols.append((crystal(u, *bb(b0 + h)) - crystal(u, *bb(b0 - h))) / (2 * h))
    Tc = np.array(cols).T
    U_, S_, _ = np.linalg.svd(Tc)
    return U_[:, : np.sum(S_ > 1e-6)]


Tc = crystal_tangent(u, al, ga, b0)
T0 = tangent(s0)
Nrm = T0 - Tc @ (Tc.T @ T0)
Qn, Sn, _ = np.linalg.svd(Nrm)
Nb = Qn[:, : np.sum(Sn > 1e-6)]
print("crystal-manifold tangent dim:", Tc.shape[1], " normal-space dim:", Nb.shape[1])


def D2(x, v, hh=1e-2):
    Q_ = lambda k: (V(x + k * v) + V(x - k * v) - 2 * V(x)) / k**2
    return (4 * Q_(hh) - Q_(2 * hh)) / 3


H = np.array(
    [
        [
            (
                (D2(s0, Nb[:, i] + Nb[:, j]) - D2(s0, Nb[:, i] - Nb[:, j])) / 4
                if i != j
                else D2(s0, Nb[:, i])
            )
            for j in range(6)
        ]
        for i in range(6)
    ]
)
print(
    "normal Hessian eigenvalues:",
    np.round(np.linalg.eigvalsh(H), 6),
    " 8(1-b0²)=%.6f" % (8 * (1 - b0**2)),
)
C3 = []
for _ in range(12):
    n = Nb @ rng.normal(size=6)
    n /= np.linalg.norm(n)
    e = 1e-2
    C3.append((V(s0 + e * n) - V(s0 - e * n)) / (2 * e**3))
print(
    "cubic coefficient C3(n) along 12 random normal directions: min %.3f max %.3f  (direction-DEPENDENT: anisotropy starts at order 3)"
    % (min(C3), max(C3))
)
# ---------- 4. exceptional-divisor endpoint map: s0 + eps*n -> endpoint; drift |end - s0| vs eps ----------

# ---- fast exact gradient via structure matrices (same CD convention) ----
LE = [np.column_stack([mul(E8[:, i], E8[:, k]) for k in range(8)]) for i in range(8)]
RE = [np.column_stack([mul(E8[:, k], E8[:, i]) for k in range(8)]) for i in range(8)]


def Lm(x):
    return sum(x[i] * LE[i] for i in range(8))


def Rm(x):
    return sum(x[i] * RE[i] for i in range(8))


def gradV_fast(s):
    a, b = s[:8], s[8:]
    La, Ra, Lb, Rb = Lm(a), Rm(a), Lm(b), Rm(b)
    c = La @ b - Ra @ b
    return np.concatenate([2 * (Rb - Lb).T @ c, 2 * (La - Ra).T @ c])


def F_fast(s):
    g = gradV_fast(s)
    g = g - (g @ s) * s
    g[0] = 0
    return -g


_s = randstate()
assert np.allclose(F_fast(_s), ruleField(_s), atol=1e-10), "fast rule field mismatch"


def rk4(s, h):
    k1 = F_fast(s)
    k2 = F_fast(s + h / 2 * k1)
    k3 = F_fast(s + h / 2 * k2)
    k4 = F_fast(s + h * k3)
    t = s + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    t[0] = 0
    return t / np.linalg.norm(t)


def flow_to_end(s, h=0.005, tol=1e-24, maxit=6000):
    for it in range(maxit):
        s = rk4(s, h)
        if V(s) < tol:
            return s, it
    return s, maxit


print("exceptional-divisor endpoint map at s0 (RK4 h=0.005, stop V<1e-24):")
for k in range(3):
    n = Nb @ rng.normal(size=6)
    n /= np.linalg.norm(n)
    out = []
    for e in (2e-2, 1e-2, 5e-3, 2.5e-3):
        st = s0 + e * n
        st /= np.linalg.norm(st)
        se, it = flow_to_end(st)
        out.append(np.linalg.norm(se - s0))
    sl = np.polyfit(np.log([2e-2, 1e-2, 5e-3, 2.5e-3]), np.log(out), 1)[0]
    print(
        f"  dir {k}: |endpoint-s0| = {['%.2e'%x for x in out]}  log-log slope = {sl:.2f}  (slope 2 = identity on the divisor to first order)"
    )
# ---------- 5. Fix(Stab(s)) for in-flight s = O_s = ker Delta(s); flow confinement ----------
print("in-flight s: Stab_g2(a,c) and its fixed set")
for trial in range(3):
    s = randstate()
    a = s[:8]
    c = s[8:].copy()
    c[0] = 0
    st = stab_of([a, c])
    print(f"  trial {trial}: dim Stab_g2(a,c) = {len(st)} (SU(2)=3)", end="")
    Mfix = np.vstack([hat(D) for D in st])
    _, Sf, Wf = np.linalg.svd(Mfix)
    Fix = Wf[np.sum(Sf > 1e-9) :].T
    w, Vv = np.linalg.eigh(Delta(s))
    Ker = Vv[:, np.abs(w) < 1e-9]
    same = np.linalg.matrix_rank(np.column_stack([Fix, Ker]), tol=1e-8)
    print(
        f" | dim Fix_S = {Fix.shape[1]} | dim ker Δ = {Ker.shape[1]} | rank[Fix,ker] = {same} (8 ⇒ equal)",
        end="",
    )
    # flow from s; track distance to ker Δ(s) and kernel constancy
    P = Ker @ Ker.T
    cur = s.copy()
    dmax = 0
    kerchange = 0
    for it in range(8000):
        cur = rk4(cur, 0.005)
        dmax = max(dmax, np.linalg.norm(P @ cur - cur))
        if it % 500 == 0:
            w2, V2 = np.linalg.eigh(Delta(cur))
            K2 = V2[:, np.abs(w2) < 1e-7]
            if K2.shape[1] == 8:
                kerchange = max(kerchange, np.linalg.norm(K2 @ K2.T - P))
        if V(cur) < 1e-24:
            break
    ue = cur[:8].copy()
    ue[0] = 0
    ue /= np.linalg.norm(ue)
    Hi = np.column_stack([a, c, cross(a, c)])
    Q, _ = np.linalg.qr(Hi)
    print(
        f"\n      flow: V_end={V(cur):.1e} after {it} steps; max dist(s(t), ker Δ(s0)) = {dmax:.1e}; max ‖P_ker(s(t)) − P_ker(s0)‖ = {kerchange:.1e}; u_end ∈ span(a,c,a×c)? resid = {np.linalg.norm(ue-Q@(Q.T@ue)):.1e}; b0_end={cur[8]:.4f}"
    )
