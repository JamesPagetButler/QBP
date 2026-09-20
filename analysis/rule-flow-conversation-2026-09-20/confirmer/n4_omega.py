import numpy as np, cdx, flow

rng = np.random.default_rng(23)


def proj(s):
    s = s.copy()
    s[..., 0] = 0
    return s / np.linalg.norm(s, axis=-1, keepdims=True)


def quench(s, steps=6000, h=0.02):
    for _ in range(steps):
        s = proj(s + h * flow.F(s))
    return s


# ---- rank of the omega-limit map:  d(omega)/d(s0) on the 14-dim tangent space
base = proj(rng.normal(size=16))
T = []  # orthonormal basis of T_base StateSphere (orth to base and to e0)
Q = np.zeros((16, 16))
vs = []
for k in range(16):
    v = np.zeros(16)
    v[k] = 1
    v[0] = 0
    v = v - (v @ base) * base
    for w in vs:
        v = v - (v @ w) * w
    n = np.linalg.norm(v)
    if n > 1e-8:
        vs.append(v / n)
T = np.array(vs)
print("tangent dim:", T.shape[0])
eps = 1e-4
w0 = quench(base)
J = []
for v in T:
    wp = quench(proj(base + eps * v))
    wm = quench(proj(base - eps * v))
    J.append((wp - wm) / (2 * eps))
J = np.array(J)  # 14 x 16
sv = np.linalg.svd(J, compute_uv=False)
print("endpoint V(base flow) = %.3e" % cdx.V(w0))
print("singular values of d(omega): ", np.array2string(sv, precision=3))
print("numerical rank (tol 1e-2 * max):", int((sv > 1e-2 * sv.max()).sum()))
print(
    "=> fibre dimension of omega  = 14 - rank =", 14 - int((sv > 1e-2 * sv.max()).sum())
)
# ---- flow-direction check: omega constant along the orbit
p1 = quench(base, steps=50)
print(
    "omega(base) vs omega(phi_50(base)) distance: %.3e"
    % np.linalg.norm(quench(p1) - w0)
)
# ---- crystal manifold dimension at w0
C = []
for k in range(200):
    d = proj(w0 + 1e-3 * rng.normal(size=16))
    d = quench(d, steps=3000)
    C.append(d - w0)
C = np.array(C)
svc = np.linalg.svd(C, compute_uv=False)
print(
    "crystal-set tangent singular values (200 nearby endpoints):",
    np.array2string(svc[:12] / svc[0], precision=3),
)
print("crystal-set dim (rel tol 0.05):", int((svc / svc[0] > 0.05).sum()))
