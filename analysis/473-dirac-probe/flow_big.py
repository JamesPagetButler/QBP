"""Gradient flow of V(s)=||[a,b]||^2 on S^14 = unit imaginary sedenions, s=(a,b), a in Im O, b in O.
Vectorised over samples via octonion structure tensor. Analytic gradient verified against finite differences.
"""

import numpy as np

exec(open("dirac_probe.py").read().split("np.set_printoptions")[0])
E8 = basis(8)
M = np.zeros((8, 8, 8))  # (x y)_k = M[i,j,k] x_i y_j
for i in range(8):
    for j in range(8):
        M[i, j] = cd_mul(E8[i], E8[j])


def omul(x, y):
    return np.einsum("ni,nj,ijk->nk", x, y, M)


def V(a, b):
    c = omul(a, b) - omul(b, a)
    return (c * c).sum(1)


def grad(a, b):
    # V=|c|^2, c=ab-ba ; dV = 2<c, da b - b da> + 2<c, a db - db a>
    # <xy,z>=<x,z ybar>, <yx,z>=<x,ybar z>  (valid in every CD algebra)
    c = omul(a, b) - omul(b, a)
    bb = b.copy()
    bb[:, 1:] *= -1
    ab = a.copy()
    ab[:, 1:] *= -1
    ga = 2 * (omul(c, bb) - omul(bb, c))
    ga[:, 0] = 0  # a imaginary: project
    gb = 2 * (omul(ab, c) - omul(c, ab))
    return ga, gb


rng = np.random.default_rng(1)
# --- FD check
a = rng.normal(size=(1, 8))
a[:, 0] = 0
b = rng.normal(size=(1, 8))
h = 1e-6
ga, gb = grad(a, b)
fd = []
for k in range(8):
    da = np.zeros((1, 8))
    da[0, k] = h
    fd.append(((V(a + da, b) - V(a - da, b)) / (2 * h))[0])
fdb = []
for k in range(8):
    db = np.zeros((1, 8))
    db[0, k] = h
    fdb.append(((V(a, b + db) - V(a, b - db)) / (2 * h))[0])
print(
    "grad check a:",
    np.allclose(ga[0], fd, atol=1e-5),
    " b:",
    np.allclose(gb[0], fdb, atol=1e-5),
)
# --- flow
N = 24000
s = rng.normal(size=(N, 15))
s /= np.linalg.norm(s, axis=1, keepdims=True)
a = np.concatenate([np.zeros((N, 1)), s[:, :7]], 1)
b = s[:, 7:].copy()
b0_init = b[:, 0].copy()
V_init = V(a, b)


def step(a, b, dt):
    ga, gb = grad(a, b)
    s = np.concatenate([a[:, 1:], b], 1)
    g = np.concatenate([ga[:, 1:], gb], 1)
    g -= (g * s).sum(1, keepdims=True) * s  # tangential
    s2 = s - dt * g
    s2 /= np.linalg.norm(s2, axis=1, keepdims=True)
    return np.concatenate([np.zeros((N, 1)), s2[:, :7]], 1), s2[:, 7:]


dt = 0.02
for it in range(5000):
    a, b = step(a, b, dt)
    if it % 2500 == 0:
        print(it, "max V", V(a, b).max())
Vend = V(a, b)
print("converged: max V =", Vend.max())
b0 = b[:, 0]
c = b[:, 1:]
an = np.linalg.norm(a, axis=1)
cn = np.linalg.norm(c, axis=1)
print(
    "endpoint b0^2: mean %.4f  (initial Haar mean 1/15=%.4f), <|b0|> %.4f"
    % ((b0**2).mean(), 1 / 15, abs(b0).mean())
)
print("endpoint |a|^2 mean %.4f, |Im b|^2 mean %.4f" % ((an**2).mean(), (cn**2).mean()))
print("transverse mass^2 = 8(1-b0^2): mean %.4f" % (8 * (1 - b0**2)).mean())
# does the flow send a parallel to Im b (vacuum) -- check alignment
cos = np.abs((a[:, 1:] * c).sum(1)) / (an * cn + 1e-15)
print("|cos(a,Im b)| at end: min %.4f" % cos.min())
# how much did b0 grow?  b0_end/b0_init
r = np.abs(b0) / np.abs(b0_init)
print(
    "b0 growth ratio: median %.3f  mean %.3f  max %.3f"
    % (np.median(r), r.mean(), r.max())
)
np.save("flow_end_big.npy", np.concatenate([a, b], 1))
np.save("flow_init_big.npy", np.stack([b0_init, V_init], 1))
se = (b0**2).std() / np.sqrt(N)
print("SE on <b0^2> = %.5f ; 1/7 = %.5f" % (se, 1 / 7))
import collections

print("quantiles b0^2:", np.quantile(b0**2, [0.1, 0.25, 0.5, 0.75, 0.9]))
