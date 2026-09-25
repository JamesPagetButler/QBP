"""ATTACK 1 / leg C — quench re-measured with different integrators on IDENTICAL Haar seeds.
Tangent field F(x) = -(∇V - <∇V,x> x) with the closed-form gradient ∂V/∂a = 8(Ca - Dc), ∂V/∂c = 8(Ac - Da)
(checked against flowlib.gradV_exact at start-up). Integrators: renormalised Euler h=0.02 (flow_big's scheme),
RK4+renormalise h = 0.02/0.01/0.005, adaptive Dormand-Prince 5(4) (rtol 1e-9) on a 2000-seed subset,
and flowlib.step itself (the on-record integrator) on the same 2000 seeds. All to T = 100; RK4 h=0.02 continued to T=400.
Closed-form endpoint b0²/(b0² + sqrt((1-b0²)² - V0)) compared per seed."""

import time
import numpy as np
from flowlib import potential, gradV_exact, step as flowstep, random_states

out = open("quench_rk4_out.txt", "w")


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    out.write(s + "\n")
    out.flush()


def grad(x):
    a, c = x[:, 1:8], x[:, 9:16]
    A = (a * a).sum(1, keepdims=True)
    C = (c * c).sum(1, keepdims=True)
    D = (a * c).sum(1, keepdims=True)
    g = np.zeros_like(x)
    g[:, 1:8] = 8 * (C * a - D * c)
    g[:, 9:16] = 8 * (A * c - D * a)
    return g


def F(x):
    g = grad(x)
    return -(g - (g * x).sum(1, keepdims=True) * x)


def renorm(x):
    return x / np.linalg.norm(x, axis=1, keepdims=True)


def euler(x, h, n):
    for _ in range(n):
        x = renorm(x + h * F(x))
    return x


def rk4(x, h, n):
    for _ in range(n):
        k1 = F(x)
        k2 = F(x + 0.5 * h * k1)
        k3 = F(x + 0.5 * h * k2)
        k4 = F(x + h * k3)
        x = renorm(x + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4))
    return x


def dp45(x, T, rtol=1e-9, atol=1e-12):
    # Dormand-Prince 5(4), common adaptive step for all seeds (error = max over seeds), renormalise after each step
    c2, c3, c4, c5 = 1 / 5, 3 / 10, 4 / 5, 8 / 9
    a21 = 1 / 5
    a31, a32 = 3 / 40, 9 / 40
    a41, a42, a43 = 44 / 45, -56 / 15, 32 / 9
    a51, a52, a53, a54 = 19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729
    a61, a62, a63, a64, a65 = (
        9017 / 3168,
        -355 / 33,
        46732 / 5247,
        49 / 176,
        -5103 / 18656,
    )
    b1, b3, b4, b5, b6 = 35 / 384, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84
    e1, e3, e4, e5, e6, e7 = (
        71 / 57600,
        -71 / 16695,
        71 / 1920,
        -17253 / 339200,
        22 / 525,
        -1 / 40,
    )
    t, h, nstep, nrej = 0.0, 1e-3, 0, 0
    while t < T:
        h = min(h, T - t)
        k1 = F(x)
        k2 = F(x + h * a21 * k1)
        k3 = F(x + h * (a31 * k1 + a32 * k2))
        k4 = F(x + h * (a41 * k1 + a42 * k2 + a43 * k3))
        k5 = F(x + h * (a51 * k1 + a52 * k2 + a53 * k3 + a54 * k4))
        k6 = F(x + h * (a61 * k1 + a62 * k2 + a63 * k3 + a64 * k4 + a65 * k5))
        xn = x + h * (b1 * k1 + b3 * k3 + b4 * k4 + b5 * k5 + b6 * k6)
        k7 = F(xn)
        err = h * (e1 * k1 + e3 * k3 + e4 * k4 + e5 * k5 + e6 * k6 + e7 * k7)
        sc = atol + rtol * np.maximum(np.abs(x), np.abs(xn))
        en = np.sqrt(((err / sc) ** 2).mean(1)).max()
        if en <= 1:
            t += h
            x = renorm(xn)
            nstep += 1
        else:
            nrej += 1
        h *= min(5, max(0.2, 0.9 * en ** (-0.2)))
    return x, nstep, nrej


def report(tag, x, ref):
    b2 = x[:, 8] ** 2
    V = potential(x)
    d = b2 - ref
    P(
        "%-28s <b0^2> = %.5f +- %.5f | vs closed form: mean diff %+.2e, max|diff| %.2e | max V_end %.1e, frac V_end>1e-8: %.4f"
        % (
            tag,
            b2.mean(),
            b2.std() / np.sqrt(len(b2)),
            d.mean(),
            np.abs(d).max(),
            V.max(),
            (V > 1e-8).mean(),
        )
    )
    return b2


N = 24000
rng = np.random.default_rng(20260924)
x0 = random_states(N, rng)
P(
    "grad closed form vs flowlib.gradV_exact (5 states): %.1e"
    % np.abs(grad(x0[:5]) - gradV_exact(x0[:5])).max()
)
P(
    "field tangency max|<F,x>| = %.1e ; F[:,0] max = %.1e"
    % (np.abs((F(x0) * x0).sum(1)).max(), np.abs(F(x0)[:, 0]).max())
)
B0 = x0[:, 8] ** 2
V0 = potential(x0)
cf = B0 / (B0 + np.sqrt((1 - B0) ** 2 - V0))
P(
    "N = %d identical Haar seeds; <b0^2>_init = %.5f (1/15 = %.5f)"
    % (N, B0.mean(), 1 / 15)
)
P(
    "closed form  b0^2/(b0^2+sqrt((1-b0^2)^2-V0)):  <b0^2>_end = %.5f +- %.5f"
    % (cf.mean(), cf.std() / np.sqrt(N))
)

t0 = time.time()
xe = euler(x0, 0.02, 5000)
be = report("Euler h=0.02  T=100 (24000)", xe, cf)
P("   [%.0f s]" % (time.time() - t0))
t0 = time.time()
xr = rk4(x0, 0.02, 5000)
b02 = report("RK4 h=0.020 T=100 (24000)", xr, cf)
P("   [%.0f s]" % (time.time() - t0))
P(
    "paired Euler(0.02) - RK4(0.02), N=24000: mean %+.2e +- %.1e, max|.| %.2e"
    % ((be - b02).mean(), (be - b02).std() / np.sqrt(N), np.abs(be - b02).max())
)
S = 6000
res = {0.02: b02[:S]}
for h in [0.01, 0.005]:
    t0 = time.time()
    xs = rk4(x0[:S].copy(), h, int(round(100 / h)))
    res[h] = report("RK4 h=%.3f T=100 (%d)" % (h, S), xs, cf[:S])
    P("   [%.0f s]" % (time.time() - t0))
d1 = res[0.02] - res[0.01]
d2 = res[0.01] - res[0.005]
P(
    "Richardson (6000 seeds): mean|RK4(0.02)-RK4(0.01)| = %.2e, mean|RK4(0.01)-RK4(0.005)| = %.2e, ratio %.1f (h^4 -> 16)"
    % (
        np.abs(d1).mean(),
        np.abs(d2).mean(),
        np.abs(d1).mean() / max(np.abs(d2).mean(), 1e-300),
    )
)
P(
    "paired Euler(0.02) - RK4(0.005), 6000 seeds: mean %+.2e +- %.1e, max|.| %.2e"
    % (
        (be[:S] - res[0.005]).mean(),
        (be[:S] - res[0.005]).std() / np.sqrt(S),
        np.abs(be[:S] - res[0.005]).max(),
    )
)
M = 2000
t0 = time.time()
xd, ns, nr = dp45(x0[:M].copy(), 100.0)
bd = report("DP45 rtol1e-9 T=100 (2000)", xd, cf[:M])
P(
    "   steps %d rejected %d [%.0f s]; paired DP45 - RK4(0.005): max|.| %.2e"
    % (ns, nr, time.time() - t0, np.abs(bd - res[0.005][:M]).max())
)
t0 = time.time()
xr400 = rk4(xd.copy(), 0.02, 15000)
report("RK4 h=0.02 T=100->400 (2000)", xr400, cf[:M])
P(
    "   [%.0f s]; T=100->400 mean shift %+.2e"
    % (time.time() - t0, (xr400[:, 8] ** 2 - bd).mean())
)
M2 = 1000
t0 = time.time()
xf = x0[:M2].copy()
for _ in range(5000):
    xf = flowstep(xf, 0.02)
bf = report("flowlib.step h=0.02 (1000)", xf, cf[:M2])
P(
    "   [%.0f s]; paired flowlib.step - my Euler: max|.| %.2e"
    % (time.time() - t0, np.abs(bf - be[:M2]).max())
)
out.close()
