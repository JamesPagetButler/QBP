"""Efimov-echo probe (2026-09-21). Tune to threshold: start at V = 1-eps next to the frozen maximum locus
(a zero divisor x* = normalise(e1+e10), V(x*)=1) and watch the departure. Log-periodicity (discrete scale
invariance) would appear as (a) oscillation of tau(eps) - a*ln(1/eps) periodic in ln eps, or (b) a
non-flat residual after the exponential fit of ln(1-V)(t). Sealed position: none of that.
"""

import numpy as np, sys

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else ".")
from flowlib import *

rng = np.random.default_rng(669)
x = np.zeros(16)
x[1] = 1
x[10] = 1
x /= np.linalg.norm(x)
print("V(x*) =", potential(x[None])[0])
h = 0.002
eps_list = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7]
ndir = 24
V0s = []
taus = np.zeros((len(eps_list), ndir))
rates = np.zeros_like(taus)
resid_amp = np.zeros_like(taus)
for ie, eps in enumerate(eps_list):
    # random tangent directions at x*, scaled so that V(s0) ~ 1 - eps (bisection on delta)
    v = rng.standard_normal((ndir, 16))
    v[:, 0] = 0
    v -= (v @ x)[:, None] * x[None]
    v /= np.linalg.norm(v, axis=1, keepdims=True)
    s0 = np.zeros_like(v)
    for j in range(ndir):
        lo, hi = 0.0, 1.0
        for _ in range(60):
            d = 0.5 * (lo + hi)
            s = x + d * v[j]
            s /= np.linalg.norm(s)
            if 1 - potential(s[None])[0] < eps:
                lo = d
            else:
                hi = d
        s0[j] = (x + hi * v[j]) / np.linalg.norm(x + hi * v[j])
    V0s.append(1 - potential(s0))
    s = s0.copy()
    logs = []
    done = np.full(ndir, np.inf)
    k = 0
    while k < 400000 and np.isinf(done).any():
        s = step(s, h)
        k += 1
        V = potential(s)
        logs.append(np.log(np.maximum(1 - V, 1e-300)))
        newly = np.isinf(done) & (V < 0.5)
        done[newly] = k * h
    logs = np.array(logs)
    t = np.arange(1, k + 1) * h
    taus[ie] = done
    for j in range(ndir):
        m = (
            (logs[:, j] > np.log(1 - 0.999))
            & (logs[:, j] < np.log(0.3))
            & (t < done[j])
        )
        if m.sum() > 30:
            c = np.polyfit(t[m], logs[m, j], 1)
            rates[ie, j] = c[0]
            r = logs[m, j] - np.polyval(c, t[m])
            resid_amp[ie, j] = r.std()
    print(
        f"eps={eps:.0e}: 1-V0 mean {V0s[-1].mean():.2e}  tau mean {done.mean():.3f} sd {done.std():.3f}  "
        f"growth rate of ln(1-V) mean {rates[ie].mean():.3f} sd {rates[ie].std():.3f}  resid sd {resid_amp[ie].mean():.2e}  steps {k}"
    )
# (a) tau vs ln(1/eps): fit line, residual, periodogram in ln eps
le = np.log(1 / np.array(eps_list))
tm = taus.mean(1)
c = np.polyfit(le, tm, 1)
res = tm - np.polyval(c, le)
print(
    f"tau(eps) = {c[0]:.4f} ln(1/eps) + {c[1]:.4f}; 1/slope = {1/c[0]:.3f} (compare growth rate); residual sd {res.std():.2e} vs tau sd across dirs {taus.std(1).mean():.2e}"
)
print("residuals per eps:", np.array2string(res, precision=4))
# log-periodic fit: A cos(w ln eps + phi) over w in [0.5, 6]; report best amplitude relative to noise
best = (0, 0)
for w in np.linspace(0.5, 6, 500):
    X = np.column_stack([np.cos(w * le), np.sin(w * le)])
    a, *_ = np.linalg.lstsq(X, res, rcond=None)
    fit = X @ a
    amp = fit.std()
    best = max(best, (amp, w, 1 - (res - fit).var() / res.var()))
print(
    f"best log-periodic component in tau residual (fitted-curve sd): {best[0]:.2e} at w={best[1]:.2f} (period in ln eps {2*np.pi/best[1]:.2f}, R2 {best[2]:.2f}); Efimov period would be 3.12; residual noise {res.std():.2e}; per-direction scatter of tau {taus.std(1).mean():.2e}"
)
# expected-noise check: shuffle residuals 200 times, best fitted sd under the null
nulls = []
for _ in range(200):
    r2 = rng.permutation(res)
    b = 0
    for w in np.linspace(0.5, 6, 100):
        X = np.column_stack([np.cos(w * le), np.sin(w * le)])
        a, *_ = np.linalg.lstsq(X, r2, rcond=None)
        b = max(b, (X @ a).std())
    nulls.append(b)
print(
    f"null (shuffled) best fitted sd: median {np.median(nulls):.2e}, 95% {np.percentile(nulls,95):.2e}"
)
