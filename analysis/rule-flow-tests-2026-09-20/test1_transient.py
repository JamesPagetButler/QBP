"""TEST 1 — the 'still pond still moving' reading: is late-stage relaxation to a crystal slow (a drift)
or exponential? Prediction from RuleFlow.lean's Hessian (deriv2 = hessQuad = 8(1−b₀²)‖Pv‖², so
V ≈ 4(1−b₀²)x², ẋ = −8(1−b₀²)x): ln V decays at rate 16(1−b₀²(endpoint)). Measured per seed.
"""

import numpy as np, sys

sys.path.insert(0, ".")
from flowlib import *

rng = np.random.default_rng(635)
n = 500
h = 0.01
T = 3000
s = random_states(n, rng)
V = [potential(s)]
B = [b0(s)]
minnp = nonpole(s).copy()
for k in range(T):
    s = step(s, h)
    V.append(potential(s))
    B.append(b0(s))
    minnp = np.minimum(minnp, nonpole(s))
V = np.array(V)
B = np.array(B)
t = np.arange(T + 1) * h
Vend = V[-1]
b2 = B[-1] ** 2
vac = Vend < 1e-10
pole = b2 > 0.99
print(f"seeds {n}, h={h}, T={T*h}")
print(
    f"endpoint: crystals (V<1e-10): {vac.mean():.4f} | poles (b0^2>0.99): {pole.mean():.4f} | non-vacuum rest (V>1e-6): {(Vend>1e-6).mean():.4f} | max V_end {Vend.max():.2e}"
)
print(
    f"endpoint <b0^2> = {b2.mean():.4f} ± {b2.std()/np.sqrt(n):.4f}  (ledger flow_big.py: 0.146)"
)
# late-time exponential rate: fit ln V over the window 1e-9 < V < 1e-4 per seed
rates = []
pred = []
for i in range(n):
    m = (V[:, i] > 1e-9) & (V[:, i] < 1e-4)
    if m.sum() >= 20:
        c = np.polyfit(t[m], np.log(V[m, i]), 1)
        rates.append(-c[0])
        pred.append(16 * (1 - b2[i]))
rates = np.array(rates)
pred = np.array(pred)
print(
    f"late-time decay of ln V: measured rate mean {rates.mean():.3f}, predicted 16(1-b0^2) mean {pred.mean():.3f}; ratio median {np.median(rates/pred):.4f}, spread [{np.percentile(rates/pred,5):.3f},{np.percentile(rates/pred,95):.3f}]  (n_fit={len(rates)})"
)
# exponential vs power law: linearity of ln V in the window (R^2)
r2 = []
for i in range(min(n, 200)):
    m = (V[:, i] > 1e-9) & (V[:, i] < 1e-4)
    if m.sum() >= 20:
        c = np.polyfit(t[m], np.log(V[m, i]), 1)
        res = np.log(V[m, i]) - np.polyval(c, t[m])
        r2.append(1 - res.var() / np.log(V[m, i]).var())
print(
    f"ln V linearity in the window: R^2 median {np.median(r2):.5f}, min {np.min(r2):.5f}  (1 = pure exponential)"
)
# how long from V=0.5 to V=1e-8 (rule-time)
tt = []
for i in range(n):
    a = np.argmax(V[:, i] < 0.5)
    b = np.argmax(V[:, i] < 1e-8)
    if V[b, i] < 1e-8 and b > a:
        tt.append((b - a) * h)
print(
    f"rule-time from V=0.5 to V=1e-8: median {np.median(tt):.2f}, 95th pct {np.percentile(tt,95):.2f}"
)
print(
    f"min over trajectories of (1-b0^2): {minnp.min():.4f}; seeds passing within 0.01 of a pole: {(minnp<0.01).mean():.4f}"
)
np.save("t1_Vend.npy", Vend)
np.save("t1_b2.npy", b2)
