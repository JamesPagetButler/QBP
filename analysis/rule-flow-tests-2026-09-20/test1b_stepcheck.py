"""Discretisation check for TEST 1: repeat the late-time rate fit at h = 0.005 and h = 0.0025.
Euler on x' = -k x has effective rate -ln(1-hk)/h ≈ k(1 + hk/2); if the 4% offset is discretisation
it must shrink to ~2% and ~1%."""

import numpy as np, sys

sys.path.insert(0, ".")
from flowlib import *

for h, T in ((0.01, 3000), (0.005, 6000), (0.0025, 12000)):
    rng = np.random.default_rng(635)
    n = 200
    s = random_states(n, rng)
    V = [potential(s)]
    for k in range(T):
        s = step(s, h)
        V.append(potential(s))
    V = np.array(V)
    t = np.arange(T + 1) * h
    b2 = b0(s) ** 2
    rat = []
    for i in range(n):
        m = (V[:, i] > 1e-9) & (V[:, i] < 1e-4)
        if m.sum() >= 20:
            c = np.polyfit(t[m], np.log(V[m, i]), 1)
            rat.append(-c[0] / (16 * (1 - b2[i])))
    rat = np.array(rat)
    k = 14.0
    print(
        f"h={h}: measured/predicted median {np.median(rat):.4f}  | Euler prediction 1+hk/2 = {1+h*k/2:.4f}"
    )
