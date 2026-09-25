"""#473 kill-attack 2 — diagnosis of the word-maps with the smallest non-pole endpoint V (attack2_wordmaps.py):
x ↦ x(ℓx), z(x(ℓx)), x(ℓ(xz)), x((xz)z).  Question: does small V at step 100 mean an approach to a NON-POLE vacuum
(σ = V/(1−b₀²)² → 0) or a slow approach to the pole ±ℓ (σ constant or bounded, |b₀| → 1)?  Runs 2000 steps on
20 s × 84 basis-sum z and reports V, |b₀|, σ at steps 100 / 500 / 2000 for the trajectories that were 'near-miss'
at step 100, plus the σ-invariance check for the (x, ℓ)-only map.  RAM < 200 MB, < 3 min.
"""

import json

import numpy as np

from flowlib import mul, potential
from zdlib import ELL, basis_sum_zds, im, stratified_states

rng = np.random.default_rng(20260924)
S = stratified_states(20, rng)
Z = np.array([z / np.sqrt(2) for *_, z, _ in basis_sum_zds()])
Sb = np.repeat(S, len(Z), axis=0)
Zb = np.tile(Z, (20, 1))
Lb = np.broadcast_to(ELL, Sb.shape).copy()
maps = {
    "x(ℓx)": lambda x: mul(x, mul(Lb, x)),
    "z(x(ℓx))": lambda x: mul(Zb, mul(x, mul(Lb, x))),
    "x(ℓ(xz))": lambda x: mul(x, mul(Lb, mul(x, Zb))),
    "x((xz)z)": lambda x: mul(x, mul(mul(x, Zb), Zb)),
}


def sig(x):
    b0 = x[:, 8]
    return potential(x) / np.maximum((1 - b0**2) ** 2, 1e-300)


out = {}
for name, f in maps.items():
    x = Sb.copy()
    dead = np.zeros(len(x), bool)
    snap = {}
    for k in range(1, 2001):
        y = im(f(x))
        n = np.linalg.norm(y, axis=-1)
        dead |= n < 1e-12
        x = np.where(dead[:, None], x, y / np.maximum(n[:, None], 1e-300))
        if k in (100, 500, 2000):
            snap[k] = (potential(x), np.abs(x[:, 8]), sig(x), x.copy())
    v100, b100, s100, _ = snap[100]
    near = (~dead) & (v100 < 1e-3) & (b100 < 0.999)
    print(
        f"\n{name}: dead {dead.sum()}/{len(x)}; near-miss at step 100 (V<1e-3, |b0|<0.999): {near.sum()}"
    )
    if name == "x(ℓx)":
        s0 = sig(Sb)
        print(
            f"   σ-invariance ((x,ℓ)-only map): max |σ(step100) − σ(s)| over alive = {np.abs(s100 - s0)[~dead].max():.2e}"
        )
    rec = {}
    for k in (100, 500, 2000):
        v, b, s, xk = snap[k]
        rec[k] = {
            "V_min": float(v[near].min()) if near.any() else None,
            "V_median": float(np.median(v[near])) if near.any() else None,
            "|b0|_min": float(b[near].min()) if near.any() else None,
            "|b0|_median": float(np.median(b[near])) if near.any() else None,
            "sigma_min": float(s[near].min()) if near.any() else None,
            "sigma_median": float(np.median(s[near])) if near.any() else None,
            "n_still_nonpole_V<1e-3": int(((v < 1e-3) & (b < 0.999))[near].sum()),
            "n_at_pole(|b0|>0.999)": int((b > 0.999)[near].sum()),
            "all_V_min_nonpole": (
                float(v[(~dead) & (b < 0.999)].min())
                if ((~dead) & (b < 0.999)).any()
                else None
            ),
            "all_sigma_min_nonpole": (
                float(s[(~dead) & (b < 0.999)].min())
                if ((~dead) & (b < 0.999)).any()
                else None
            ),
        }
        r = rec[k]
        print(
            f"   step {k:4d}: near-miss set → V min {r['V_min']}, |b0| median {r['|b0|_median']}, σ min {r['sigma_min']}, σ median {r['sigma_median']}; still non-pole V<1e-3: {r['n_still_nonpole_V<1e-3']}, now at pole: {r['n_at_pole(|b0|>0.999)']}  || all alive non-pole: V min {r['all_V_min_nonpole']}, σ min {r['all_sigma_min_nonpole']}"
        )
    # where do the near-miss trajectories sit? distance to ±ℓ and to the nearest vacuum direction
    _, _, _, x2000 = snap[2000]
    if near.any():
        dl = np.minimum(
            np.linalg.norm(x2000[near] - ELL, axis=1),
            np.linalg.norm(x2000[near] + ELL, axis=1),
        )
        print(
            f"   step 2000 near-miss set: distance to ±ℓ min {dl.min():.3e} median {np.median(dl):.3e} max {dl.max():.3e}"
        )
    out[name] = {
        "dead": int(dead.sum()),
        "n_near100": int(near.sum()),
        "snapshots": rec,
    }
json.dump(out, open("out_nearmiss.json", "w"), indent=1)
