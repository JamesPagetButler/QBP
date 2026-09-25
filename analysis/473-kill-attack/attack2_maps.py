"""#473 kill-attack 2, iterated maps with a canonical zero divisor z (mode basis: 84 basis-sum ZDs;
mode ridge: 50 random ridge points).  Maps on the state sphere (200 steps, from 200 stratified s):
  raw:  x ↦ norm(f(x))          (f = x·z, z·x, [x,z], x+z, xz+zx, (xz)ℓ, z(xℓ), x+z+ℓ)  — may leave Im𝕊
  im :  x ↦ norm(Im f(x))       (state-sphere self-map)
Records endpoint V, b₀, period (≤ 6, up to sign), fraction leaving Im, and — because x·z etc. are the
linear maps R_z, L_z, ad_z — compares the endpoint with the projection of the start onto the top-σ space.
Sealed expectation (driver): endpoints on the ridge V → 1 (b₀ → 0) or degenerate (xz+zx is real);
x+z → z (ridge); no non-pole vacuum.  RAM < 600 MB, ≈ 1–2 min."""

import json
import sys
import time

import numpy as np

from flowlib import mul, potential
from zdlib import ELL, basis_sum_zds, im, norm_im, stratified_states

mode = sys.argv[1] if len(sys.argv) > 1 else "basis"
NS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
STEPS = 200
rng = np.random.default_rng(20260924)
t0 = time.time()
S = stratified_states(NS, rng)
if mode == "basis":
    zds = basis_sum_zds()
    Z = np.array([z / np.sqrt(2) for *_, z, _ in zds])
else:

    def ridge_point():
        a = rng.normal(size=7)
        a /= np.linalg.norm(a)
        c = rng.normal(size=7)
        c -= np.dot(c, a) * a
        c /= np.linalg.norm(c)
        x = np.zeros(16)
        x[1:8] = a / np.sqrt(2)
        x[9:] = c / np.sqrt(2)
        return x

    Z = np.array([ridge_point() for _ in range(50)])
NZ = len(Z)
Sb = np.repeat(S, NZ, axis=0)
Zb = np.tile(Z, (NS, 1))
Lb = np.broadcast_to(ELL, Sb.shape)
print(f"mode {mode}: {NS} s × {NZ} z = {Sb.shape[0]} trajectories, {STEPS} steps")

maps = {
    "x·z": lambda x: mul(x, Zb),
    "z·x": lambda x: mul(Zb, x),
    "[x,z]": lambda x: mul(x, Zb) - mul(Zb, x),
    "x+z": lambda x: x + Zb,
    "xz+zx": lambda x: mul(x, Zb) + mul(Zb, x),
    "(xz)ℓ": lambda x: mul(mul(x, Zb), Lb),
    "z(xℓ)": lambda x: mul(Zb, mul(x, Lb)),
    "x+z+ℓ": lambda x: x + Zb + Lb,
    "x+z−ℓ": lambda x: x + Zb - Lb,
}
results = {}
for name, f in maps.items():
    for variant in ("raw", "im"):
        x = Sb.copy()
        left_im = np.zeros(len(x), bool)
        dead = np.zeros(len(x), bool)
        hist = []
        for k in range(STEPS):
            y = f(x)
            if variant == "im":
                y = im(y)
            n = np.linalg.norm(y, axis=-1)
            dead |= n < 1e-7
            y = y / np.maximum(n[:, None], 1e-300)
            left_im |= np.abs(y[:, 0]) > 1e-9
            x = np.where(dead[:, None], x, y)
            if k >= STEPS - 7:
                hist.append(x.copy())
        alive = ~dead
        xs, _ = norm_im(x)  # read the endpoint on the state sphere
        v = potential(xs)
        b0 = xs[:, 8]
        per = np.full(len(x), -1)
        for kk in range(1, 7):
            d = np.minimum(
                np.abs(hist[-1] - hist[-1 - kk]).max(-1),
                np.abs(hist[-1] + hist[-1 - kk]).max(-1),
            )
            per = np.where((per < 0) & (d < 1e-8), kk, per)
        hit = alive & (v < 1e-8) & (np.abs(b0) < 0.999)
        r = {
            "alive": int(alive.sum()),
            "dead(→0 or real)": int(dead.sum()),
            "left_Im": int(left_im[alive].sum()) if alive.any() else 0,
            "V_end_min": float(v[alive].min()) if alive.any() else None,
            "V_end_mean": float(v[alive].mean()) if alive.any() else None,
            "V_end_max": float(v[alive].max()) if alive.any() else None,
            "frac_V>0.999": float((v[alive] > 0.999).mean()) if alive.any() else None,
            "frac_V<1e-3": float((v[alive] < 1e-3).mean()) if alive.any() else None,
            "|b0|_end_max": float(np.abs(b0[alive]).max()) if alive.any() else None,
            "periods(up to sign)": (
                {
                    str(k): int((per[alive] == k).sum())
                    for k in sorted(set(per[alive].tolist()))
                }
                if alive.any()
                else {}
            ),
            "hits": int(hit.sum()),
        }
        results[f"{name} [{variant}]"] = r
        print(
            f"  {name:8s} [{variant:3s}] alive {r['alive']:5d} dead {r['dead(→0 or real)']:5d} leftIm {r['left_Im']:5d} | V_end [{r['V_end_min'] if r['V_end_min'] is None else round(r['V_end_min'],4)}, {r['V_end_max'] if r['V_end_max'] is None else round(r['V_end_max'],4)}] mean {r['V_end_mean'] if r['V_end_mean'] is None else round(r['V_end_mean'],4)} | frac ridge {r['frac_V>0.999']} | max|b0| {r['|b0|_end_max'] if r['|b0|_end_max'] is None else round(r['|b0|_end_max'],3)} | periods {r['periods(up to sign)']} | HITS {r['hits']}"
        )
json.dump(
    {
        "mode": mode,
        "NS": NS,
        "NZ": NZ,
        "steps": STEPS,
        "results": results,
        "seconds": time.time() - t0,
    },
    open(f"out_maps_{mode}.json", "w"),
    indent=1,
)
print(f"done {time.time()-t0:.0f}s")
