"""#473 kill-attack 2 — ITERATED NONLINEAR WORD-MAPS.  Every pure word w(x, ℓ, z) of length ≤ 4 (471 trees; the
ones without x are constant maps and are skipped) is used as a self-map of the state sphere,
x ↦ Im w(x, ℓ, z)/‖Im w(x, ℓ, z)‖, iterated 100 steps from 20 stratified non-vacuum s, for z in the 84 basis-sum
ZDs (mode basis) or 20 random ridge points (mode ridge).  This is the probe Prop 16 is actually about
("dynamics" = iteration of an algebra-native map); the linear cases (one x) are settled by the top-σ analysis
(zd_subspaces.py), the nonlinear ones (≥ 2 x) are new — e.g. x((xz)z) ≠ −2x·x because 𝕊 is not alternative.
Sealed expectation (driver): no non-pole vacuum is an attractor; endpoints are ridge points, poles, or cycles/fixed
points with V bounded away from 0; a few maps may be degenerate (Im → 0).  Hit ⇔ endpoint V < 1e-6, |b₀| < 0.999.
(In σ = V/(1−b₀²)² that is σ < 2.5e-1 at the |b₀| = 0.999 cut and σ < 1e-6 at b₀ = 0; the question this script answers
is the attractor one — no non-pole vacuum attractor — not reachability; see attack2_zd_words.md §7.0/§7.1.)
RAM < 400 MB; ≈ 10–20 min per mode (471 words × 100 steps × ≤ 3 products on 1680 rows).
"""

import json
import sys
import time

import numpy as np

from flowlib import mul, potential
from zdlib import ELL, basis_sum_zds, im, norm_im, stratified_states

mode = sys.argv[1] if len(sys.argv) > 1 else "basis"
NS, STEPS = 20, 100
rng = np.random.default_rng(20260924)
t0 = time.time()
S = stratified_states(NS, rng)
if mode == "basis":
    Z = np.array([z / np.sqrt(2) for *_, z, _ in basis_sum_zds()])
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

    Z = np.array([ridge_point() for _ in range(20)])
NZ = len(Z)
Sb = np.repeat(S, NZ, axis=0)
Zb = np.tile(Z, (NS, 1))
Lb = np.broadcast_to(ELL, Sb.shape).copy()

# word trees as nested tuples; leaves 'x','l','z'
trees = {1: ["x", "l", "z"]}
for n in range(2, 5):
    trees[n] = [(a, b) for i in range(1, n) for a in trees[i] for b in trees[n - i]]


def name(t):
    return t if isinstance(t, str) else f"({name(t[0])}{name(t[1])})"


def ev(t, x):
    if t == "x":
        return x
    if t == "l":
        return Lb
    if t == "z":
        return Zb
    return mul(ev(t[0], x), ev(t[1], x))


def n_x(t):
    return (t == "x") if isinstance(t, str) else n_x(t[0]) + n_x(t[1])


words = [t for n in range(1, 5) for t in trees[n] if n_x(t) >= 1 and name(t) != "x"]
print(
    f"mode {mode}: {len(words)} word-maps with ≥1 x (of 471 trees), {Sb.shape[0]} trajectories each, {STEPS} steps"
)
res, hits = [], []
for wi, t in enumerate(words):
    x = Sb.copy()
    dead = np.zeros(len(x), bool)
    hist = []
    for k in range(STEPS):
        y = im(ev(t, x))
        n = np.linalg.norm(y, axis=-1)
        dead |= n < 1e-9
        y = y / np.maximum(n[:, None], 1e-300)
        x = np.where(dead[:, None], x, y)
        if k >= STEPS - 7:
            hist.append(x.copy())
    alive = ~dead
    v = potential(x)
    b0 = x[:, 8]
    per = np.full(len(x), -1)
    for kk in range(1, 7):
        d = np.minimum(
            np.abs(hist[-1] - hist[-1 - kk]).max(-1),
            np.abs(hist[-1] + hist[-1 - kk]).max(-1),
        )
        per = np.where((per < 0) & (d < 1e-7), kk, per)
    nonpole = alive & (np.abs(b0) < 0.999)
    hit = nonpole & (v < 1e-6)
    r = {
        "word": name(t),
        "n_x": n_x(t),
        "alive": int(alive.sum()),
        "V_end_min_nonpole": float(v[nonpole].min()) if nonpole.any() else None,
        "V_end_mean": float(v[alive].mean()) if alive.any() else None,
        "frac_ridge": float((v[alive] > 0.999).mean()) if alive.any() else None,
        "frac_pole": (
            float(((v < 1e-8) & (np.abs(b0) >= 0.999))[alive].mean())
            if alive.any()
            else None
        ),
        "frac_nonpole_V<1e-3": (
            float((v[nonpole] < 1e-3).mean()) if nonpole.any() else None
        ),
        "n_nonpole_V<1e-3": int((v[nonpole] < 1e-3).sum()),
        "periods": (
            {
                str(k): int((per[alive] == k).sum())
                for k in sorted(set(per[alive].tolist()))
            }
            if alive.any()
            else {}
        ),
        "hits": int(hit.sum()),
    }
    res.append(r)
    for idx in np.where(hit)[0]:
        hits.append(
            {
                "word": name(t),
                "s_index": int(idx // NZ),
                "z_index": int(idx % NZ),
                "V": float(v[idx]),
                "b0": float(b0[idx]),
                "period": int(per[idx]),
            }
        )
    if wi % 50 == 0 or r["hits"]:
        print(
            f"  [{wi:3d}/{len(words)}] {name(t):22s} alive {r['alive']:5d} Vmin(nonpole) {r['V_end_min_nonpole']} ridge {r['frac_ridge']} pole {r['frac_pole']} periods {r['periods']} HITS {r['hits']}  {time.time()-t0:.0f}s",
            flush=True,
        )
nl = [r for r in res if r["n_x"] >= 2]
print(f"\nnonlinear word-maps (≥2 x): {len(nl)}; linear (1 x): {len(res)-len(nl)}")
vm = [r["V_end_min_nonpole"] for r in res if r["V_end_min_nonpole"] is not None]
print(
    f"min endpoint V over all non-pole alive trajectories and all maps: {min(vm):.3e}"
)
print(
    f"maps with any non-pole endpoint V<1e-3: {sum(1 for r in res if r['n_nonpole_V<1e-3'])} of {len(res)}; total such trajectories {sum(r['n_nonpole_V<1e-3'] for r in res)} of {len(res)*Sb.shape[0]}"
)
print(
    f"maps whose alive endpoints are all on the ridge: {sum(1 for r in res if r['frac_ridge']==1.0)}; all at a pole: {sum(1 for r in res if r['frac_pole']==1.0)}; fully dead: {sum(1 for r in res if r['alive']==0)}"
)
allper = {}
for r in res:
    for k, c in r["periods"].items():
        allper[k] = allper.get(k, 0) + c
print(
    f"period census over alive trajectories (−1 = not periodic ≤6 at 1e-7): {dict(sorted(allper.items(), key=lambda kv: int(kv[0])))}"
)
print(f"HITS (endpoint V < 1e-6, |b0| < 0.999): {len(hits)}")
for h in hits[:20]:
    print("   ", h)
worst = sorted(
    [r for r in res if r["V_end_min_nonpole"] is not None],
    key=lambda r: r["V_end_min_nonpole"],
)[:10]
print("10 maps with the smallest non-pole endpoint V:")
for r in worst:
    print(
        f"    {r['word']:22s} n_x {r['n_x']}  Vmin {r['V_end_min_nonpole']:.3e}  frac<1e-3 {r['frac_nonpole_V<1e-3']:.3f}  ridge {r['frac_ridge']:.3f} pole {r['frac_pole']:.3f}  periods {r['periods']}"
    )
json.dump(
    {
        "mode": mode,
        "NS": NS,
        "NZ": NZ,
        "steps": STEPS,
        "n_maps": len(res),
        "hits": hits,
        "results": res,
        "seconds": time.time() - t0,
    },
    open(f"out_wordmaps_{mode}.json", "w"),
    indent=1,
)
print(f"done {time.time()-t0:.0f}s")
