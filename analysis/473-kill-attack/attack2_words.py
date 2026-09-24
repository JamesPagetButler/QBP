"""#473 kill-attack 2, part (A)/(B): words w(s, ℓ, z) of length ≤ 5 (all bracketings, all leaf labellings)
over s (200 stratified non-vacuum states), ℓ = e₈, z ∈ the 84 basis-sum ZDs (mode 'basis') or 50 random
points of the ZD ridge V = 1 (mode 'ridge').  Conjugation is redundant for imaginary generators (conj of
a word is ± its reversal, and every reversal is enumerated); real scalars are absorbed by normalisation.
Variant 'imnode': words of length ≤ 4 where every internal node may additionally be Im-projected
(the (+, conj, scalar) closure the Lean `GenBy` uses).  Each word is evaluated on the state sphere
x = Im w/‖Im w‖; hit ⇔ V < 1e-8 and |b₀| < 0.999 and the word is non-degenerate (‖Im w‖ > 1e-7 absolute; leaves are unit).
NOTE (Red Team #676 F1/F2): in the invariant σ = V/(1−b₀²)² this criterion is σ < 1e-8/(1−b₀²)², i.e. σ < 2.5e-3 at
the |b₀| = 0.999 cut; σ is the hit variable to read the outputs by.  The preimage of the vacuum under a fixed word has
codim ≥ 4, so 200 sampled s cannot hit it and "0 hits" does NOT test reachability (fixed words such as s·z do reach
non-pole vacua on a measure-zero set of s); the reported σ_min values are sampling floors.  See attack2_zd_words.md §7.0.
Also: linear closure dimension of the (s, ℓ, z)-subalgebra (rank of the word vectors, 20 pairs), and
fixed-coefficient two-word combinations w₁ + c·w₂ (length ≤ 3, c ∈ {±1, ±2, ±½}).
Usage: python3 attack2_words.py basis|ridge   (RAM ≈ 1.6 GB for 'basis', ≈ 1 GB for 'ridge'; ≈ 2–5 min)
"""

import json
import sys
import time

import numpy as np

from flowlib import mul, potential
from zdlib import E, ELL, basis_sum_zds, im, norm_im, stratified_states

mode = sys.argv[1] if len(sys.argv) > 1 else "basis"
NS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
rng = np.random.default_rng(20260924)
t0 = time.time()

S = stratified_states(NS, rng)
vS = potential(S)
print(
    f"states: {NS}, V(s) ∈ [{vS.min():.4f}, {vS.max():.4f}], |b0| max {np.abs(S[:,8]).max():.3f}, all non-vacuum: {vS.min() > 1e-3}"
)

if mode == "basis":
    zds = basis_sum_zds()
    Z = np.array([z / np.sqrt(2) for *_, z, _ in zds])
    zlab = [f"e{i}{'+' if sg>0 else '-'}e{j}" for i, j, sg, _, _ in zds]
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
    zlab = [f"ridge{k}" for k in range(len(Z))]
    assert np.allclose(potential(Z), 1.0)
NZ = len(Z)
# batch of (s, z) pairs, processed in CHUNKS of ≤ CH s-states (memory: stored word arrays scale with rows;
# measured 0.92 GB peak at 1680 rows incl. heap fragmentation, so chunks of 25 s × NZ rows stay ≈ 1 GB)
CH = max(1, 2100 // NZ)
HIT_V, HIT_B0, DEGEN_ABS = (
    1e-8,
    0.999,
    1e-7,
)  # absolute ‖Im w‖ floor (leaves are unit vectors; cancellations like s + s³/‖s³‖ ≡ 0 must not pass as states)
hits, degenerate, ACC = [], [], {}
BINS = np.linspace(0, 1, 21)
HIST = {}
closure_dims = {}
n_imnode = n_combo = 0


def acc(variant, v, b0):
    h = HIST.setdefault(
        variant,
        {
            "V": np.zeros(20, int),
            "sigma": np.zeros(20, int),
            "n_pole": 0,
            "n_eval": 0,
            "n_nonpole_V<1e-3": 0,
            "sigma_min": 1.0,
        },
    )
    h["V"] += np.histogram(np.clip(v, 0, 1), BINS)[0]
    np_ = np.abs(b0) < 0.999
    sig = v[np_] / (1 - b0[np_] ** 2) ** 2
    h["sigma"] += np.histogram(np.clip(sig, 0, 1), BINS)[0]
    h["n_pole"] += int(((v < 1e-8) & ~np_).sum())
    h["n_eval"] += int(len(v))
    h["n_nonpole_V<1e-3"] += int((v[np_] < 1e-3).sum())
    if sig.size:
        h["sigma_min"] = min(h["sigma_min"], float(sig.min()))
    return sig


def evaluate(name, W, variant="pure", s_offset=0):
    """accumulate per-word statistics of the state-sphere image across chunks; record hits."""
    nrm = np.linalg.norm(W, axis=-1)
    x, nim = norm_im(W)
    ok = nim > DEGEN_ABS
    v = potential(x)
    b0 = x[:, 8]
    sig = acc(variant, v[ok], b0[ok])
    a = ACC.setdefault(
        name,
        {
            "variant": variant,
            "n": 0,
            "n_degenerate": 0,
            "n_zero": 0,
            "V_min": np.inf,
            "V_sum": 0.0,
            "n_ok": 0,
            "V_max": -np.inf,
            "n_V<1e-3": 0,
            "n_V>0.999": 0,
            "max|b0|": 0.0,
            "Re_sum": 0.0,
            "sigma_min": np.inf,
            "n_pole": 0,
        },
    )
    a["n"] += len(v)
    a["n_degenerate"] += int((~ok).sum())
    a["n_zero"] += int((nrm < DEGEN_ABS).sum())
    a["Re_sum"] += float(np.sum(np.abs(W[:, 0]) / np.maximum(nrm, 1e-300)))
    if ok.any():
        vo = v[ok]
        a["V_min"] = min(a["V_min"], float(vo.min()))
        a["V_max"] = max(a["V_max"], float(vo.max()))
        a["V_sum"] += float(vo.sum())
        a["n_ok"] += int(ok.sum())
        a["n_V<1e-3"] += int((vo < 1e-3).sum())
        a["n_V>0.999"] += int((vo > 0.999).sum())
        a["max|b0|"] = max(a["max|b0|"], float(np.abs(b0[ok]).max()))
        a["n_pole"] += int(((v < 1e-8) & (np.abs(b0) >= 0.999) & ok).sum())
    if sig.size:
        a["sigma_min"] = min(a["sigma_min"], float(sig.min()))
    h = np.where(ok & (v < HIT_V) & (np.abs(b0) < HIT_B0))[0]
    for idx in h:
        hits.append(
            {
                "word": name,
                "s_index": int(s_offset + idx // NZ),
                "z": zlab[idx % NZ],
                "V": float(v[idx]),
                "b0": float(b0[idx]),
            }
        )


MAXLEN = 5
for c0 in range(0, NS, CH):
    Sc = S[c0 : c0 + CH]
    Sb = np.repeat(Sc, NZ, axis=0)
    Zb = np.tile(Z, (len(Sc), 1))
    Lb = np.broadcast_to(ELL, Sb.shape).copy()
    leaves = {"s": Sb, "l": Lb, "z": Zb}
    first = c0 == 0
    # ---- pure product words, length ≤ 5 (levels 1–4 stored, level 5 streamed) --------------------
    words_by_len = {1: [(k, v) for k, v in leaves.items()]}
    for k, v in words_by_len[1]:
        evaluate(k, v, "pure", c0)
    if first:
        sub_pairs = rng.choice(Sb.shape[0], 20, replace=False)
        closure_vecs = {
            int(p): [E[0]] + [leaves[k][p] for k in "slz"] for p in sub_pairs
        }
    for n in range(2, MAXLEN + 1):
        new = []
        for i in range(1, n):
            for na, A in words_by_len[i]:
                for nb, B in words_by_len[n - i]:
                    name = f"({na}{nb})"  # every product parenthesised: distinct trees get distinct names
                    W = mul(A, B)
                    evaluate(name, W, "pure", c0)
                    if first:
                        for p in sub_pairs:
                            closure_vecs[int(p)].append(W[p])
                    if n < MAXLEN:
                        new.append((name, W))
        words_by_len[n] = new
    if first:
        closure_dims = {
            p: int(np.linalg.matrix_rank(np.array(vs), 1e-8))
            for p, vs in closure_vecs.items()
        }
    del words_by_len
    # ---- Im-node variant, length ≤ 4 (level 3 stored, level 4 streamed) ----------------------------
    wl = {1: [(k, v) for k, v in leaves.items()]}
    for n in range(2, 5):
        new = []
        for i in range(1, n):
            for na, A in wl[i]:
                for nb, B in wl[n - i]:
                    W = mul(A, B)
                    for tag, WW in [("", W), ("Im", im(W))]:
                        name = f"{tag}({na}{nb})"
                        evaluate(name, WW, "imnode", c0)
                        if first:
                            n_imnode += 1
                        if n < 4:
                            new.append((name, WW))
        wl[n] = new
    del wl
    # ---- fixed-coefficient two-word combinations, length ≤ 3 ---------------------------------------
    lvl = {1: [(k, v) for k, v in leaves.items()]}
    for n in (2, 3):
        lvl[n] = [
            (f"({na}{nb})", mul(A, B))
            for i in range(1, n)
            for (na, A) in lvl[i]
            for (nb, B) in lvl[n - i]
        ]
    allshort = lvl[1] + lvl[2] + lvl[3]
    for a_ in range(len(allshort)):
        for b_ in range(a_ + 1, len(allshort)):
            na, A = allshort[a_]
            nb, B = allshort[b_]
            An = A / np.maximum(np.linalg.norm(A, axis=-1, keepdims=True), 1e-300)
            Bn = B / np.maximum(np.linalg.norm(B, axis=-1, keepdims=True), 1e-300)
            for c in (1, -1, 2, -2, 0.5, -0.5):
                evaluate(
                    f"{na}{'+' if c>0 else '-'}{abs(c)}·{nb}", An + c * Bn, "combo", c0
                )
                if first:
                    n_combo += 1
    del lvl, allshort, leaves, Sb, Zb, Lb
    print(
        f"  chunk s[{c0}:{c0+len(Sc)}] done: words pure/imnode/combo = {sum(1 for a in ACC.values() if a['variant']=='pure')}/{n_imnode}/{n_combo}; hits so far {len(hits)}; {time.time()-t0:.0f}s",
        flush=True,
    )
print(
    f"linear-closure dimension of span(words ≤ {MAXLEN}) over 20 (s,z) pairs: {sorted(set(closure_dims.values()))}"
)

# finalise per-word stats
stats = []
for name, a in ACC.items():
    st = {
        "word": name,
        "variant": a["variant"],
        "n_degenerate": a["n_degenerate"],
        "n_zero": a["n_zero"],
        "n_pole": a["n_pole"],
        "V_min": a["V_min"] if a["n_ok"] else None,
        "V_mean": a["V_sum"] / a["n_ok"] if a["n_ok"] else None,
        "V_max": a["V_max"] if a["n_ok"] else None,
        "frac_V<1e-3": a["n_V<1e-3"] / a["n_ok"] if a["n_ok"] else None,
        "frac_V>0.999": a["n_V>0.999"] / a["n_ok"] if a["n_ok"] else None,
        "max|b0|": a["max|b0|"] if a["n_ok"] else None,
        "mean|Re w|/|w|": a["Re_sum"] / a["n"],
        "sigma_min": a["sigma_min"] if np.isfinite(a["sigma_min"]) else None,
    }
    stats.append(st)
    if a["n_ok"] == 0:
        degenerate.append(name)

# ---- summary -----------------------------------------------------------------------------------------
pure = [s for s in stats if s["variant"] == "pure"]
vmins = np.array([s["V_min"] for s in pure if s["V_min"] is not None])
print(
    f"\npure words: {len(pure)}, fully degenerate (real or zero for all pairs): {len([d for d in degenerate if ACC[d]['variant']=='pure'])} (of which identically zero: {sum(1 for d in degenerate if ACC[d]['variant']=='pure' and ACC[d]['n_zero']==ACC[d]['n'])})"
)
print(
    f"  per-word V_min over the batch: min {vmins.min():.3e}, median {np.median(vmins):.3e}; words with V_min < 1e-3: {(vmins < 1e-3).sum()}"
)
print(
    f"  words whose image is entirely on the ridge (frac V>0.999 = 1): {sum(1 for s in pure if s['frac_V>0.999'] == 1.0)}"
)
for var, h in HIST.items():
    print(
        f"  [{var}] evaluations {h['n_eval']}: pole landings {h['n_pole']}, non-pole with V<1e-3: {h['n_nonpole_V<1e-3']}, σ_min (non-pole) {h['sigma_min']:.3e}"
    )
    print(f"     V hist (20 bins on [0,1]):  {h['V'].tolist()}")
    print(f"     σ hist (20 bins on [0,1]):  {h['sigma'].tolist()}")
smin = np.array([s["sigma_min"] for s in pure if s["sigma_min"] is not None])
print(
    f"  pure words σ_min: min {smin.min():.3e}, words with σ_min < 1e-3: {(smin < 1e-3).sum()}, < 1e-2: {(smin < 1e-2).sum()}"
)
print(f"HITS (V < {HIT_V}, |b0| < {HIT_B0}, non-degenerate): {len(hits)}")
from collections import Counter

byword = Counter(h["word"] for h in hits)
for w, c in byword.most_common(30):
    zs = {h["z"] for h in hits if h["word"] == w}
    ss = {h["s_index"] for h in hits if h["word"] == w}
    print(
        f"    {w:40s} hits {c:6d}  distinct z {len(zs):3d}  distinct s {len(ss):3d}  example {[h for h in hits if h['word']==w][0]}"
    )
out_hits_by_word = {
    w: {
        "count": c,
        "n_z": len({h["z"] for h in hits if h["word"] == w}),
        "n_s": len({h["s_index"] for h in hits if h["word"] == w}),
    }
    for w, c in byword.items()
}
out = {
    "mode": mode,
    "NS": NS,
    "NZ": NZ,
    "n_words_pure": len(pure),
    "n_words_imnode": n_imnode,
    "n_combos": n_combo,
    "closure_dims": closure_dims,
    "degenerate_words": degenerate,
    "hits_by_word": out_hits_by_word,
    "hits": hits[:2000],
    "V_min_over_words": float(vmins.min()),
    "words_Vmin_lt_1e-3": [
        s["word"] for s in pure if s["V_min"] is not None and s["V_min"] < 1e-3
    ],
    "ridge_words": [s["word"] for s in pure if s["frac_V>0.999"] == 1.0],
    "hist": {
        k: {kk: (vv.tolist() if hasattr(vv, "tolist") else vv) for kk, vv in h.items()}
        for k, h in HIST.items()
    },
    "words_sigma_lt_1e-3": [
        s["word"] for s in pure if s["sigma_min"] is not None and s["sigma_min"] < 1e-3
    ],
    "stats_pure": pure,
    "seconds": time.time() - t0,
}
json.dump(out, open(f"out_words_{mode}.json", "w"), indent=1)
print(f"done {time.time()-t0:.0f}s")
