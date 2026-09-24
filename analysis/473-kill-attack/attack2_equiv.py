"""#473 kill-attack 2, part (C): Aut-equivariance.  Aut(𝕊) = G₂ × S₃ (Brown 1967).  G₂ acts diagonally,
φ(a,b) = (ga, gb), fixes ℓ, and is an algebra automorphism, so for ANY word  w(φs, ℓ, φz) = φ w(s, ℓ, z)
and V∘φ = V, b₀∘φ = b₀ exactly — hits/non-hits are G₂-invariant by construction.  The S₃ factor
(closed-form D₃ from aut_s3.py: rotations by 0, ±120° on the (a, Im b) multiplicity space with ℓ ↦ ℓ;
reflections with ℓ ↦ −ℓ) preserves V (det M = ±1) and maps b₀ ↦ ±b₀.  This script CHECKS both statements
numerically on all words of length ≤ 3 and on the 200-step iterated maps, 20 s × 84 z (and on 20 random
ridge z), and reports max |ΔV| and max |Δ|b₀||.  RAM < 500 MB, < 2 min."""

import json
import time

import numpy as np

from flowlib import mul, potential
from zdlib import (
    E,
    ELL,
    aut_residual,
    basis_sum_zds,
    im,
    norm_im,
    octonion_derivation_basis,
    random_g2_sedenion_aut,
    stratified_states,
)

rng = np.random.default_rng(7)
t0 = time.time()


def s3_matrix(deg, s, refl=False):
    """x₀ + a + b₀ℓ + cℓ ↦ x₀ + (m₁₁a + m₁₂c) + s b₀ ℓ + (m₂₁a + m₂₂c)ℓ"""
    t = np.radians(2 * deg if refl else deg)
    M = (
        np.array([[np.cos(t), np.sin(t)], [np.sin(t), -np.cos(t)]])
        if refl
        else np.array([[np.cos(t), -np.sin(t)], [np.sin(t), np.cos(t)]])
    )
    P = np.zeros((16, 16))
    P[0, 0] = 1
    P[8, 8] = s
    for k in range(1, 8):
        P[k, k] = M[0, 0]
        P[k, 8 + k] = M[0, 1]
        P[8 + k, k] = M[1, 0]
        P[8 + k, 8 + k] = M[1, 1]
    return P


# find the D₃ elements exactly (rotations 0/±120 with s=+1; reflections: grid search on the axis angle)
auts = {"rot+120": s3_matrix(120, +1), "rot-120": s3_matrix(-120, +1)}
for th in np.arange(0, 180, 0.5):
    P = s3_matrix(th, -1, refl=True)
    if aut_residual(P) < 1e-12:
        auts[f"refl{th:g}"] = P
ders = octonion_derivation_basis()
for k in range(2):
    auts[f"G2#{k}"] = random_g2_sedenion_aut(rng, ders)
print("automorphisms used (residual over 256 basis pairs):")
for n, P in auts.items():
    print(
        f"  {n:10s} residual {aut_residual(P):.1e}  ℓ ↦ {'+ℓ' if np.allclose(P@ELL, ELL) else ('−ℓ' if np.allclose(P@ELL, -ELL) else 'other')}"
    )
assert all(aut_residual(P) < 1e-11 for P in auts.values())
assert sum(n.startswith("refl") for n in auts) == 3, "expected 3 reflections"

S = stratified_states(20, rng)
zds = basis_sum_zds()
Zb_all = np.array([z / np.sqrt(2) for *_, z, _ in zds])


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


Zr_all = np.array([ridge_point() for _ in range(20)])


def word_images(Sb, Zb):
    """V and |b0| of all words of length ≤ 3 (state-sphere image), plus iterated-map endpoints (200 steps)."""
    Lb = np.broadcast_to(ELL, Sb.shape)
    lv = {1: [("s", Sb), ("l", Lb), ("z", Zb)]}
    for n in (2, 3):
        lv[n] = [
            (f"({na}{nb})", mul(A, B))
            for i in range(1, n)
            for (na, A) in lv[i]
            for (nb, B) in lv[n - i]
        ]
    out = {}
    for n in (1, 2, 3):
        for name, W in lv[n]:
            x, nim = norm_im(W)
            v = potential(x)
            v[nim < 1e-7] = np.nan
            out[name] = (v, np.abs(x[:, 8]))
    for name, f in {
        "z·x": lambda x: mul(Zb, x),
        "x·z": lambda x: mul(x, Zb),
        "[x,z]": lambda x: mul(x, Zb) - mul(Zb, x),
        "x+z": lambda x: x + Zb,
    }.items():
        x = Sb.copy()
        for _ in range(200):
            y = im(f(x))
            x = y / np.maximum(np.linalg.norm(y, axis=-1, keepdims=True), 1e-300)
        out[f"iter {name}"] = (potential(x), np.abs(x[:, 8]))
    return out


report = {}
for zname, Zset in [("basis84", Zb_all), ("ridge20", Zr_all)]:
    Sb = np.repeat(S, len(Zset), axis=0)
    Zb = np.tile(Zset, (len(S), 1))
    base = word_images(Sb, Zb)
    for an, P in auts.items():
        img = word_images(Sb @ P.T, Zb @ P.T)
        dV = max(np.nanmax(np.abs(img[k][0] - base[k][0])) for k in base)
        db = max(np.nanmax(np.abs(img[k][1] - base[k][1])) for k in base)
        nan_mismatch = sum(
            int((np.isnan(img[k][0]) != np.isnan(base[k][0])).sum()) for k in base
        )
        report[f"{zname}/{an}"] = {
            "max|ΔV|": float(dV),
            "max|Δ|b0||": float(db),
            "degeneracy-pattern mismatches": nan_mismatch,
        }
        print(
            f"  {zname:8s} {an:10s} max|ΔV| {dV:.1e}  max|Δ|b0|| {db:.1e}  degeneracy mismatches {nan_mismatch}"
        )
json.dump(
    {"auts": list(auts), "report": report, "seconds": time.time() - t0},
    open("out_equiv.json", "w"),
    indent=1,
)
print(f"done {time.time()-t0:.0f}s")
