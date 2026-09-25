"""step 1: the canonical invariant subspaces of a basis-sum ZD.  L_z has σ ∈ {2, √2, 0} with multiplicities
4/8/4; the normalised iteration x ↦ norm(z·x) converges into the σ=2 space T (and, up to the L_z rotation,
to the projection of x onto it).  Question: does the unit sphere of T (or of ker L_z = K, or of the
middle M) contain vacua (V = 0, |b₀| < 1)?  Sealed expectation (driver): T and K lie on the ridge V = 1.
"""

import json

import numpy as np

from flowlib import mul, potential
from zdlib import E, L_matrix, R_matrix, basis_sum_zds

rng = np.random.default_rng(1)
zds = basis_sum_zds()


def spaces(M):
    U, s, Wt = np.linalg.svd(M)
    T = Wt[np.isclose(s, s.max())]  # right-singular vectors, top
    K = Wt[s < 1e-9]  # kernel
    Mid = Wt[(~np.isclose(s, s.max())) & (s >= 1e-9)]
    return T, Mid, K


def V_stats(B, n=4000):
    """V and b0 over random unit vectors of span(B) (rows orthonormal), after Im-projection+normalisation."""
    X = rng.normal(size=(n, B.shape[0])) @ B
    X[:, 0] = 0
    X /= np.linalg.norm(X, axis=1, keepdims=True)
    v = potential(X)
    return float(v.min()), float(v.mean()), float(v.max()), float(np.abs(X[:, 8]).max())


rows = []
for name, mk in [
    ("L_z", L_matrix),
    ("R_z", R_matrix),
    ("ad_z", lambda z: L_matrix(z) - R_matrix(z)),
]:
    for i, j, sg, z, _ in zds[:6] + zds[40:43]:
        T, Mid, K = spaces(mk(z))
        r = {
            "map": name,
            "z": f"e{i}{'+' if sg>0 else '-'}e{j}",
            "dimT": len(T),
            "dimM": len(Mid),
            "dimK": len(K),
        }
        for lab, B in [("T", T), ("M", Mid), ("K", K)]:
            if len(B):
                mn, me, mx, b0 = V_stats(B)
                r[lab] = {
                    "Vmin": mn,
                    "Vmean": me,
                    "Vmax": mx,
                    "max|b0|": b0,
                    "Re-part present": bool(np.abs(B[:, 0]).max() > 1e-9),
                    "contains ℓ-component": bool(np.abs(B[:, 8]).max() > 1e-9),
                }
        rows.append(r)
for r in rows:
    print(
        f"{r['map']:5s} z={r['z']:8s} dims T/M/K = {r['dimT']}/{r['dimM']}/{r['dimK']}"
    )
    for lab in "TMK":
        if lab in r:
            q = r[lab]
            print(
                f"      {lab}: V ∈ [{q['Vmin']:.4f}, {q['Vmax']:.4f}] mean {q['Vmean']:.4f}  max|b0| {q['max|b0|']:.3f}  Re {q['Re-part present']}  ℓ {q['contains ℓ-component']}"
            )
# is T(L_{e1+e10}) = K(L_{e1-e10})?  and are the spaces spanned by basis-sum ZDs?
z, zm = E[1] + E[10], E[1] - E[10]
T, _, K = spaces(L_matrix(z))
_, _, Km = spaces(L_matrix(zm))
print(
    "T(L_{e1+e10}) == K(L_{e1-e10}):",
    np.linalg.matrix_rank(np.vstack([T, Km]), 1e-9) == 4,
)
for lab, B in [("T", T), ("K", K)]:
    supp = sorted({k for row in B for k in range(16) if abs(row[k]) > 1e-9})
    print(f"  coordinate support of {lab}(L_z): {supp}")
    # basis-sum ZDs inside B?
    inside = [
        f"e{i}{'+' if sg>0 else '-'}e{j}"
        for i, j, sg, w, _ in zds
        if np.linalg.norm(w - B.T @ (B @ w)) < 1e-9
    ]
    print(f"  basis-sum ZDs lying in {lab}: {inside}")
# does the ridge-valued V on T mean T ⊂ ridge?  Explicit: V on T for the 4 basis directions and the sums
json.dump(rows, open("out_zd_subspaces.json", "w"), indent=1, default=str)
