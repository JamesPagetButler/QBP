"""step 0: enumerate the basis-sum zero divisors; cross-check 84 elements / 42 planes; V = 1 on the sphere;
ZD ⇔ V = 1 sanity on random ridge points; the Jordan map degeneracy; the S₃/G₂ automorphism check.
"""

import json

import numpy as np

from flowlib import mul, potential
from zdlib import (
    E,
    ELL,
    L_matrix,
    R_matrix,
    aut_residual,
    basis_sum_zds,
    octonion_derivation_basis,
    random_g2_sedenion_aut,
)

rng = np.random.default_rng(473)
zds = basis_sum_zds()
print(f"basis-sum zero divisors e_i ± e_j with singular L_z: {len(zds)} (expect 84)")
planes = sorted({(i, j) for i, j, _, _, _ in zds})
print(f"distinct planes (i,j): {len(planes)} (expect 42)")
kd = sorted({k for *_, k in zds})
print(f"left-kernel dims present: {kd}")
# each plane: do both signs appear?
both = all(
    ((i, j, 1) in {(a, b, s) for a, b, s, _, _ in zds})
    and ((i, j, -1) in {(a, b, s) for a, b, s, _, _ in zds})
    for i, j in planes
)
print(f"both signs per plane: {both}")
# any plane with i,j both < 8 (octonion) or both > 8?  ZDs must straddle the halves
print(
    f"planes straddling 𝕆 / 𝕆ℓ: {sum(1 for i,j in planes if i<8 and j>8)} / {len(planes)}   (i=8 or j=8 involved: {sum(1 for i,j in planes if 8 in (i,j))})"
)
# V on the sphere
vals = [potential(z / np.sqrt(2)) for *_, z, _ in zds]
print(f"V(z/√2): min {min(vals):.12f} max {max(vals):.12f} (expect 1)")
# singular values of L_z, R_z, ad_z for one canonical z (structure).  All are the full 16×16 matrices on 𝕊
# (real line included); ad_z = L_z − R_z on 𝕊 gives {4 ×4, 2√2 ×6, 0 ×6}, Σσ² = 112 (Red Team #676 F3).
z = E[1] + E[10]
for name, M in [
    ("L_z", L_matrix(z)),
    ("R_z", R_matrix(z)),
    ("ad_z", L_matrix(z) - R_matrix(z)),
    ("L_z+R_z", L_matrix(z) + R_matrix(z)),
]:
    sv = np.linalg.svd(M, compute_uv=False)
    print(f"  {name:8s} σ = {np.round(sv, 6).tolist()}   Σσ² = {np.sum(sv**2):.3f}")
# same spectrum for all 84?
specs = set()
for *_, zz, _ in zds:
    specs.add(tuple(np.round(np.linalg.svd(L_matrix(zz), compute_uv=False), 8)))
print(f"distinct L_z spectra over the 84: {len(specs)}")
# Jordan map degeneracy: xz+zx real for imaginary x
X = rng.normal(size=(50, 16))
X[:, 0] = 0
J = mul(X, z) + mul(z, X)
print(
    f"Jordan xz+zx on imaginary x: max |Im| = {np.abs(J[:,1:]).max():.1e}, Re = -2(x1+x10)? {np.allclose(J[:,0], -2*(X[:,1]+X[:,10]))}"
)


# ridge sanity: random V=1 points are ZDs?  (a ⊥ Im b, |a|=|Im b|, b0=0)
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


ranks = [np.linalg.matrix_rank(L_matrix(ridge_point()), 1e-9) for _ in range(20)]
print(f"random ridge points (V=1): rank L_x = {sorted(set(ranks))} (ZD ⇔ rank < 16)")
# G2 element check
ders = octonion_derivation_basis()
print(
    f"dim Der(𝕆) from basis pairs: {np.linalg.matrix_rank(np.array([d.ravel() for d in ders]), 1e-9)} (expect 14)"
)
Phi = random_g2_sedenion_aut(rng, ders)
print(
    f"random G₂ element: orthogonal {np.allclose(Phi.T@Phi, np.eye(16))}, automorphism residual (256 pairs) {aut_residual(Phi):.1e}, fixes ℓ {np.allclose(Phi@ELL, ELL)}"
)
json.dump(
    {
        "n_zd": len(zds),
        "planes": planes,
        "kernel_dims": kd,
        "V_on_sphere": [float(min(vals)), float(max(vals))],
    },
    open("out_zd_enum.json", "w"),
    indent=1,
)
