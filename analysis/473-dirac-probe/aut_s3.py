"""#473 AC1 round 7/8 — the S₃ factor of Aut(𝕊) = G₂ × S₃ (Brown 1967), concretely.

An automorphism commuting with G₂ must act on Im𝕊 = Im𝕆 ⊕ ℝℓ ⊕ Im𝕆·ℓ  (= 7 ⊕ 1 ⊕ 7 as a
G₂-module) through the commutant: a 2×2 matrix M on the multiplicity space of the 7 and a
scalar s on ℓ:   x₀ + a + b₀ℓ + cℓ  ↦  x₀ + (m₁₁a + m₁₂c) + s·b₀ℓ + (m₂₁a + m₂₂c)ℓ.
We solve φ(xy) = φ(x)φ(y) numerically for (M, s) and list the distinct solutions; then read
off how they act on the G₂-invariants (|a|², |Im b|², ⟨a,Im b⟩, b₀) and on the vacuum orbit
space.  Also checks that the unit zero-divisor locus δ = 1 is a single G₂-orbit (dim 11).
"""

import numpy as np
from scipy.optimize import least_squares

exec(open("dirac_probe.py").read().split("def spec")[0])  # cd_mul, basis, L, R

rng = np.random.default_rng(7)


def phi(p, x):
    m11, m12, m21, m22, s = p
    a, c = x[1:8], x[9:16]
    y = np.zeros(16)
    y[0] = x[0]
    y[1:8] = m11 * a + m12 * c
    y[8] = s * x[8]
    y[9:16] = m21 * a + m22 * c
    return y


X = rng.normal(size=(4, 16))
Y = rng.normal(size=(4, 16))


def resid(p):
    return np.concatenate(
        [phi(p, cd_mul(x, y)) - cd_mul(phi(p, x), phi(p, y)) for x, y in zip(X, Y)]
    )


sols = []
for _ in range(40):
    p0 = rng.normal(size=5) * 2
    r = least_squares(resid, p0, xtol=1e-14, ftol=1e-14, gtol=1e-14)
    if np.linalg.norm(r.fun) < 1e-9 and not any(
        np.linalg.norm(r.x - q) < 1e-6 for q in sols
    ):
        sols.append(r.x)
sols.sort(key=lambda q: (round(q[4]), round(q[0], 3), round(q[1], 3)))
print(f"distinct automorphisms commuting with G2: {len(sols)} (expect 6 = |S3|)")
for q in sols:
    M = q[:4].reshape(2, 2)
    print(
        f"  s = {q[4]:+.3f}   M = {np.round(M, 4).tolist()}   det M = {np.linalg.det(M):+.3f}"
    )

# action on the invariants: Gram matrix G = [[|a|²,⟨a,c⟩],[⟨a,c⟩,|c|²]] ↦ M G Mᵀ ; b0 ↦ s·b0
# vacuum orbit space: rank G ≤ 1, i.e. (a, c) = (cosθ, sinθ)·u ; θ ∈ RP¹ ↦ M·(cosθ, sinθ)
print("\naction on the vacuum orbit space (θ = direction in the (a, Im b) plane, b0):")
for q in sols:
    M = q[:4].reshape(2, 2)
    thetas = []
    for th in [0.0, np.pi / 2, np.pi / 4, -np.pi / 4]:
        v = M @ np.array([np.cos(th), np.sin(th)])
        thetas.append(np.degrees(np.arctan2(v[1], v[0])) % 180)
    print(
        f"  s={q[4]:+.0f}: θ ∈ (0°, 90°, 45°, -45°) ↦ {np.round(thetas, 1).tolist()}   b0 ↦ {q[4]:+.0f}·b0"
    )

# unit zero-divisor locus: δ = 1 ⇔ b0 = 0, |a|² = |Im b|² = 1/2, a ⟂ Im b.  One G2-orbit?
e8 = basis(8)


def Lm(x):
    return L(x, 8)


def Rm(x):
    return R(x, 8)


def D(x, y):
    return (
        (Lm(x) @ Lm(y) - Lm(y) @ Lm(x))
        + (Lm(x) @ Rm(y) - Rm(y) @ Lm(x))
        + (Rm(x) @ Rm(y) - Rm(y) @ Rm(x))
    )


ders = [D(e8[i], e8[j]) for i in range(1, 8) for j in range(i + 1, 8)]
a, c = e8[1] / np.sqrt(2), e8[2] / np.sqrt(2)
vecs = np.array([np.concatenate([d @ a, d @ c]) for d in ders])
zd_dim = int(np.linalg.matrix_rank(vecs, 1e-9))
# G2 acts transitively on orthonormal pairs in Im O (stabiliser SU(2)), so the locus
# {b0=0, |a|²=|c|²=1/2, a⊥c} is one orbit of dim 14-3.
print(
    f"\nzero-divisor ridge: G2-orbit dim at (e1+e2ℓ)/√2 = {zd_dim} (expect 11 = 14 - dim SU(2))"
)
print(
    "  the ridge is the single orbit of orthonormal pairs (a, Im b) — no finite data without a basis"
)
