"""P2 vs P2′ audit, confirmer finding 1 — the Cayley–Dickson "cell" is NOT canonical.

There is an order-3 automorphism ρ of 𝕊 that FIXES ℓ and rotates the two octonion halves into
each other: on Im𝕆_low, a ↦ cos(2π/3)·a + sin(2π/3)·(aℓ); on Im𝕆_low·ℓ, aℓ ↦ −sin(2π/3)·a +
cos(2π/3)·(aℓ); 1 and ℓ fixed. (This is an order-3 element of the S₃ factor of Aut(𝕊) — master's aut_s3.py already exhibits it as
rot(120°, s = +1); it fixes ℓ, so CrystalHosting.aut_hosting_equivariant already applies to it, and it
fixes each ℍ_s as a set, acting on it as the inner automorphism x ↦ q̄xq, q = cos(π/3) + sin(π/3)ℓ.) Consequences asserted here:
  (1) ρ is an algebra automorphism (multiplicative on random pairs), ρ³ = id, ρ ≠ id, ρ(ℓ) = ℓ;
  (2) ρ(𝕆_low) is a closed octonion subalgebra of 𝕊 DIFFERENT from 𝕆_low (rank(𝕆_low ∪ ρ𝕆_low) = 15);
  (3) ρ preserves the crystal condition: V(ρ s) = V(s) on random states, so V = 0 ⇔ V(ρs) = 0 —
      the crystal does not pick a half;
  (4) for a crystal s, ℍ_s ∩ ρ(𝕆_low) is a DIFFERENT ℂ inside ℍ_s than ℍ_s ∩ 𝕆_low = span{1, U}:
      the three halves {𝕆_low, ρ𝕆_low, ρ²𝕆_low} meet ℍ_s in three ℂ's at 120° in the (U, Uℓ)-plane.
So "the cell" under P2′ is a choice in a ℤ/3-torsor: one DISCRETE root, not zero.
Run: python3 analysis/473-dirac-probe/p2_cell_torsor_check.py
"""

import numpy as np, sys, os

sys.path.insert(0, os.path.dirname(__file__))
from dirac_probe import cd_mul


def main():
    rng = np.random.default_rng(3)
    N = 16
    c, s = np.cos(2 * np.pi / 3), np.sin(2 * np.pi / 3)
    R = np.zeros((N, N))
    R[0, 0] = 1
    R[8, 8] = 1
    for k in range(1, 8):  # a = e_k (low), aℓ = e_{k+8} (high)  [e_k · e_8 = e_{k+8}]
        R[k, k] = c
        R[k + 8, k] = s
        R[k, k + 8] = -s
        R[k + 8, k + 8] = c
    rho = lambda x: R @ x
    e = lambda i: np.eye(N)[i]
    # e_k * e_8 = ± e_{k+8}: fix the sign convention so that "aℓ" means the actual product a·ℓ
    for k in range(1, 8):
        prod = cd_mul(e(k), e(8))
        sgn = prod[k + 8]
        assert abs(abs(sgn) - 1) < 1e-12 and abs(np.linalg.norm(prod) - 1) < 1e-12
        if sgn < 0:  # re-express the rotation in the (e_k, e_k·ℓ) basis
            R[k + 8, k] = -s
            R[k, k + 8] = s
    # (1) automorphism, order 3, fixes ℓ
    worst = 0.0
    for _ in range(200):
        x = rng.normal(size=N)
        y = rng.normal(size=N)
        worst = max(worst, np.linalg.norm(rho(cd_mul(x, y)) - cd_mul(rho(x), rho(y))))
    assert worst < 1e-12, worst
    assert np.linalg.norm(np.linalg.matrix_power(R, 3) - np.eye(N)) < 1e-12
    assert np.linalg.norm(R - np.eye(N)) > 1
    assert np.linalg.norm(rho(e(8)) - e(8)) < 1e-12
    # (2) ρ(𝕆_low) ≠ 𝕆_low, closed
    low = np.eye(N)[:8]
    rlow = np.array([rho(v) for v in low])
    assert np.linalg.matrix_rank(np.vstack([low, rlow]), tol=1e-9) == 15
    B = rlow / np.linalg.norm(rlow, axis=1, keepdims=True)
    closure = max(
        np.linalg.norm(cd_mul(a, b) - B.T @ (B @ cd_mul(a, b)))
        for a in rlow
        for b in rlow
    )
    assert closure < 1e-12, closure

    # (3) V invariant: V(ρ s) = V(s)
    def V(x):
        a = np.r_[x[:8], np.zeros(8)]
        b = np.r_[x[8:], np.zeros(8)]
        return float(np.sum((cd_mul(a, b) - cd_mul(b, a)) ** 2))

    # NB: V is the CD-commutator form, defined w.r.t. the low/high split; invariance under ρ is checked, not assumed
    dv = 0.0
    for _ in range(200):
        x = rng.normal(size=N)
        x[0] = 0
        x /= np.linalg.norm(x)
        dv = max(dv, abs(V(rho(x)) - V(x)))
    assert dv < 1e-10, dv
    # (4) for a crystal s = αu + (b₀ + γu)ℓ: ℍ_s ∩ ρ(𝕆_low) is a different ℂ than span{1, U}
    u = rng.normal(size=8)
    u[0] = 0
    u /= np.linalg.norm(u)
    U = np.r_[u, np.zeros(8)]
    ell = e(8)
    ellU = cd_mul(ell, U)
    Hs = np.array([e(0), ell, U, ellU])

    def intersect(Bsub):
        # dimension of ℍ_s ∩ span(Bsub) via rank
        return (
            4 + Bsub.shape[0] - np.linalg.matrix_rank(np.vstack([Hs, Bsub]), tol=1e-9)
        )

    assert intersect(low) == 2 and intersect(rlow) == 2
    # the two ℂ's differ: span{1,U} ∩ ρ(𝕆_low) is 1-dim (just the reals)
    assert (
        2 + 8 - np.linalg.matrix_rank(np.vstack([np.array([e(0), U]), rlow]), tol=1e-9)
        == 1
    )
    print("ρ: automorphism (residual %.1e), order 3, ρ(ℓ) = ℓ ✓" % worst)
    print("ρ(𝕆_low) is a closed octonion subalgebra ≠ 𝕆_low (rank of union 15) ✓")
    print(
        "V(ρ s) = V(s) on 200 random states (max dev %.1e): the crystal does not pick a half ✓"
        % dv
    )
    print(
        "ℍ_s meets 𝕆_low and ρ(𝕆_low) in two DIFFERENT ℂ's (each 2-dim; common part = ℝ) ✓"
    )
    print(
        "ALL ASSERTIONS PASSED — under P2′ 'the cell' is a ℤ/3-torsor choice, one discrete root"
    )


if __name__ == "__main__":
    main()
