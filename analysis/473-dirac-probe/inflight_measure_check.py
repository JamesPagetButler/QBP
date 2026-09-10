"""AXIOM-2 demotion, round 6 — does the horn-1 ensemble put any mass on crystals at Γ = 0?

POST-hosting (history form): every universe's history passes through the in-flight region V > 0.
Gemini's proposed kill: the ruled initial ensemble (horn 1 = the surface measure of N on the
imaginary unit sphere S¹⁴ ⊂ Im𝕊) places all its measure on the vacuum manifold V = 0.
Dimension count: a vacuum is s = a + bℓ with a = α·u, Im b = γ·u (Prop 15, Lean
CrystalHosting.vacuum_iff_parametrised), so the vacuum locus in S¹⁴ is parametrised by
u ∈ S⁶ (6 dims) and (α, γ, b₀) on S² (2 dims): an 8-dimensional subset of a 14-manifold,
hence surface-measure ZERO. So the kill cannot fire. NOTE (confirmer delta, package v0.4 §9c):
this does NOT derive POST-hosting from the ruling — horn 1 already lives on the level-16
sphere, and one level down (𝕆, every state a crystal) the same kill FIRES; the measure argument
re-expresses POST-hosting as the level lower bound. POST-hosting remains a root.
This script checks the dimension count numerically (rank of the Jacobian of the vacuum
parametrisation) and samples the ensemble: fraction of Haar-random imaginary unit sedenions
with V below a threshold, and the distribution of V.  Every claim is asserted.
Run: python3 analysis/473-dirac-probe/inflight_measure_check.py
"""

import numpy as np, sys, os

sys.path.insert(0, os.path.dirname(__file__))
from dirac_probe import cd_mul


def V(s):
    a = np.zeros(8)
    b = np.zeros(8)
    a[:] = s[:8]
    b[:] = s[8:]
    ab = cd_mul(np.r_[a, np.zeros(8)], np.r_[b, np.zeros(8)])[:8]
    ba = cd_mul(np.r_[b, np.zeros(8)], np.r_[a, np.zeros(8)])[:8]
    return float(np.sum((ab - ba) ** 2))


def vacuum(u, alpha, gamma, b0):
    s = np.zeros(16)
    s[:8] = alpha * u
    s[8] = b0
    s[8:] += gamma * u
    return s


def main():
    rng = np.random.default_rng(473)
    # (1) sampled vacua really have V = 0
    for _ in range(50):
        u = rng.normal(size=8)
        u[0] = 0
        u /= np.linalg.norm(u)
        p = rng.normal(size=3)
        p /= np.linalg.norm(p)
        s = vacuum(u, *p)
        assert abs(np.linalg.norm(s) - 1) < 1e-12 and s[0] == 0
        assert V(s) < 1e-24, V(s)
    # (2) dimension of the vacuum locus: Jacobian rank of (u ∈ S⁶, (α,γ,b₀) ∈ S²) ↦ s, at random points
    ranks = []
    for _ in range(20):
        u = rng.normal(size=8)
        u[0] = 0
        u /= np.linalg.norm(u)
        p = rng.normal(size=3)
        p /= np.linalg.norm(p)
        eps = 1e-6
        cols = []
        # tangent directions on S⁶ (7-dim ambient Im𝕆 minus radial) and S²
        for k in range(1, 8):
            du = np.zeros(8)
            du[k] = 1
            du -= np.dot(du, u) * u
            if np.linalg.norm(du) < 1e-9:
                continue
            du /= np.linalg.norm(du)
            cols.append(
                (vacuum(u + eps * du, *p) - vacuum(u - eps * du, *p)) / (2 * eps)
            )
        for k in range(3):
            dp = np.zeros(3)
            dp[k] = 1
            dp -= np.dot(dp, p) * p
            if np.linalg.norm(dp) < 1e-9:
                continue
            dp /= np.linalg.norm(dp)
            cols.append(
                (vacuum(u, *(p + eps * dp)) - vacuum(u, *(p - eps * dp))) / (2 * eps)
            )
        J = np.array(cols).T
        ranks.append(np.linalg.matrix_rank(J, tol=1e-6))
    assert max(ranks) == 8 and min(ranks) == 8, ranks
    # (3) the ensemble: Haar-random imaginary unit sedenions
    N = 20000
    Vs = []
    for _ in range(N):
        s = rng.normal(size=16)
        s[0] = 0
        s /= np.linalg.norm(s)
        Vs.append(V(s))
    Vs = np.array(Vs)
    frac6 = float(np.mean(Vs < 1e-6))
    frac3 = float(np.mean(Vs < 1e-3))
    assert frac6 == 0.0, frac6
    print(
        f"vacuum locus: Jacobian rank = 8 at 20 random points (8-dim in the 14-dim state sphere) ✓"
    )
    print(
        f"horn-1 ensemble, N = {N}: fraction with V < 1e-6 = {frac6:.5f} ✓ (zero);  V < 1e-3: {frac3:.5f}"
    )
    print(
        f"V distribution: min {Vs.min():.4f}, median {np.median(Vs):.4f}, mean {Vs.mean():.4f}, max {Vs.max():.4f} (ridge V = 1)"
    )
    print(
        "ALL ASSERTIONS PASSED — the kill 'born crystallised' cannot fire under horn 1"
    )


if __name__ == "__main__":
    main()
