"""ATTACK 1 / leg A — exact (quadrature) Gibbs anneal on S^14 with weight e^{-beta V}.

Reduction (attack1_anneal_vs_quench.md §1b): with x = (a, b0, c), a,c in R^7, on S^14,
  dσ_{S^14} = (1-b0²)^6 db0 dΩ_13,   (a,c) = r ω, r² = 1-b0², ω ∈ S^13,
  ω = (√t p, √(1-t) q):  t ~ Beta(7/2,7/2),  p,q iid uniform on S^6,  cos φ = <p,q> has density ∝ sin^5 φ,
  V = 4 r^4 κ,  κ = t(1-t) sin²φ.
So  <b0²>_β = ∫ db0 (1-b0²)^6 b0² I(β,(1-b0²)²) / ∫ db0 (1-b0²)^6 I(β,(1-b0²)²),
    I(β,x) = ∫_0^1 dt t^{5/2}(1-t)^{5/2} J(4 β x t(1-t)),   J(μ) = ∫_0^π sin^5φ e^{-μ sin²φ} dφ = ∫_0^1 w²(1-w)^{-1/2} e^{-μ w} dw.
No Monte Carlo anywhere. Independent of the Hessian/tube derivation (§1a).

Numerics: composite Gauss-Legendre with geometric panel refinement toward the boundary layers (t ~ 1/(βx), 1-b0 ~ β^{-1/2}).
[v1 used scipy.integrate.quad with weight='alg'; it silently under-resolved the t-boundary layer for βx ≳ 10³ (1–2 % low,
 caught by the Laplace-constant check β³x³ I → 2π/64). Replaced.]
J(μ): μ < 60 via Kummer  B(3,½) e^{-μ} 1F1(½;7/2;μ);  μ ≥ 60 via the convergent series Σ_k C(2k,k)4^{-k} Γ(k+3) μ^{-(k+3)} (k ≤ 40).
"""

import numpy as np
from scipy import integrate, special

B35 = special.beta(3, 0.5)  # 16/15
_k = np.arange(41)
_ck = special.comb(2 * _k, _k) / 4.0**_k * special.gamma(_k + 3)


def J(mu):
    mu = np.asarray(mu, dtype=float)
    out = np.empty_like(mu)
    lo = mu < 60
    out[lo] = B35 * np.exp(-mu[lo]) * special.hyp1f1(0.5, 3.5, mu[lo])
    m = mu[~lo][:, None]
    out[~lo] = (_ck / m ** (_k + 3)).sum(1)
    return out


def J_quad(mu):  # reference, scalar
    return integrate.quad(
        lambda w: w * w * (1 - w) ** -0.5 * np.exp(-mu * w),
        0,
        1,
        limit=400,
        points=[min(0.9, 40 / max(mu, 1))],
    )[0]


_xs, _ws = np.polynomial.legendre.leggauss(32)


def panels(edges):
    a, b = edges[:-1, None], edges[1:, None]
    return (0.5 * (b - a) * _xs + 0.5 * (b + a)).ravel(), (0.5 * (b - a) * _ws).ravel()


# t = sin²ψ, ψ ∈ (0, π/2); symmetric about π/4; geometric panels toward ψ = 0
_psi, _wpsi = panels(np.concatenate([[0], np.geomspace(1e-10, np.pi / 4, 300)]))
_t = np.sin(_psi) ** 2
_wt = (
    _wpsi * 2 * np.sin(_psi) * np.cos(_psi) * _t**2.5 * (1 - _t) ** 2.5 * 2
)  # ×2 for the mirror half
_tt = _t * (1 - _t)


def I(beta, x):
    return float(np.sum(_wt * J(4 * beta * x * _tt)))


# b0 ∈ (0,1) (even integrand): s = 1 - b0, geometric panels toward s = 0
_s, _ws_ = panels(np.concatenate([[0], np.geomspace(1e-10, 1.0, 300)]))
_b = 1 - _s


def moments(beta):
    f = np.array([(1 - b * b) ** 6 * I(beta, (1 - b * b) ** 2) for b in _b])
    z = np.sum(_ws_ * f)
    m = np.sum(_ws_ * f * _b**2)
    return m / z, z


if __name__ == "__main__":
    out = open("anneal_quadrature_out.txt", "w")

    def P(*a):
        s = " ".join(str(x) for x in a)
        print(s)
        out.write(s + "\n")
        out.flush()

    errs = [
        abs(J(np.array([mu]))[0] / J_quad(mu) - 1)
        for mu in [0, 0.5, 3, 10, 50, 59.9, 60.1, 200, 1e3, 1e4, 1e6]
    ]
    P(
        "J(mu) vectorised vs reference quad, mu in [0, 1e6]: max rel err = %.2e"
        % max(errs)
    )
    P(
        "Beta(7/2,7/2) normalisation check: I(0,x)/J(0) = %.12f vs B(7/2,7/2) = %.12f"
        % (I(0, 1.0) / J(np.array([0.0]))[0], special.beta(3.5, 3.5))
    )
    P(
        "beta=0 b0-weight check: ∫(1-b²)^6 b² / ∫(1-b²)^6 = %.10f  (1/15 = %.10f)"
        % (
            np.sum(_ws_ * (1 - _b**2) ** 6 * _b**2) / np.sum(_ws_ * (1 - _b**2) ** 6),
            1 / 15,
        )
    )
    for beta in [1e3, 1e5, 1e7]:
        P(
            "beta=%.0e  beta^3 x^3 I(beta,x) at x=1: %.6f  x=0.25: %.6f   (Laplace limit 2pi/64 = %.6f)"
            % (
                beta,
                beta**3 * I(beta, 1.0),
                beta**3 * 0.25**3 * I(beta, 0.25),
                2 * np.pi / 64,
            )
        )
    P("\nbeta       <b0^2>_beta     deficit d=1/3-<b0^2>     d*sqrt(beta)")
    for beta in [
        0,
        2,
        5,
        10,
        20,
        40,
        80,
        160,
        320,
        1000,
        3000,
        1e4,
        3e4,
        1e5,
        1e6,
        1e7,
    ]:
        m, z = moments(beta)
        d = 1 / 3 - m
        P(
            "%-9g  %.6f        %+.6f              %.4f"
            % (beta, m, d, d * np.sqrt(beta) if beta > 0 else float("nan"))
        )
    P("beta=0 exact 1/15 = %.6f" % (1 / 15))
    P(
        "on-record importance sampling (gibbs_check.py): beta=5: 0.121, 10: 0.167, 40: 0.245, 160: 0.290(+-0.03)"
    )
    P("\nb0-density relative to b0=0 (uniform limit = 1.000):")
    P("beta      b0=0.3    b0=0.6    b0=0.9    b0=0.99")
    for beta in [100, 1e4, 1e6]:
        r0 = I(beta, 1.0)
        vals = [
            (1 - b * b) ** 6 * I(beta, (1 - b * b) ** 2) / r0
            for b in [0.3, 0.6, 0.9, 0.99]
        ]
        P("%-8g  %.4f    %.4f    %.4f    %.4f" % (beta, *vals))
    out.close()
