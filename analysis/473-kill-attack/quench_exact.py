"""ATTACK 1 / leg C — the quench endpoint in closed form (derived in attack1_anneal_vs_quench.md §3a):
under the sphere-projected gradient flow of V = 4(AC - D²), the invariants A=|a|², C=|c|², D=<a,c>, B=b0²
obey A' = 2A-1, C' = 2C-1, D' = 2D, B' = 2B in the time dτ = 4V dt, i.e. they move on a straight ray until V=0:
      b0²_end = B0 / (B0 + sqrt((1-B0)² - V0)).
Hence <b0²>_quench = E_Haar[ B/(B + (1-B) sqrt(1 - 4κ)) ],  κ = t(1-t) sin²φ  (same Haar reduction as leg A).
(1) 3-d quadrature, no MC;  (2) 10^7 Haar points with V from flowlib.potential (no reduction), closed form applied per point.
"""

import time
import numpy as np
from scipy import integrate, special
from flowlib import potential, random_states

out = open("quench_exact_out.txt", "w")


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    out.write(s + "\n")
    out.flush()


def endpoint(B, V0):
    return B / (B + np.sqrt(np.maximum((1 - B) ** 2 - V0, 0.0)))


# (1) quadrature.  inner(B) = E_{t,φ}[ h(B,κ) ],  f_t ∝ t^{5/2}(1-t)^{5/2},  f_φ ∝ sin^5 φ
def inner(B):
    def over_phi(t):
        k = t * (1 - t)
        f = (
            lambda ph: np.sin(ph) ** 5
            * B
            / (B + (1 - B) * np.sqrt(max(1 - 4 * k * np.sin(ph) ** 2, 0.0)))
        )
        return integrate.quad(f, 0, np.pi, limit=200, points=[np.pi / 2])[0] / (16 / 15)

    g = lambda t: t**2.5 * (1 - t) ** 2.5 * over_phi(t)
    return integrate.quad(g, 0, 1, limit=200, points=[0.5])[0] / special.beta(3.5, 3.5)


t0 = time.time()
Z = integrate.quad(lambda b: (1 - b * b) ** 6, 0, 1)[0]
Q = (
    integrate.quad(
        lambda b: (1 - b * b) ** 6 * inner(b * b), 0, 1, limit=200, epsabs=1e-9
    )[0]
    / Z
)
Qinit = integrate.quad(lambda b: (1 - b * b) ** 6 * b * b, 0, 1)[0] / Z
P(
    "quadrature: <b0^2>_init = %.7f (1/15 = %.7f);  <b0^2>_quench (closed form) = %.6f   [%.0f s]"
    % (Qinit, 1 / 15, Q, time.time() - t0)
)

# (2) Monte Carlo over Haar with the full sedenion potential
rng = np.random.default_rng(31415)
NT, CH = 10_000_000, 500_000
s1 = s2 = 0.0
n = 0
maxdev = 0.0
q = []
for _ in range(NT // CH):
    s = random_states(CH, rng)
    V0 = potential(s)
    a, c = s[:, 1:8], s[:, 9:16]
    Vcf = 4 * ((a * a).sum(1) * (c * c).sum(1) - (a * c).sum(1) ** 2)
    maxdev = max(maxdev, np.abs(V0 - Vcf).max())
    e = endpoint(s[:, 8] ** 2, V0)
    s1 += e.sum()
    s2 += (e * e).sum()
    n += CH
    if len(q) < 4:
        q.append(e)
m = s1 / n
se = np.sqrt((s2 / n - m * m) / n)
q = np.concatenate(q)
P("MC 1e7 Haar, V = flowlib.potential:  max |V - 4(AC-D^2)| = %.1e" % maxdev)
P(
    "MC <b0^2>_quench = %.5f +- %.5f ;  quantiles(0.1,.25,.5,.75,.9) = %s"
    % (m, se, np.array2string(np.quantile(q, [0.1, 0.25, 0.5, 0.75, 0.9]), precision=4))
)
P(
    "on-record quench numbers: flow_big/#629 0.1462+-0.0011, s3_check seed 2 0.1454+-0.0011, 0.1436+-0.0011"
)
out.close()
