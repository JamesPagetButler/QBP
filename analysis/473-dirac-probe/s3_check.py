"""#473 AC1 round 8 (relabelled after PR #631 review) — flow smoke test + S₃-consistency of
the #629 endpoints.

WHAT THIS TESTS, honestly.  V = 4·det Gram(a, Im b) is invariant under the FULL O(2) acting on
the (a, Im b) multiplicity plane (centraliser of G₂ in O(15) is O(2) × O(1)), not just under the
S₃ ⊂ O(2) of aut_s3.py; the round-metric gradient flow is O(2)-equivariant and the N-Haar initial
measure is O(15)-invariant.  So the endpoint angle θ (direction in the (a, Im b) plane, mod 180°)
must be UNIFORM on ℝP¹, and b₀ must be even.  Any 60°-periodic statistic therefore passes
automatically — this script cannot fail as an S₃ test (Red Team finding 4; Gemini agreed).  What
it does test: that `grad`/`step` in flow_big.py are implemented without an O(2)-breaking bug
(KS test of θ against Uniform[0,180), overall and in |b₀| bands), that b₀ is even, and that the
vacuum orbit space pinches at b₀ = ±1 (suspension of ℝP¹ = S²).  The actual S₃ verification is
the exact 256-basis-pair check in aut_s3.py.

Seeding: same seed VALUE as flow_big.py (rng(1)) but an independent stream — flow_big.py
consumes two FD-check draws before sampling, this script reseeds after the exec'd prefix — so
the 24 000 initial points differ from #629's.  The endpoint ⟨b₀²⟩ printed below is therefore an
independent re-measurement of #629's 0.1462 ± 0.0011 (1500 steps here vs 5000 there).
Set S3_CHECK_N=3000 for a ~1 min validation run; S3_CHECK_MU=μ for a Q_μ-Gaussian initial state.
"""

import os

import numpy as np
from scipy.stats import kstest

src = open("flow_big.py").read()
exec(src.split("# --- flow")[0])  # omul, V, grad, FD check

N = int(os.environ.get("S3_CHECK_N", "24000"))
rng = np.random.default_rng(1)
s = rng.normal(size=(N, 15))
# optional Q_μ-Gaussian initial state (Prop 7′ BOTE check): b₀ ~ N(0, 1/μ), then project to S¹⁴
MU = float(os.environ.get("S3_CHECK_MU", "1"))
s[:, 7] /= np.sqrt(MU)
s /= np.linalg.norm(s, axis=1, keepdims=True)
print(
    "N = %d   mu = %g   initial <b0^2> = %.4f  (BOTE (1/mu)/(14+1/mu) = %.4f)"
    % (N, MU, (s[:, 7] ** 2).mean(), (1 / MU) / (14 + 1 / MU))
)
a = np.concatenate([np.zeros((N, 1)), s[:, :7]], 1)
b = s[:, 7:].copy()


def step(a, b, dt):
    ga, gb = grad(a, b)
    s = np.concatenate([a[:, 1:], b], 1)
    g = np.concatenate([ga[:, 1:], gb], 1)
    g -= (g * s).sum(1, keepdims=True) * s
    s2 = s - dt * g
    s2 /= np.linalg.norm(s2, axis=1, keepdims=True)
    return np.concatenate([np.zeros((N, 1)), s2[:, :7]], 1), s2[:, 7:]


for it in range(1500):  # 0.3 s/step; V < 1e-6 well before this
    a, b = step(a, b, 0.02)
print("converged: max V =", V(a, b).max())
np.save("flow_end_big.npy", np.concatenate([a, b], 1))

b0 = b[:, 0]
c = b[:, 1:]
an = np.linalg.norm(a, axis=1)
cn = np.linalg.norm(c, axis=1)
# at a vacuum c = ±k a; θ = atan2(sign·|c|, |a|) with the sign of <a, c>
sgn = np.sign((a[:, 1:] * c).sum(1))
theta = np.degrees(np.arctan2(sgn * cn, an)) % 180.0
print(
    "endpoint <b0^2> = %.4f  (SE %.4f)" % ((b0**2).mean(), (b0**2).std() / np.sqrt(N))
)

# --- check 1: θ uniform on [0,180) (implied by O(2) ⊃ S₃; KS has a null, sector counts do not)
ks_all = kstest(theta / 180.0, "uniform")
print("KS θ vs Uniform[0,180): D = %.4f  p = %.3f" % (ks_all.statistic, ks_all.pvalue))
for lo, hi in [(0.0, 0.3), (0.3, 0.6), (0.6, 0.99)]:
    m = (np.abs(b0) >= lo) & (np.abs(b0) < hi)
    ks = kstest(theta[m] / 180.0, "uniform")
    print(
        "   |b0| in [%.2f,%.2f): n=%5d  KS D = %.4f  p = %.3f"
        % (lo, hi, m.sum(), ks.statistic, ks.pvalue)
    )
# --- (legacy) 60°-sector counts — implied by uniformity; kept as a sanity print only.
bins3 = np.histogram(theta, bins=[0, 60, 120, 180])[0]
print("θ in [0,60), [60,120), [120,180):", bins3.tolist(), " (expect equal within √N)")
# finer: the distribution of θ mod 60 should be the same in each of the three sectors
sec = (theta // 60).astype(int)
folded = theta % 60
hists = [np.histogram(folded[sec == k], bins=12, range=(0, 60))[0] for k in range(3)]
chi2 = sum(((h - np.mean(hists, 0)) ** 2 / np.mean(hists, 0)).sum() for h in hists)
print("chi² across the three sectors (12 bins each, dof≈22): %.1f" % chi2)
# --- check 2: b0 even (S₃ reflections, also implied by O(1) on the ℓ-axis).
print(
    "<b0> = %+.4f  (SE %.4f);  <b0^3> = %+.4f"
    % (b0.mean(), b0.std() / np.sqrt(N), (b0**3).mean())
)
# --- reflection axes: θ = 0, 60, 120 (Im b = 0 type) vs 30, 90, 150 (a = 0 type)
print(
    "fraction within 5° of {0,60,120}: %.3f ; of {30,90,150}: %.3f"
    % (
        (np.min(np.abs(theta[:, None] - np.array([0, 60, 120, 180])), 1) < 5).mean(),
        (np.min(np.abs(theta[:, None] - np.array([30, 90, 150])), 1) < 5).mean(),
    )
)
# --- topology: at b0 -> ±1, |a|, |c| -> 0 and θ is undefined (collapsed): suspension of RP^1
top = np.abs(b0) > 0.99
print(
    "points with |b0|>0.99: %d ; their max(|a|,|Im b|) = %.3e"
    % (top.sum(), np.maximum(an, cn)[top].max() if top.any() else 0)
)
