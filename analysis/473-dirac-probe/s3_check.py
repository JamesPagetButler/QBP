"""#473 AC1 round 8 — S₃ consistency check on the #629 flow endpoints.

Aut(𝕊) = G₂ × S₃ acts on the vacuum orbit space (θ = direction in the (a, Im b) plane mod
180°, b₀) by θ ↦ θ ± 120° and b₀ ↦ −b₀ (aut_s3.py).  The gradient flow of V is
Aut-equivariant and the N-round (Haar) initial measure is Aut-invariant, so the endpoint
distribution must be 60°-periodic in θ and even in b₀.  This re-runs the #629 flow
(flow_big.py, same seed) and tests both — a free check that #629 and aut_s3.py agree.
Also confirms the vacuum orbit space is the suspension of ℝP¹ (a 2-sphere): θ collapses at
b₀ = ±1.
"""

import numpy as np

src = open("flow_big.py").read()
exec(src.split("# --- flow")[0])  # omul, V, grad, FD check

N = 24000
rng = np.random.default_rng(1)
s = rng.normal(size=(N, 15))
s /= np.linalg.norm(s, axis=1, keepdims=True)
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
print("endpoint <b0^2> = %.4f" % (b0**2).mean())

# --- S3 check 1: 60°-periodicity of θ.  Fold θ mod 60 and compare the three 60° bins.
bins3 = np.histogram(theta, bins=[0, 60, 120, 180])[0]
print("θ in [0,60), [60,120), [120,180):", bins3.tolist(), " (expect equal within √N)")
# finer: the distribution of θ mod 60 should be the same in each of the three sectors
sec = (theta // 60).astype(int)
folded = theta % 60
hists = [np.histogram(folded[sec == k], bins=12, range=(0, 60))[0] for k in range(3)]
chi2 = sum(((h - np.mean(hists, 0)) ** 2 / np.mean(hists, 0)).sum() for h in hists)
print("chi² across the three sectors (12 bins each, dof≈22): %.1f" % chi2)
# --- S3 check 2: b0 even.
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
