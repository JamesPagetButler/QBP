"""Human-Visual-Review artifacts for PR #629 (requested by the Red Team review):

  (1) δ(s) = ‖[a,b]‖ histogram over Haar-random unit imaginary sedenions, with the
      closed-form Haar mean ⟨δ²⟩ = 56/85 marked;
  (2) spectrum of −L_s² along a one-parameter path from an octonion-subalgebra
      direction (δ = 0) to a zero-divisor direction (δ = 1): the 16 eigenvalues
      should trace {1−δ ×4, 1 ×8, 1+δ ×4}, i.e. the 4/8/4 structure that the
      Sprint-12 ledger Hessian carries.

Numerical flashlight only.  Writes hvr_delta_hist.png and hvr_spectrum_vs_delta.png.
"""

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

exec(open("dirac_probe.py").read().split("def spec")[0])  # cd_mul, conj, basis, L, R

rng = np.random.default_rng(473)
N = 16


def split(s):
    return s[:8], s[8:]


def delta(s):
    a, b = split(s)
    return np.linalg.norm(cd_mul(a, b) - cd_mul(b, a))


# ---------- (1) Haar histogram ----------
M = 20000
S = rng.normal(size=(M, 15))
S /= np.linalg.norm(S, axis=1, keepdims=True)
deltas = np.array([delta(np.concatenate([[0.0], s])) for s in S])
mean_d2 = float(np.mean(deltas**2))
print(f"<delta^2> Haar, {M} samples: {mean_d2:.4f}  vs 56/85 = {56/85:.4f}")

fig, ax = plt.subplots(figsize=(7, 4))
ax.hist(deltas, bins=60, color="#4a6fa5", alpha=0.85, density=True)
ax.axvline(
    np.sqrt(56 / 85),
    color="#c0392b",
    lw=2,
    ls="--",
    label=r"$\sqrt{56/85}$ (closed form)",
)
ax.axvline(
    np.sqrt(mean_d2),
    color="#111",
    lw=1,
    ls=":",
    label=r"$\sqrt{\langle\delta^2\rangle_{sample}}$",
)
ax.set_xlabel(
    r"$\delta(s) = \|[a,b]\|$   (unit imaginary sedenion $s = a + b\ell$, Haar on $S^{14}$)"
)
ax.set_ylabel("density")
ax.set_title(
    r"Alternativity defect over $S^{14}$ (Haar): vacua $\delta=0$ are measure-zero; ridge at $\delta=1$"
)
ax.set_xlim(0, 1.05)
ax.legend()
fig.tight_layout()
fig.savefig("hvr_delta_hist.png", dpi=130)

# ---------- (2) spectrum along a δ path ----------
e = basis(N)
s0 = (e[1] + e[9]) / np.sqrt(
    2
)  # a = e1, b = e1 : [a,b] = 0  -> octonion subalgebra direction
s1 = (e[1] + e[10]) / np.sqrt(2)  # a = e1, b = e2 : zero-divisor direction, δ = 1
ts = np.linspace(0, 1, 41)
rows = []
for t in ts:
    s = (1 - t) * s0 + t * s1
    s /= np.linalg.norm(s)
    Lm = L(s, N)
    w = np.sort(np.linalg.eigvalsh(-(Lm @ Lm)))
    rows.append((delta(s), w))
rows.sort(key=lambda r: r[0])
d = np.array([r[0] for r in rows])
W = np.array([r[1] for r in rows])

fig, ax = plt.subplots(figsize=(7, 4.5))
for k in range(N):
    ax.plot(d, W[:, k], color="#4a6fa5", lw=1.2, alpha=0.8)
ax.plot(d, 1 - d, "r--", lw=1, label=r"$1-\delta$  (×4)")
ax.plot(d, 1 + d, "r--", lw=1, label=r"$1+\delta$  (×4)")
ax.axhline(1, color="gray", ls=":", lw=1, label="1  (×8)")
ax.set_xlabel(
    r"$\delta(s)$ along the path  $e_1+e_9 \to e_1+e_{10}$  (renormalised to $S^{14}$)"
)
ax.set_ylabel(r"eigenvalues of $-L_s^2$")
ax.set_title(
    r"$-L_s^2 = I + T_s$: spectrum $\{1-\delta\,(4),\ 1\,(8),\ 1+\delta\,(4)\}$ — the ledger's 4/8/4"
)
ax.legend(loc="upper left")
fig.tight_layout()
fig.savefig("hvr_spectrum_vs_delta.png", dpi=130)

# check the 4/8/4 count at the endpoint
w_end = W[-1]
print(
    "delta at end:",
    round(d[-1], 6),
    " spectrum counts:",
    int(np.sum(np.isclose(w_end, 0, atol=1e-6))),
    int(np.sum(np.isclose(w_end, 1, atol=1e-6))),
    int(np.sum(np.isclose(w_end, 2, atol=1e-6))),
)
