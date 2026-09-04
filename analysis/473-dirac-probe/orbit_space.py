"""#473 AC1 v0.1 — the G₂ orbit space of S¹⁴ ⊂ Im𝕊 and the descent of the δ-landscape.

Checks (numerically; the committed evidence behind Props 5–6 of
docs/foundations/473-ac1-first-link-v0.1.md):

  (1) the 21 standard derivations D_{e_i,e_j} of 𝕆 span a 14-dim space (= 𝔤₂) and are
      derivations of the octonion product;
  (2) G₂ acting diagonally on Im𝕊 = Im𝕆 ⊕ 𝕆 (s = a + bℓ ↦ Da + (Db)ℓ) has generic
      orbit dimension 11, so the orbit space S¹⁴/G₂ is 3-dimensional;
  (3) the landscape potential V(s) = δ² = ‖[a,b]‖² equals 4(|a|²|Im b|² − ⟨a,Im b⟩²),
      i.e. a function of the three invariants (|a|², b₀, ⟨a,Im b⟩) only — so the
      gradient flow of #629 descends to the orbit space.

Also writes hvr_orbit_space.png: V over the orbit space (slices in ⟨a,Im b⟩), with the
vacuum locus and the zero-divisor ridge marked.  Numerical flashlight only.
"""

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

exec(open("dirac_probe.py").read().split("def spec")[0])  # cd_mul, basis, L, R

rng = np.random.default_rng(473)
e8 = basis(8)


def Lm(x):
    return L(x, 8)


def Rm(x):
    return R(x, 8)


def D(x, y):
    """Standard inner derivation of an alternative algebra."""
    return (
        (Lm(x) @ Lm(y) - Lm(y) @ Lm(x))
        + (Lm(x) @ Rm(y) - Rm(y) @ Lm(x))
        + (Rm(x) @ Rm(y) - Rm(y) @ Rm(x))
    )


ders = [D(e8[i], e8[j]) for i in range(1, 8) for j in range(i + 1, 8)]
g2_dim = np.linalg.matrix_rank(np.array([d.ravel() for d in ders]), 1e-9)
x, y = rng.normal(size=8), rng.normal(size=8)
leib = max(
    np.abs(d @ cd_mul(x, y) - cd_mul(d @ x, y) - cd_mul(x, d @ y)).max() for d in ders
)
print(
    f"(1) dim span D_(ei,ej) = {g2_dim} (expect 14 = dim g2); Leibniz residual {leib:.1e}"
)

# (2) generic orbit dimension on Im S
orbit_dims = []
for _ in range(5):
    a = np.concatenate([[0.0], rng.normal(size=7)])
    b = rng.normal(size=8)
    vecs = np.array([np.concatenate([d @ a, d @ b]) for d in ders])
    orbit_dims.append(int(np.linalg.matrix_rank(vecs, 1e-9)))
print(
    f"(2) generic G2 orbit dim on Im S: {orbit_dims} -> S^14/G2 has dim {14 - orbit_dims[0]}"
)

# (3) V descends: delta^2 = 4(|a|^2 |Im b|^2 - <a,Im b>^2)
worst = 0.0
for _ in range(2000):
    s = rng.normal(size=16)
    s[0] = 0.0
    s /= np.linalg.norm(s)
    a, b = s[:8], s[8:]
    d2 = np.linalg.norm(cd_mul(a, b) - cd_mul(b, a)) ** 2
    imb = b.copy()
    imb[0] = 0.0
    worst = max(worst, abs(d2 - 4 * (a @ a * (imb @ imb) - (a @ imb) ** 2)))
print(
    f"(3) max |delta^2 - 4(|a|^2|Im b|^2 - <a,Im b>^2)| over 2000 Haar samples: {worst:.1e}"
)

# ---------- HVR plot: V on the orbit space ----------
# coordinates on S^14/G2: A = |a|^2, B0 = b_0, P = <a, Im b>, with |Im b|^2 = 1 - A - B0^2
# and the constraint P^2 <= A * |Im b|^2 (Cauchy-Schwarz).
fig, axes = plt.subplots(1, 3, figsize=(13, 4.2), sharey=True)
A = np.linspace(0, 1, 301)
B0 = np.linspace(-1, 1, 301)
AA, BB = np.meshgrid(A, B0)
IMB2 = 1 - AA - BB**2
for ax, pfrac in zip(axes, [0.0, 0.5, 0.9]):
    # P = pfrac * sqrt(A |Im b|^2): pfrac = 0 (a ⟂ Im b), ... , 0.9 (nearly parallel)
    with np.errstate(invalid="ignore"):
        V = 4 * (AA * IMB2) * (1 - pfrac**2)
    V[IMB2 < 0] = np.nan
    im = ax.contourf(AA, BB, V, levels=np.linspace(0, 1, 21), cmap="viridis")
    ax.contour(AA, BB, V, levels=[1e-3], colors="white", linewidths=1.2)
    ax.set_title(
        rf"$\langle a,\mathrm{{Im}}\,b\rangle = {pfrac}\cdot\sqrt{{|a|^2|\mathrm{{Im}}\,b|^2}}$"
    )
    ax.set_xlabel(r"$|a|^2$")
axes[0].set_ylabel(r"$b_0$")
# zero-divisor ridge: A = |Im b|^2 = 1/2, b0 = 0, P = 0 -> V = 1
axes[0].plot([0.5], [0.0], "r*", ms=12, label=r"ZD ridge: $V=1$")
axes[0].plot([0, 1], [0, 0], "w:", lw=0.8)
axes[0].legend(loc="lower left", fontsize=8)
fig.suptitle(
    r"$V=\delta^2$ on the 3-dim orbit space $S^{14}/G_2$ (invariants $|a|^2,\ b_0,\ \langle a,\mathrm{Im}\,b\rangle$);"
    "  white = vacua $V=0$ (the a=0 / Im b=0 / a∥Im b edges)",
    fontsize=10,
    y=1.06,
)
fig.colorbar(im, ax=axes, shrink=0.9, label=r"$V=\delta^2$")
fig.savefig("hvr_orbit_space.png", dpi=130, bbox_inches="tight")
print("wrote hvr_orbit_space.png")
