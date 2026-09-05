"""#473 AC1 v0.4, Prop 16(ii) — what the algebra's operations on (s, ℓ) can and cannot do.

Committed after PR #631 Red Team round 3 (finding 27), which falsified the round-12 claim
"every (s, ℓ)-map is a finite-order symmetry, none attracting": s ↦ (s + ℓ)/‖s + ℓ‖ is an
(s, ℓ)-map of infinite order that attracts everything to the vacuum ℓ.  The correct, stronger
statement, checked here:

  (1) for an imaginary unit s, {1, s, ℓ} generate a QUATERNION subalgebra
      ℍ_s = span{1, ℓ, p, ℓp}, p := s − b₀ℓ  (dimension 4; multiplication closes);
  (2) on Im ℍ_s the vacuum SHAPE invariant  σ(s) := V(s)/(1 − b₀²)²  is constant — the
      algebra's operations on (s, ℓ) move only b₀ and the overall (a, Im b) scale, never the
      shape of the (a, Im b) pair (its Gram matrix up to scale);
  (3) hence the only vacua reachable from a non-vacuum s by (s, ℓ)-words are ±ℓ; every other
      vacuum (a ∥ Im b with |a| + |Im b| > 0) is unreachable;
  (4) the three maps of round 12 (sℓ, ℓ(sℓ), [s,ℓ]) re-checked, plus normalize(s + ℓ), which
      is NOT of finite order and converges to ℓ (b₀ → 1, V → 0).
Also confirms the CD-coordinate formulas: sℓ = (−b, a), ℓs = (−b̄, −a), [s,ℓ] = −2c + 2aℓ.
Numerical flashlight; the Lean statement is the next step (span closure of a 4-dim subspace).
"""

import numpy as np

exec(open("dirac_probe.py").read().split("def spec")[0])  # cd_mul, conj, basis
exec(open("flow_big.py").read().split("# --- FD check")[0])  # omul, V

rng = np.random.default_rng(16)
e = np.eye(16)
ell = e[8]
one = e[0]


def nz(v):
    return v / np.linalg.norm(v)


def Vs(s):
    return V(np.concatenate([[0.0], s[1:8]])[None, :], s[8:][None, :])[0]


def shape(s):
    b0 = s[8]
    return Vs(s) / (1 - b0**2) ** 2 if abs(b0) < 1 - 1e-9 else np.nan


def rand_unit_imag():
    s = rng.normal(size=16)
    s[0] = 0
    return nz(s)


# (1) quaternion closure of {1, s, ℓ}
dims, closure_res = [], 0.0
for _ in range(20):
    s = rand_unit_imag()
    p = s - s[8] * ell
    B = np.stack([one, ell, p, cd_mul(ell, p)], 1)  # candidate basis of ℍ_s
    dims.append(np.linalg.matrix_rank(B, 1e-9))
    for i in range(4):
        for j in range(4):
            prod = cd_mul(B[:, i], B[:, j])
            coef = np.linalg.lstsq(B, prod, rcond=None)[0]
            closure_res = max(closure_res, np.abs(B @ coef - prod).max())
print(
    f"(1) dim span{{1,ℓ,p,ℓp}} = {set(dims)} (expect {{4}}); closure residual {closure_res:.1e}"
)

# (2) shape invariant constant on Im ℍ_s (random elements of the subalgebra)
spread = 0.0
for _ in range(20):
    s = rand_unit_imag()
    p = s - s[8] * ell
    lp = cd_mul(ell, p)
    sig0 = shape(s)
    for _ in range(50):
        x, y, z = rng.normal(size=3)
        w = nz(x * ell + y * p + z * lp)
        sig = shape(w)
        if not np.isnan(sig):
            spread = max(spread, abs(sig - sig0))
print(f"(2) max |σ(w) − σ(s)| over Im ℍ_s: {spread:.1e}  (σ = V/(1−b0²)²)")

# (3) reachable vacua: V = 0 within ℍ_s only at b0 = ±1 unless σ(s) = 0
s = rand_unit_imag()
p = s - s[8] * ell
lp = cd_mul(ell, p)
minV = 1.0
for _ in range(20000):
    x, y, z = rng.normal(size=3)
    w = nz(x * ell + y * p + z * lp)
    if abs(w[8]) < 0.99:
        minV = min(minV, Vs(w) / (1 - w[8] ** 2) ** 2)
print(
    f"(3) min V/(1−b0²)² over 2·10⁴ elements of Im ℍ_s with |b0|<0.99: {minV:.6f} vs σ(s) = {shape(s):.6f}"
)

# (4) the maps
S = np.array([rand_unit_imag() for _ in range(500)])


def report(name, f, imag_required=True):
    out = np.array([f(s) for s in S])
    realpart = np.abs(out[:, 0]).max()
    dV = np.abs([Vs(o) - Vs(s) for o, s in zip(out, S)]).max()
    # order: f^k = ±id for k ≤ 4?
    ords = []
    for s in S[:50]:
        x = s.copy()
        k = None
        for it in range(1, 5):
            x = f(x)
            if min(np.abs(x - s).max(), np.abs(x + s).max()) < 1e-9:
                k = it
                break
        ords.append(k)
    print(
        f"  {name:16s} max real part {realpart:.1e}  max|ΔV| {dV:.1e}  order(±) ≤4 in first 50: {sorted(set(ords), key=str)}"
    )


maps = {
    "s·ℓ": lambda s: nz(cd_mul(s, ell)),
    "ℓ·s": lambda s: nz(cd_mul(ell, s)),
    "ℓ(sℓ)": lambda s: nz(cd_mul(ell, cd_mul(s, ell))),
    "[s,ℓ]": lambda s: nz(cd_mul(s, ell) - cd_mul(ell, s)),
    "(s+ℓ)/‖s+ℓ‖": lambda s: nz(s + ell),
}
print("(4) maps on unit imaginary s (order None = not of finite order ≤ 4):")
for n, f in maps.items():
    report(n, f)
# iterate normalize(s+ℓ): converges to ℓ
s = rand_unit_imag()
traj = [s[8]]
for _ in range(30):
    s = nz(s + ell)
    traj.append(s[8])
print(
    f"    iterate (s+ℓ)/‖s+ℓ‖: b0 = {traj[0]:.3f} → {traj[5]:.4f} → {traj[30]:.6f};  V at end {Vs(s):.1e}  (→ vacuum ℓ)"
)

# CD-coordinate formulas
s = rand_unit_imag()
a, b0, c = s[1:8], s[8], s[9:16]
sl, ls = cd_mul(s, ell), cd_mul(ell, s)
comm = sl - ls
ok = (
    np.isclose(sl[0], -b0)
    and np.allclose(sl[1:8], -c)
    and np.allclose(sl[9:16], a)
    and np.isclose(ls[0], -b0)
    and np.allclose(ls[1:8], c)
    and np.allclose(ls[9:16], -a)
    and np.allclose(comm[1:8], -2 * c)
    and np.isclose(comm[8], 0)
    and np.allclose(comm[9:16], 2 * a)
)
print(f"CD formulas sℓ = (−b, a), ℓs = (−b̄, −a), [s,ℓ] = −2c + 2aℓ: {ok}")
