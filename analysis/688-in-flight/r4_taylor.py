import numpy as np

src = open("r4_numerics.py").read()
exec(
    src.split("# ---------- 4.")[0].replace("print(", "(lambda *a,**k: None)(")
)  # sections 0-3 silently
lam = 8 * (1 - b0**2)
print("lambda_perp =", lam)
print(
    "V(s0+t n) fitted to c2 t^2 + c3 t^3 + c4 t^4 along normal directions (exact quartic, 6 sample points):"
)
for k in range(6):
    n = Nb @ rng.normal(size=6)
    n /= np.linalg.norm(n)
    ts = np.array([0.05, 0.1, 0.15, 0.2, 0.25, 0.3])
    vals = np.array([V(s0 + t * n) for t in ts])
    A = np.column_stack([ts**2, ts**3, ts**4])
    c = np.linalg.lstsq(A, vals, rcond=None)[0]
    print(f"  dir {k}: c2={c[0]:.6f} (λ/2={lam/2:.6f})  c3={c[1]:.2e}  c4={c[2]:.5f}")
# also along a mixed direction (normal + crystal-tangent) to show c3 is not identically zero on the full tangent
m = Nb[:, 0] + Tc[:, 0]
m /= np.linalg.norm(m)
ts = np.array([0.05, 0.1, 0.15, 0.2, 0.25, 0.3])
vals = np.array([V(s0 + t * m) for t in ts])
c = np.linalg.lstsq(np.column_stack([ts**2, ts**3, ts**4]), vals, rcond=None)[0]
print(f"  mixed normal+tangent dir: c2={c[0]:.6f} c3={c[1]:.4f} c4={c[2]:.4f}")
