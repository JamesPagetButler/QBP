"""#639 / flag 3 — the holographic boundary of a universe U(s), candidate A, numerically.

For a crystal s = αu + (b₀ + γu)ℓ the hosted algebra is ℍ_s = span{1, ℓ, U, ℓU} (Lean:
CrystalHosting.vacuum_hosts_quaternion).  ℍ_s straddles both Cayley–Dickson halves of 𝕊
(ℓ = e₈ and ℓU lie in the high half), so ℍ_s is NOT inside the low-half octonions.  The
octonion subalgebras of 𝕊 that DO contain ℍ_s are the doublings

    𝕆'_v := ℍ'_v ⊕ ℍ'_v·ℓ,   ℍ'_v := span{1, u, v, uv},   v ⊥ u a unit imaginary octonion,

and inside each the "4D gap" ℍ_s^⊥ ∩ 𝕆'_v = span{V, UV, ℓV, ℓ(UV)} is the candidate boundary.
This script checks, for random u, v:
  (1) 𝕆'_v is closed under the sedenion product (rank 8, products inside to machine precision);
  (2) 𝕆'_v is alternative ((xx)y = x(xy) and (yx)x = y(xx)) — an octonion, not merely a subspace;
  (3) ℍ_s ⊂ 𝕆'_v, and dim ℍ_s^⊥ ∩ 𝕆'_v = 4 (the codimension-4 theorem, instantiated);
  (4) the boundary DEPENDS on v: for v' ⊥ {u, v, uv} the two gaps meet only in 0, and a random
      x ⊥ ℍ_s lies in no single 𝕆'_v — so "which octonion encodes the universe" is a datum
      the hosting definition does not yet carry (AXIOM-2 fixes the algebra type, not the copy).
Run: python3 analysis/473-dirac-probe/boundary_octonion_check.py
"""

import numpy as np, sys, os, io, contextlib

sys.path.insert(0, os.path.dirname(__file__))
with contextlib.redirect_stdout(
    io.StringIO()
):  # dirac_probe prints its own report on import
    from dirac_probe import cd_mul

rng = np.random.default_rng(639)
N = 16


def e(i):
    z = np.zeros(N)
    z[i] = 1.0
    return z


def lo(a8):  # embed an octonion (8-vector) in the low half
    z = np.zeros(N)
    z[:8] = a8
    return z


ell = e(8)


def unit_im_oct(perp=()):
    a = rng.normal(size=8)
    a[0] = 0
    for p in perp:
        a -= np.dot(a, p) * p
    return a / np.linalg.norm(a)


def span_basis(vecs):
    M = np.array(vecs)
    U, S, Vt = np.linalg.svd(M, full_matrices=False)
    r = int((S > 1e-9).sum())
    return Vt[:r], r


def in_span(B, x):
    return np.linalg.norm(x - B.T @ (B @ x)) < 1e-9


def mul(x, y):
    return cd_mul(x, y)


worst = {"closure": 0.0, "alt": 0.0}
for trial in range(5):
    u = unit_im_oct()
    v = unit_im_oct(perp=(u,))
    U, V = lo(u), lo(v)
    UV = mul(U, V)
    Hp = [e(0), U, V, UV]  # ℍ'_v
    Op = Hp + [mul(h, ell) for h in Hp]  # 𝕆'_v = ℍ' ⊕ ℍ'ℓ
    B, r = span_basis(Op)
    assert r == 8, r
    # (1) closure
    for x in Op:
        for y in Op:
            worst["closure"] = max(
                worst["closure"], np.linalg.norm(mul(x, y) - B.T @ (B @ mul(x, y)))
            )
    # (2) alternativity on random elements of 𝕆'_v
    for _ in range(20):
        x = B.T @ rng.normal(size=8)
        y = B.T @ rng.normal(size=8)
        worst["alt"] = max(
            worst["alt"],
            np.linalg.norm(mul(mul(x, x), y) - mul(x, mul(x, y))),
            np.linalg.norm(mul(mul(y, x), x) - mul(y, mul(x, x))),
        )
    # (3) ℍ_s ⊂ 𝕆'_v and the gap is 4-dim
    Hs = [e(0), ell, U, mul(ell, U)]
    assert all(in_span(B, h) for h in Hs)
    Bh, rh = span_basis(Hs)
    assert rh == 4
    gap = [b - Bh.T @ (Bh @ b) for b in B]  # project 𝕆'_v onto ℍ_s^⊥
    _, rg = span_basis(gap)
    assert rg == 4, rg
    # (4) v-dependence
    v2 = unit_im_oct(perp=(u, v, UV[:8] / np.linalg.norm(UV[:8])))
    V2 = lo(v2)
    Hp2 = [e(0), U, V2, mul(U, V2)]
    Op2 = Hp2 + [mul(h, ell) for h in Hp2]
    B2, _ = span_basis(Op2)
    gap2 = [b - Bh.T @ (Bh @ b) for b in B2]
    G1, _ = span_basis(gap)
    G2, _ = span_basis(gap2)
    _, rint = span_basis(list(G1) + list(G2))  # dim(G1 + G2) = 8 ⇒ G1 ∩ G2 = 0
    x = rng.normal(size=N)
    x -= Bh.T @ (Bh @ x)  # random x ⊥ ℍ_s
    print(
        f"trial {trial}: 𝕆'_v rank 8 ✓  ℍ_s ⊂ 𝕆'_v ✓  gap dim 4 ✓  dim(gap_v + gap_v') = {rint} "
        f"(disjoint ⇔ 8)  random x ⊥ ℍ_s in 𝕆'_v: {in_span(B, x)}  in 𝕆'_v': {in_span(B2, x)}"
    )
print(
    f"worst closure residual {worst['closure']:.1e}; worst alternativity residual {worst['alt']:.1e}"
)
# Contrast: the CD low half 𝕆 does NOT contain ℍ_s (ℓ is not in it)
print("ℓ in low-half 𝕆:", in_span(np.eye(N)[:8], ell))
# Contrast: 𝕊 itself is not alternative (sanity)
x = rng.normal(size=N)
y = rng.normal(size=N)
print(
    f"𝕊 alternativity residual (should be O(1)): {np.linalg.norm(mul(mul(x,x),y)-mul(x,mul(x,y))):.2f}"
)
