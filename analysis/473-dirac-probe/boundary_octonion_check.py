"""#639 / flag 3 — the holographic boundary of a universe U(s), candidate A, numerically.

For a crystal s = αu + (b₀ + γu)ℓ the hosted algebra is ℍ_s = span{1, ℓ, U, ℓU} (Lean:
CrystalHosting.vacuum_hosts_quaternion).  ℍ_s straddles both Cayley–Dickson halves of 𝕊
(ℓ = e₈ and ℓU lie in the high half), so ℍ_s is NOT inside the low-half octonions.  The
octonion subalgebras of 𝕊 that DO contain ℍ_s are the doublings

    𝕆'_v := ℍ'_v ⊕ ℍ'_v·ℓ,   ℍ'_v := span{1, u, v, uv},   v ⊥ u a unit imaginary octonion,

and inside each the "4D gap" ℍ_s^⊥ ∩ 𝕆'_v = span{V, UV, ℓV, ℓ(UV)} = ℍ_s·V is the candidate
boundary.  That these are ALL the octonion subalgebras of 𝕊 containing ℍ_s is a CONJECTURE
(numerically probed in (6), not proved).  This script checks, for random u, v:
  (1) 𝕆'_v is closed under the sedenion product (rank 8, products inside to machine precision);
  (2) 𝕆'_v is alternative ((xx)y = x(xy) and (yx)x = y(xx)) — an octonion, not merely a subspace;
  (3) ℍ_s ⊂ 𝕆'_v, and dim ℍ_s^⊥ ∩ 𝕆'_v = 4 (the codimension-4 theorem, instantiated);
  (4) the boundary DEPENDS on v: for v' ⊥ {u, v, uv} the two gaps meet only in 0 (they span 8),
      the gap depends only on the ℂ_u-line span{v, uv} (v and uv give the same 𝕆'_v), and a
      generic x ⊥ ℍ_s lies in no single 𝕆'_v — the union of the gaps is an 8-dim cone inside the
      12-dim ℍ_s^⊥ (4-dim fibres over the ℂP² of ℂ_u-lines in u^⊥ ≅ ℝ⁶);
  (5) ℍ_s^⊥ is a left ℍ_s-module: L_U, L_ℓ, L_{ℓU} preserve it — the v-free object the gaps
      are ℍ_s-lines in (Red Team #643 finding 6);
  (6) completeness probe: ℍ_s ⊕ ℍ_s·w for w ⊥ ℍ_s that mixes the two CD halves off a ℂ_u-line
      is NOT closed (so no octonion of that shape contains ℍ_s) — supports, does not prove, the
      conjecture that the 𝕆'_v are all of them.
Every claim above is ASSERTED (exit 1 on failure), not merely printed.
Run: python3 analysis/473-dirac-probe/boundary_octonion_check.py
"""

import numpy as np, sys, os, io, contextlib

sys.path.insert(0, os.path.dirname(__file__))
with contextlib.redirect_stdout(
    io.StringIO()
):  # dirac_probe prints its own report on import
    from dirac_probe import cd_mul


def main():
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
        _, S, Vt = np.linalg.svd(M, full_matrices=False)
        r = int((S > 1e-9).sum())
        return Vt[:r], r

    def in_span(B, x):
        return np.linalg.norm(x - B.T @ (B @ x)) < 1e-9

    mul = cd_mul
    worst = {"closure": 0.0, "alt": 0.0, "module": 0.0}
    min_mixed_residual = np.inf
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
                xy = mul(x, y)
                worst["closure"] = max(
                    worst["closure"], np.linalg.norm(xy - B.T @ (B @ xy))
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
        assert all(in_span(B, h) for h in Hs), "ℍ_s ⊄ 𝕆'_v"
        Bh, rh = span_basis(Hs)
        assert rh == 4
        gap = [b - Bh.T @ (Bh @ b) for b in B]  # project 𝕆'_v onto ℍ_s^⊥
        G1, rg = span_basis(gap)
        assert rg == 4, rg
        # (4) v-dependence, ℂ_u-line invariance, generic x outside every gap
        uv8 = UV[:8] / np.linalg.norm(UV[:8])
        v2 = unit_im_oct(perp=(u, v, uv8))
        V2 = lo(v2)
        Hp2 = [e(0), U, V2, mul(U, V2)]
        Op2 = Hp2 + [mul(h, ell) for h in Hp2]
        B2, _ = span_basis(Op2)
        G2, _ = span_basis([b - Bh.T @ (Bh @ b) for b in B2])
        _, rint = span_basis(list(G1) + list(G2))
        assert (
            rint == 8
        ), f"gaps for v' ⊥ {{u,v,uv}} should meet only in 0; dim(sum) = {rint}"
        Hp3 = [e(0), U, UV, mul(U, UV)]
        Op3 = Hp3 + [mul(h, ell) for h in Hp3]  # v ↦ uv
        B3, _ = span_basis(Op3)
        assert all(
            in_span(B3, b) for b in B
        ), "𝕆'_{uv} ≠ 𝕆'_v: the gap is not ℂ_u-line invariant"
        x = rng.normal(size=N)
        x -= Bh.T @ (Bh @ x)  # random x ⊥ ℍ_s
        assert not in_span(B, x) and not in_span(
            B2, x
        ), "generic x ⊥ ℍ_s landed in a gap"
        # (5) ℍ_s^⊥ is a left ℍ_s-module
        P = np.eye(N) - Bh.T @ Bh  # projector onto ℍ_s^⊥
        for h in (U, ell, mul(ell, U)):
            for _ in range(10):
                y = P @ rng.normal(size=N)
                worst["module"] = max(worst["module"], np.linalg.norm(Bh @ mul(h, y)))
        # (6) completeness probe: w ⊥ ℍ_s mixing the halves off a ℂ_u-line ⇒ ℍ_s ⊕ ℍ_s w not closed
        w = lo(v) + 0.7 * mul(lo(v2), ell)  # (v, 0.7·v')ℓ-mixed, v' ∉ span{v, uv}
        w -= Bh.T @ (Bh @ w)
        w /= np.linalg.norm(w)
        Sw = Hs + [mul(h, w) for h in Hs]
        Bw, rw = span_basis(Sw)
        assert rw == 8
        res = max(
            np.linalg.norm(mul(a, b) - Bw.T @ (Bw @ mul(a, b))) for a in Sw for b in Sw
        )
        min_mixed_residual = min(min_mixed_residual, res)
        print(
            f"trial {trial}: 𝕆'_v rank 8 ✓  ℍ_s ⊂ 𝕆'_v ✓  gap dim 4 ✓  dim(gap_v + gap_v') = {rint} ✓  "
            f"𝕆'_uv = 𝕆'_v ✓  generic x ⊥ ℍ_s in neither ✓  mixed-w closure residual {res:.2f}"
        )
    assert worst["closure"] < 1e-12, worst
    assert worst["alt"] < 1e-12, worst
    assert worst["module"] < 1e-12, worst
    assert (
        min_mixed_residual > 0.1
    ), "a mixed-halves w gave a closed algebra — completeness conjecture challenged"
    print(
        f"worst closure residual {worst['closure']:.1e}; worst alternativity residual {worst['alt']:.1e}; "
        f"worst ℍ_s-module residual {worst['module']:.1e}; min mixed-w closure residual {min_mixed_residual:.2f}"
    )
    # Contrast: the CD low half 𝕆 does NOT contain ℍ_s (ℓ is not in it)
    assert not in_span(np.eye(N)[:8], ell)
    print("ℓ in low-half 𝕆: False ✓")
    # Contrast: 𝕊 itself is not alternative (sanity)
    x = rng.normal(size=N)
    y = rng.normal(size=N)
    r = np.linalg.norm(mul(mul(x, x), y) - mul(x, mul(x, y)))
    assert r > 1.0
    print(f"𝕊 alternativity residual (should be O(1)): {r:.2f} ✓")
    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
