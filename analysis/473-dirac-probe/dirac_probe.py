"""Flashlight probe for #473 lit-path step 1: candidate algebraic Dirac operators
over the CD cascade H -> O -> S.  Numerical only (numpy); NOT a proof.

CD recursion (Schafer convention, matches proofs/QBP/Foundations/CDAlg.lean):
  (a,b)(c,d) = (ac - conj(d) b,  d a + b conj(c))
"""

import numpy as np, itertools, sys


def cd_mul(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate(
        [cd_mul(a, c) - cd_mul(conj(d), b), cd_mul(d, a) + cd_mul(b, conj(c))]
    )


def conj(x):
    y = -x.copy()
    y[0] = x[0]
    return y


def basis(n):
    return [np.eye(n)[i] for i in range(n)]


def L(s, n):
    """matrix of left multiplication by s on the n-dim CD algebra"""
    return np.column_stack([cd_mul(s, e) for e in basis(n)])


def R(s, n):
    return np.column_stack([cd_mul(e, s) for e in basis(n)])


def spec(M, tol=1e-9):
    w = np.linalg.eigvals(M)
    w = np.sort_complex(np.round(w, 6))
    vals, counts = np.unique(w, return_counts=True)
    return list(zip(vals, counts))


np.set_printoptions(linewidth=160, precision=4, suppress=True)

for n, name in [(4, "H"), (8, "O"), (16, "S")]:
    print(f"\n===== {name} (dim {n}) =====")
    # sanity: basis units square to -1 and quasi-group closure
    E = basis(n)
    ok = all(np.allclose(cd_mul(E[a], E[a]), -E[0]) for a in range(1, n))
    print("e_a^2 = -1 for all a:", ok)
    # Gemini's D = i * sum_a L_{e_a} = i * L_s
    s = sum(E[1:])
    Ls = L(s, n)
    D2 = -(Ls @ Ls)  # (i L_s)^2 = -L_s^2
    print("spectrum of D^2 = -L_s^2  (s = sum of imaginary units):")
    print("  ", spec(D2))
    print("  is D^2 = (n-1) I ?", np.allclose(D2, (n - 1) * np.eye(n)))
    # linearised left-alternative defect: Delta = sum_{a<b} {L_a, L_b}
    Delta = sum(
        L(E[a], n) @ L(E[b], n) + L(E[b], n) @ L(E[a], n)
        for a in range(1, n)
        for b in range(a + 1, n)
    )
    print("  Delta = sum_{a<b} {L_a,L_b}  spectrum:", spec(Delta))
    # D^2 = (n-1) I - Delta  check
    print("  D^2 == (n-1)I - Delta ?", np.allclose(D2, (n - 1) * np.eye(n) - Delta))
    # covariance probe: random unit s instead of sum of units
    rng = np.random.default_rng(0)
    for trial in range(2):
        r = rng.normal(size=n)
        r[0] = 0
        r /= np.linalg.norm(r)
        Lr = L(r, n)
        print(f"  random imaginary unit s, spectrum of -L_s^2:", spec(-(Lr @ Lr)))
    # G2-covariant alternative: Casimir-type  C = -sum_a L_a^2  and  -sum_a (L_a - R_a)^2 (ad-type)
    C = -sum(L(E[a], n) @ L(E[a], n) for a in range(1, n))
    print("  C = -sum_a L_a^2 spectrum:", spec(C))
    AD = -sum(
        (L(E[a], n) - R(E[a], n)) @ (L(E[a], n) - R(E[a], n)) for a in range(1, n)
    )
    print("  ad-Casimir -sum_a ad(e_a)^2 spectrum:", spec(AD))
    # associator-based operator on the algebra: T_a = L_a R_a - R_a L_a ... skip

# Where does the ledger Hessian {0,4,8,12}x{16,4,8,4} live?  32-dim => pairs.
# Probe: the norm-composition defect  g(x,y) = N(xy) - N(x)N(y)  Hessian at (x,y)=(e0,e0)? -> need a stationary pt.
# Cheap probe: Hessian of the squared associator  a(x) = |[x,x?]|  -- leave for the lean side.
