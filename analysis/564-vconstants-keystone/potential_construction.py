"""
#564 Sub-problem A: build the crystallisation potential V(y) from the verified #559
ingredients and characterise its minimum. Sub-problem C: is R_αμ scale-independent?

V(y) = a|y|^2  +  b * Re<X(y e4),(y e4)X>  +  c (|y|^2)^2
  - |y|^2: the Euclidean octonion norm (positive).
  - Re<X(ye4),(ye4)X>: the #559 NON-COMMUTATIVE cross-coupling, NEGATIVE-definite for
    imaginary background X (this is the algebra-supplied negative mass term).
  - c(|y|^2)^4-term: the quartic that stabilises (lowest SO(4)-invariant quartic = (|y|^2)^2).
"""

import numpy as np, numpy.linalg as la

rng = np.random.default_rng(3)


def qmul(p, q):
    w0, x0, y0, z0 = p
    w1, x1, y1, z1 = q
    return np.array(
        [
            w0 * w1 - x0 * x1 - y0 * y1 - z0 * z1,
            w0 * x1 + x0 * w1 + y0 * z1 - z0 * y1,
            w0 * y1 - x0 * z1 + y0 * w1 + z0 * x1,
            w0 * z1 + x0 * y1 - y0 * x1 + z0 * w1,
        ]
    )


def qconj(p):
    return np.array([p[0], -p[1], -p[2], -p[3]])


def omul(A, B):
    p, q = A[:4], A[4:]
    r, s = B[:4], B[4:]
    return np.concatenate(
        [qmul(p, r) - qmul(qconj(s), q), qmul(s, p) + qmul(q, qconj(r))]
    )


def emb(y4):
    return np.concatenate([np.zeros(4), y4])


def inner(a, b):
    return float(a @ b)


b4 = [np.eye(4)[k] for k in range(4)]


def crossM(X):  # matrix of Re<X(ye4),(ye4)X> in y
    M = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            f = lambda y: inner(
                omul(np.concatenate([X, np.zeros(4)]), emb(y)),
                omul(emb(y), np.concatenate([X, np.zeros(4)])),
            )
            M[i, j] = 0.25 * (f(b4[i] + b4[j]) - f(b4[i] - b4[j]))
    return 0.5 * (M + M.T)


print("=== M(X) signature for various backgrounds (the negative-mass source) ===")
for name, X in [
    ("X=e1 (imag unit)", np.array([0, 1.0, 0, 0])),
    ("X=1 (real unit)", np.array([1.0, 0, 0, 0])),
    ("X=(1+e1)/sqrt2 (mixed)", np.array([1, 1.0, 0, 0]) / np.sqrt(2)),
    ("X=imag generic", np.concatenate([[0], rng.standard_normal(3)])),
]:
    M = crossM(X)
    ev = np.round(la.eigvalsh(M), 4)
    print(
        f"  {name:26s} eig={ev}  (|X|^2={inner(X,X):.3f})  -> isotropic={np.allclose(ev,ev[0])}"
    )

# So for imaginary X: M = -|X|^2 I  (isotropic negative). Quadratic mass term coefficient:
# V(y) = (a - b|X_im|^2)|y|^2 + c(|y|^2)^2  for imaginary background, |X_im|^2 = m.
print("\n=== V(y) is a Mexican hat iff the negative cross-coupling dominates ===")


def vev(a, b, m, c):
    mass2 = a - b * m  # coefficient of |y|^2
    if mass2 >= 0:
        return 0.0, mass2
    return np.sqrt((b * m - a) / (2 * c)), mass2  # |y|_min


for a, b, m, c in [(1.0, 0.5, 1.0, 0.1), (1.0, 2.0, 1.0, 0.1), (0.5, 1.0, 3.0, 0.2)]:
    v, mass2 = vev(a, b, m, c)
    print(
        f"  a={a},b={b},|X|^2={m},c={c}: mass^2={mass2:+.3f} -> {'MEXICAN HAT, v=%.4f'%v if v>0 else 'no SSB (v=0)'}"
    )

# === Sub-problem C: is R_alpha,mu scale-independent? ===
# If a constant couples to the VEV as a POWER LAW  f(v) = f0 * v^p, then
#   dln f/dln v = p  (CONSTANT, independent of v and of all potential coefficients).
#   R_ab = (dln A/dv)/(dln B/dv) = p_A / p_B   -> a pure RATIO OF EXPONENTS, scale-free.
print("\n=== Sub-problem C: R_ab structure ===")
print("If alpha(v)=a0*v^p_alpha and mu(v)=m0*v^p_mu (power-law coupling to the VEV),")
print("then R_alpha,mu = (dln alpha/dln v)/(dln mu/dln v) = p_alpha/p_mu :")
for pa, pmu in [(1, -1), (2, -1), (1, 1), (-1, 2)]:
    print(
        f"   p_alpha={pa:+d}, p_mu={pmu:+d}  ->  R = {pa/pmu:+.4f}   (scale-INDEPENDENT)"
    )
print(
    "\n=> R is independent of the absolute VEV v AND of the potential coefficients (a,b,c,|X|)"
)
print(
    "   IFF the couplings are power laws. The falsifiable number reduces to the EXPONENTS,"
)
print(
    "   i.e. to Sub-problem B (how each constant couples to the (2,2)) -- NOT the hard scale."
)
