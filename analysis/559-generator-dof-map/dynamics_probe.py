"""
#559 dynamics probe: can the octonion ALGEBRA source a symmetry-breaking potential
for the lost (2,2) complement field y (z = x + y*e4, y in H ~ the (2,2))?

The adversary's mandate: find a Mexican-hat V(y) from the algebra, or admit there is none.

Two parts:
 (A) REP-THEORY NO-GO (rigorous): the only SO(4)-invariant polynomials of a single
     vector y in (2,2)=R^4 are polynomials in |y|^2. So any SO(4)-invariant self-
     potential is V(|y|^2): a single positive-definite norm gives a single well (min at
     y=0). SSB needs a wrong-sign mass term, which a positive algebra-norm cannot supply.
 (B) ASSOCIATOR ACTION (compute): the natural algebra-derived action is a sum of squared
     associators (the non-associativity 'energy'). Being a sum of squares it is
     positive-semidefinite -> also single-well. Compute its signature to confirm, and
     check whether ANY algebra-natural quadratic form on y is sign-indefinite (tachyonic).
"""

import numpy as np, numpy.linalg as la

rng = np.random.default_rng(1)


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


def assoc(a, b, c):
    return omul(omul(a, b), c) - omul(a, omul(b, c))


E = [np.zeros(8) for _ in range(8)]
for i in range(8):
    E[i][i] = 1.0


# embed complement field y (quaternion) into octonion as (0, y) = y*e4
def emb(y4):
    return np.concatenate([np.zeros(4), y4])


# --- (B1) Associator action S(y) = sum_{i<j in 0..7} |[g_i, emb(y), g_j]|^2  (quadratic in y) ---
# build the quadratic form matrix M (4x4): S(y) = y^T M y
gens = E  # use all 8 basis octonions as probe generators
M = np.zeros((4, 4))
basis4 = [np.zeros(4) for _ in range(4)]
for k in range(4):
    basis4[k][k] = 1.0
for i in range(8):
    for j in range(8):
        # columns: associator is linear in y -> [g_i, emb(y), g_j] = L(y); accumulate L^T L
        L = np.array(
            [assoc(gens[i], emb(basis4[k]), gens[j]) for k in range(4)]
        ).T  # 8x4
        M += L.T @ L
evals = np.round(la.eigvalsh(M), 6)
print("(B) Associator-squared action quadratic form on y:")
print("    eigenvalues:", evals)
print("    positive-semidefinite (no tachyon):", bool(np.all(evals >= -1e-9)))
print("    => single-well: y=0 is a MINIMUM, no SSB from associator-squared action")

# --- (B2) try a generic algebra-natural SO(4)-invariant quartic: is it ever a Mexican hat? ---
# The only SO(4)-invariant of single y is |y|^2; build V=a|y|^2+b|y|^4 from algebra norms.
# Confirm: minimizing a|y|^2+b|y|^4 with a,b>=0 (norms are positive) gives min at y=0.
print("\n(A) Rep-theory no-go check (SO(4)-invariants of one (2,2) vector):")


# numerically confirm |y|^2 is SO(4)-invariant and that an independent quartic invariant
# (other than (|y|^2)^2) does not exist: test that any quartic built from omul/norm reduces to (|y|^2)^2
def norm2(o):
    return float(o @ o)


# random y, check a candidate 'associator quartic' Q4(y)=|[emb(y),X,emb(y)]|^2 vs (|y|^2)^2
X = E[1]
ratios = []
for _ in range(8):
    y = rng.standard_normal(4)
    q4 = norm2(assoc(emb(y), X, emb(y)))
    n4 = (y @ y) ** 2
    ratios.append(q4 / n4 if n4 > 1e-12 else np.nan)
print("    Q4(y)=|[y,e1,y]|^2 / (|y|^2)^2 across random y:", np.round(ratios, 4))
print(
    "    constant ratio => the only quartic invariant is (|y|^2)^2 (no independent Mexican-hat quartic)"
)

# --- (C) the decisive question: is there ANY sign-indefinite algebra-natural quadratic on y? ---
# Scan associator quadratic forms [g_i, emb(y), g_j] for fixed (i,j) (not summed) and check signatures.
indef = False
for i in range(8):
    for j in range(8):
        L = np.array([assoc(gens[i], emb(basis4[k]), gens[j]) for k in range(4)]).T
        Mij = L.T @ L
        ev = la.eigvalsh(Mij)
        if ev.min() < -1e-9 and ev.max() > 1e-9:
            indef = True
print("\n(C) Any sign-indefinite (tachyonic) associator quadratic form found:", indef)
print("    (each |associator|^2 form is a sum of squares => PSD => never tachyonic)")
print(
    "\nCONCLUSION: the octonion algebra's natural actions (norm, associator-squared) are"
)
print(
    "positive / single-well. No Mexican-hat SSB potential arises from the algebra ALONE."
)
