"""
#559 cross-coupling probe (addressing the RT + Gemini APPROVE-WITH-CONCERN on PR #561).
The earlier no-go was OVERCLAIMED: it only showed positive sum-of-squares actions are
single-well (trivial). SSB needs a SIGN-INDEFINITE (tachyonic) mass term. Two routes the
reviewers named: (i) cross-coupling y<->retained sector with a background; (ii) any
non-positive algebra invariant. Test both HONESTLY.

KEY STRUCTURAL FACT: the only natural real bilinear on the (division) octonions is the
inner product <a,b> = Re(a*conj(b)), which equals the EUCLIDEAN dot product (positive-
definite) -- the #474 NormForm 'D10' guardrail. We test whether cross-couplings to a
background can nonetheless induce an indefinite quadratic form on y.
"""

import numpy as np, numpy.linalg as la

rng = np.random.default_rng(2)


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


def oconj(A):
    return np.concatenate([qconj(A[:4]), -A[4:]])


def assoc(a, b, c):
    return omul(omul(a, b), c) - omul(a, omul(b, c))


def emb(y4):
    return np.concatenate([np.zeros(4), y4])


def inner(a, b):
    return float(a @ b)  # Euclidean inner product = Re(a conj(b))


b4 = [np.zeros(4) for _ in range(4)]
for k in range(4):
    b4[k][k] = 1.0


def quad_form(scalar_fn):
    """scalar_fn(y4)->R assumed quadratic in y; return its 4x4 symmetric matrix."""
    M = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            # polarization: S(ei+ej)-S(ei-ej) = 4 * y^T M (ei,ej)/... use finite eval
            ei, ej = b4[i], b4[j]
            M[i, j] = 0.25 * (scalar_fn(ei + ej) - scalar_fn(ei - ej))
    return 0.5 * (M + M.T)


def signature(M):
    ev = np.round(la.eigvalsh(M), 6)
    pos = int((ev > 1e-9).sum())
    neg = int((ev < -1e-9).sum())
    zer = int((abs(ev) <= 1e-9).sum())
    return ev, (pos, neg, zer)


print("Testing natural algebra-derived quadratic forms on y for SIGN-INDEFINITENESS:")
print("(an indefinite form => a tachyonic direction => SSB possible)\n")

x0_choices = {
    "x0=1": np.array([1.0, 0, 0, 0]),
    "x0=e1": np.array([0, 1.0, 0, 0]),
    "x0=generic": rng.standard_normal(4),
}
any_indefinite = False
for name, x0 in x0_choices.items():
    X = np.concatenate([x0, np.zeros(4)])
    forms = {
        "norm |y e4|^2": lambda y: inner(emb(y), emb(y)),
        "|X*(y e4)|^2": lambda y: inner(omul(X, emb(y)), omul(X, emb(y))),
        "|(y e4)*X|^2": lambda y: inner(omul(emb(y), X), omul(emb(y), X)),
        "|[X, y e4]|^2 (commutator)": lambda y: (lambda c: inner(c, c))(
            omul(X, emb(y)) - omul(emb(y), X)
        ),
        "|[X, y e4, X]|^2 (assoc)": lambda y: (lambda a: inner(a, a))(
            assoc(X, emb(y), X)
        ),
        "Re<X*(ye4), (ye4)*X> (cross, NOT a norm)": lambda y: inner(
            omul(X, emb(y)), omul(emb(y), X)
        ),
        "Re( conj(ye4) * X * (ye4) ) scalar part": lambda y: omul(
            omul(oconj(emb(y)), X), emb(y)
        )[0],
    }
    print(f"--- background {name} ---")
    for fname, fn in forms.items():
        M = quad_form(fn)
        ev, (p, n, z) = signature(M)
        indef = p > 0 and n > 0
        any_indefinite |= indef
        print(
            f"  {fname:42s} eig={ev}  sig(+,-,0)=({p},{n},{z}){'  <-- INDEFINITE!' if indef else ''}"
        )
    print()
print("ANY sign-indefinite (tachyon-capable) natural form found:", any_indefinite)
print(
    "\nInterpretation: if ALL natural forms are positive-(semi)definite, the EUCLIDEAN"
)
print("octonion norm forbids a tachyonic mass even WITH background cross-coupling ->")
print("SSB requires an INDEFINITE-signature structure (split-octonions / loss of the")
print(
    "positive-definite norm at the sedenion level), OR an externally-imposed wrong-sign mass."
)
