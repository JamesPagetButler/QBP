"""Cayley–Dickson algebra helpers shared by the #473 Dirac-probe scripts (numpy, numerical only).

Extracted under #632 (housekeeping) at master 86dbbd2 so the scripts in this directory import a
plain module instead of ``exec(open("dirac_probe.py").read().split(...)[0])`` — a convention that
was cwd-dependent, marker-string-dependent and silently ran the exec'd prefix's side effects.

Provenance — every function body below is lifted VERBATIM (numerics untouched) from:

  * ``dirac_probe.py`` (master 226a3b1, PR #629):  cd_mul, conj, basis, L, R, spec
  * ``flow_big.py``   (master 226a3b1, PR #629):  M8 (octonion structure tensor), omul, V, grad,
                                                 and the finite-difference gradient check
                                                 (here ``grad_fd_check``)
  * ``delta_formula.py`` (master 226a3b1, PR #629): T(s) = left alternator (here ``alternator``)
                                                 and delta(s) (here ``delta_max``)
  * ``landscape.py``  (master 226a3b1, PR #629):  hess (here ``fd_hessian``)
  * ``orbit_space.py`` / ``aut_s3.py`` (master 163ea98, PR #631): the standard inner derivation D

CD recursion (Schafer convention, matches proofs/QBP/Foundations/CDAlg.lean):
  (a,b)(c,d) = (ac - conj(d) b,  d a + b conj(c))

Coordinates: a 2n-vector x = (a, b) is a + b·ℓ with ℓ the new unit; index 0 is the real part.
For sedenions (dim 16): a = coords 0..7 (octonion), b = coords 8..15, b₀ = coord 8 = ℓ-component.

This module deliberately has NO import-time side effects (no seeding, no printing, no
``np.set_printoptions``): none of the former exec'd prefixes propagated set_printoptions to the
importing scripts, so importing from here keeps their stdout byte-identical.
"""

from __future__ import annotations

import numpy as np

# --------------------------------------------------------------------------- core (dirac_probe.py)


def cd_mul(x, y):
    """Cayley–Dickson product of two same-length vectors (length a power of two)."""
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return np.concatenate(
        [cd_mul(a, c) - cd_mul(conj(d), b), cd_mul(d, a) + cd_mul(b, conj(c))]
    )


def conj(x):
    """CD conjugation: negate every coordinate except the real part (index 0)."""
    y = -x.copy()
    y[0] = x[0]
    return y


def basis(n):
    """Standard basis e_0 .. e_{n-1} of the n-dim CD algebra as a list of vectors."""
    return [np.eye(n)[i] for i in range(n)]


def L(s, n):
    """matrix of left multiplication by s on the n-dim CD algebra"""
    return np.column_stack([cd_mul(s, e) for e in basis(n)])


def R(s, n):
    """matrix of right multiplication by s on the n-dim CD algebra"""
    return np.column_stack([cd_mul(e, s) for e in basis(n)])


def spec(M, tol=1e-9):
    """Eigenvalues of M rounded to 6 places, as a list of (value, multiplicity)."""
    w = np.linalg.eigvals(M)
    w = np.sort_complex(np.round(w, 6))
    vals, counts = np.unique(w, return_counts=True)
    return list(zip(vals, counts))


# ------------------------------------------------ vectorised octonion product (flow_big.py)

_E8 = basis(8)
M8 = np.zeros((8, 8, 8))  # (x y)_k = M8[i,j,k] x_i y_j
for _i in range(8):
    for _j in range(8):
        M8[_i, _j] = cd_mul(_E8[_i], _E8[_j])


def omul(x, y):
    """Row-wise octonion product of two (n, 8) arrays via the structure tensor."""
    return np.einsum("ni,nj,ijk->nk", x, y, M8)


def V(a, b):
    """Landscape potential V = ‖[a, b]‖² row-wise, for (n, 8) arrays a, b."""
    c = omul(a, b) - omul(b, a)
    return (c * c).sum(1)


def grad(a, b):
    """Analytic gradient of V w.r.t. (a, b); the a-gradient is projected onto Im O."""
    # V=|c|^2, c=ab-ba ; dV = 2<c, da b - b da> + 2<c, a db - db a>
    # <xy,z>=<x,z ybar>, <yx,z>=<x,ybar z>  (valid in every CD algebra)
    c = omul(a, b) - omul(b, a)
    bb = b.copy()
    bb[:, 1:] *= -1
    ab = a.copy()
    ab[:, 1:] *= -1
    ga = 2 * (omul(c, bb) - omul(bb, c))
    ga[:, 0] = 0  # a imaginary: project
    gb = 2 * (omul(ab, c) - omul(c, ab))
    return ga, gb


def grad_fd_check(rng, h=1e-6):
    """The flow_big.py finite-difference check of ``grad``, verbatim.

    Draws ONE imaginary a and ONE b from ``rng`` (two ``rng.normal(size=(1, 8))`` calls, in
    that order — callers that go on to sample from the same ``rng`` depend on this draw order)
    and returns ``(ok_a, ok_b)``: ``np.allclose`` of the analytic against the central-difference
    gradient at atol 1e-5.
    """
    a = rng.normal(size=(1, 8))
    a[:, 0] = 0
    b = rng.normal(size=(1, 8))
    ga, gb = grad(a, b)
    fd = []
    for k in range(8):
        da = np.zeros((1, 8))
        da[0, k] = h
        fd.append(((V(a + da, b) - V(a - da, b)) / (2 * h))[0])
    fdb = []
    for k in range(8):
        db = np.zeros((1, 8))
        db[0, k] = h
        fdb.append(((V(a, b + db) - V(a, b - db)) / (2 * h))[0])
    return np.allclose(ga[0], fd, atol=1e-5), np.allclose(gb[0], fdb, atol=1e-5)


# ------------------------------------------------------ alternator (delta_formula.py)


def alternator(s):
    """Left alternator T_s : x -> [s,s,x] = (ss)x - s(sx), as a matrix on the algebra of s."""
    n = len(s)
    ss = cd_mul(s, s)
    return np.column_stack([cd_mul(ss, e) - cd_mul(s, cd_mul(s, e)) for e in basis(n)])


def delta_max(s):
    """Largest eigenvalue of the symmetrised alternator — delta(s) of delta_formula.py."""
    T = alternator(s)
    w = np.linalg.eigvalsh((T + T.T) / 2)
    return w.max()


# ------------------------------------------------------- FD Hessian (landscape.py)


def fd_hessian(f, s, h=1e-4):
    """Central-difference Hessian of a scalar function f at s (landscape.py's ``hess``)."""
    m = len(s)
    H = np.zeros((m, m))
    for i in range(m):
        for j in range(m):
            ei = np.zeros(m)
            ej = np.zeros(m)
            ei[i] = h
            ej[j] = h
            H[i, j] = (
                f(s + ei + ej) - f(s + ei - ej) - f(s - ei + ej) + f(s - ei - ej)
            ) / (4 * h * h)
    return H


# ---------------------------------------------- derivations (orbit_space.py / aut_s3.py)


def D(x, y, n=8):
    """Standard inner derivation D_{x,y} = [L_x,L_y] + [L_x,R_y] + [R_x,R_y] of an alternative algebra."""
    Lx, Ly, Rx, Ry = L(x, n), L(y, n), R(x, n), R(y, n)
    return (Lx @ Ly - Ly @ Lx) + (Lx @ Ry - Ry @ Lx) + (Rx @ Ry - Ry @ Rx)
