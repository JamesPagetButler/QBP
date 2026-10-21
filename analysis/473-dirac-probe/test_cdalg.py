"""Unit checks for cdalg.py (#632) — the Cayley–Dickson helpers shared by the #473 probe scripts.

Run from anywhere:  python3 -m pytest analysis/473-dirac-probe/test_cdalg.py -q

The checks pin the helpers to known algebra facts (Schafer CD convention, as in
proofs/QBP/Foundations/CDAlg.lean) and to the invariants the probe scripts' docstrings rely on.
Random samples are seeded, so every test is deterministic.
"""

from __future__ import annotations

import itertools

import numpy as np
import pytest

from cdalg import (
    D,
    L,
    M8,
    R,
    V,
    alternator,
    basis,
    cd_mul,
    conj,
    delta_max,
    fd_hessian,
    grad,
    grad_fd_check,
    omul,
    spec,
)

RNG = np.random.default_rng(632)


def e(i: int, n: int) -> np.ndarray:
    return np.eye(n)[i]


def N(x: np.ndarray) -> float:
    return float(x @ x)


# ------------------------------------------------------------------ multiplication tables


def test_complex_table():
    i = e(1, 2)
    assert np.array_equal(cd_mul(i, i), -e(0, 2))
    assert np.array_equal(cd_mul(e(0, 2), i), i)


def test_quaternion_table():
    one, i, j, k = basis(4)
    assert np.array_equal(cd_mul(i, j), k)
    assert np.array_equal(cd_mul(j, k), i)
    assert np.array_equal(cd_mul(k, i), j)
    assert np.array_equal(cd_mul(j, i), -k)
    for u in (i, j, k):
        assert np.array_equal(cd_mul(u, u), -one)
    # Schafer convention check: with ℓ = e2 = j, (a + bℓ)(c + dℓ) = (ac - d̄b) + (da + bc̄)ℓ
    # so e1·e2 = (0 + 0ℓ)... concretely i·ℓ = ℓ·(conj i) ⇒ i j = -(j i) = k, consistent above.
    assert np.array_equal(cd_mul(i, j), -cd_mul(j, i))


@pytest.mark.parametrize("n", [4, 8, 16])
def test_units_square_to_minus_one_and_anticommute(n):
    E = basis(n)
    for a in range(1, n):
        assert np.array_equal(cd_mul(E[a], E[a]), -E[0])
        for b in range(a + 1, n):
            assert np.array_equal(cd_mul(E[a], E[b]), -cd_mul(E[b], E[a]))


@pytest.mark.parametrize("n", [2, 4, 8, 16])
def test_identity_and_conjugation(n):
    x = RNG.normal(size=n)
    assert np.allclose(cd_mul(e(0, n), x), x)
    assert np.allclose(cd_mul(x, e(0, n)), x)
    # x x̄ = (N(x), 0, …, 0) at every doubling (positive-definiteness survives)
    xxbar = cd_mul(x, conj(x))
    assert np.allclose(xxbar, e(0, n) * N(x))
    assert np.allclose(conj(cd_mul(x, x)), cd_mul(conj(x), conj(x)))
    assert np.array_equal(conj(conj(x)), x)


def test_octonion_table_against_structure_tensor():
    """M8[i, j] must be the (e_i e_j) row of cd_mul — the vectorised product is the scalar one."""
    E = basis(8)
    for i, j in itertools.product(range(8), repeat=2):
        assert np.array_equal(M8[i, j], cd_mul(E[i], E[j]))
    # a concrete entry in the Schafer convention: e1 e2 = e3, e1 e4 = e5, e2 e4 = e6, e3 e4 = e7
    assert np.array_equal(cd_mul(E[1], E[2]), E[3])
    assert np.array_equal(cd_mul(E[1], E[4]), E[5])
    assert np.array_equal(cd_mul(E[2], E[4]), E[6])
    assert np.array_equal(cd_mul(E[3], E[4]), E[7])


# ------------------------------------------------------------------ norm multiplicativity


@pytest.mark.parametrize("n", [2, 4, 8])
def test_norm_multiplicative_up_to_octonions(n):
    for _ in range(50):
        x, y = RNG.normal(size=n), RNG.normal(size=n)
        assert np.isclose(N(cd_mul(x, y)), N(x) * N(y), rtol=1e-12)


def test_norm_not_multiplicative_for_sedenions():
    """Explicit zero divisor (e1 + e10)(e4 - e15) = 0 and a random witness with N(xy) ≠ N(x)N(y)."""
    E = basis(16)
    x, y = E[1] + E[10], E[4] - E[15]
    assert np.allclose(cd_mul(x, y), 0)
    assert N(x) * N(y) == 4.0
    ratios = []
    for _ in range(50):
        a, b = RNG.normal(size=16), RNG.normal(size=16)
        ratios.append(N(cd_mul(a, b)) / (N(a) * N(b)))
    assert not np.allclose(ratios, 1.0)


# ------------------------------------------------------------------ (non-)associativity


def test_quaternions_associative_octonions_alternative_not_associative():
    for _ in range(20):
        x, y, z = (RNG.normal(size=4) for _ in range(3))
        assert np.allclose(cd_mul(cd_mul(x, y), z), cd_mul(x, cd_mul(y, z)))
    E = basis(8)
    # alternative: [x, x, y] = 0 for all x, y
    for _ in range(20):
        x, y = RNG.normal(size=8), RNG.normal(size=8)
        assert np.allclose(cd_mul(cd_mul(x, x), y), cd_mul(x, cd_mul(x, y)))
    # but not associative: the classic witness (e1 e2) e4 = e3 e4 = e7 while e1 (e2 e4) = e1 e6 = -e7
    assert np.array_equal(cd_mul(cd_mul(E[1], E[2]), E[4]), E[7])
    assert np.array_equal(cd_mul(E[1], cd_mul(E[2], E[4])), -E[7])


def test_sedenions_not_alternative():
    """[s, s, x] ≠ 0 for a generic imaginary sedenion s — the probe's whole object of study."""
    s = RNG.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    x = RNG.normal(size=16)
    assert not np.allclose(cd_mul(cd_mul(s, s), x), cd_mul(s, cd_mul(s, x)))


# ------------------------------------------------------------------ L, R, spec


@pytest.mark.parametrize("n", [4, 8, 16])
def test_L_R_are_the_multiplication_matrices(n):
    s, x = RNG.normal(size=n), RNG.normal(size=n)
    assert np.allclose(L(s, n) @ x, cd_mul(s, x))
    assert np.allclose(R(s, n) @ x, cd_mul(x, s))


@pytest.mark.parametrize("n", [4, 8, 16])
def test_sum_of_units_squares_to_minus_dim_minus_one(n):
    """README §1: D² = -L_s² = (n-1)·I for s = Σ_{a≥1} e_a, at every level including 𝕊."""
    E = basis(n)
    s = sum(E[1:])
    Ls = L(s, n)
    assert np.allclose(-(Ls @ Ls), (n - 1) * np.eye(n))
    assert spec(-(Ls @ Ls)) == [(complex(n - 1), n)]


def test_spec_counts_multiplicities():
    assert spec(np.diag([1.0, 1.0, 2.0])) == [(1 + 0j, 2), (2 + 0j, 1)]


def test_zero_divisor_direction_has_4_8_4_spectrum():
    """README §2: at s = (e1 + e10)/√2, spec(-L_s²) = {0 ×4, 1 ×8, 2 ×4}; in an 𝕆 subalgebra, L_s² = -1."""
    E = basis(16)
    s = (E[1] + E[10]) / np.sqrt(2)
    w = np.sort(np.linalg.eigvalsh(-(L(s, 16) @ L(s, 16))))
    assert np.allclose(w, [0] * 4 + [1] * 8 + [2] * 4)
    t = RNG.normal(size=16)
    t[0] = 0
    t[8:] = 0
    t /= np.linalg.norm(t)
    assert np.allclose(L(t, 16) @ L(t, 16), -np.eye(16))


# ------------------------------------------------------------------ alternator / delta


def test_alternator_matches_minus_Ls_squared_minus_identity_and_delta_formula():
    """README §6: -L_s² = |s|²·I + T_s, spec T_s = {+δ ×4, 0 ×8, -δ ×4}, δ = ‖[a, b]‖, T_s³ = δ²·T_s."""
    for _ in range(5):
        s = RNG.normal(size=16)
        s[0] = 0
        s /= np.linalg.norm(s)
        T = alternator(s)
        assert np.allclose(T, T.T)
        assert np.allclose(-(L(s, 16) @ L(s, 16)), np.eye(16) + T)
        a, b = s[:8], s[8:]
        delta = np.linalg.norm(cd_mul(a, b) - cd_mul(b, a))
        assert np.isclose(delta_max(s), delta)
        w = np.sort(np.linalg.eigvalsh(T))
        assert np.allclose(w, [-delta] * 4 + [0] * 8 + [delta] * 4)
        assert np.allclose(T @ T @ T, delta**2 * T)


def test_alternator_vanishes_in_octonion_subalgebra():
    s = RNG.normal(size=16)
    s[8:] = 0
    assert np.allclose(alternator(s), 0)


# ------------------------------------------------------------------ omul / V / grad (flow_big)


def test_omul_rowwise_equals_cd_mul():
    X, Y = RNG.normal(size=(6, 8)), RNG.normal(size=(6, 8))
    P = omul(X, Y)
    for k in range(6):
        assert np.allclose(P[k], cd_mul(X[k], Y[k]))


def test_V_is_commutator_norm_squared_and_descends_to_gram_determinant():
    """orbit_space.py (3): V = ‖[a,b]‖² = 4(|a|²|Im b|² - ⟨a, Im b⟩²) for imaginary a."""
    A = RNG.normal(size=(8, 8))
    A[:, 0] = 0
    B = RNG.normal(size=(8, 8))
    v = V(A, B)
    for k in range(8):
        c = cd_mul(A[k], B[k]) - cd_mul(B[k], A[k])
        assert np.isclose(v[k], c @ c)
        imb = B[k].copy()
        imb[0] = 0
        assert np.isclose(v[k], 4 * (A[k] @ A[k] * (imb @ imb) - (A[k] @ imb) ** 2))
    assert np.allclose(V(A, A), 0)  # [a, a] = 0


def test_grad_matches_finite_differences():
    ok_a, ok_b = grad_fd_check(np.random.default_rng(1))
    assert ok_a and ok_b
    # and directly, at a fresh point, both slots
    a = RNG.normal(size=(1, 8))
    a[:, 0] = 0
    b = RNG.normal(size=(1, 8))
    ga, gb = grad(a, b)
    assert ga[0, 0] == 0.0  # projected onto Im O
    h = 1e-6
    for k in range(1, 8):
        da = np.zeros((1, 8))
        da[0, k] = h
        assert np.isclose(
            ga[0, k], (V(a + da, b) - V(a - da, b))[0] / (2 * h), atol=1e-5
        )
    for k in range(8):
        db = np.zeros((1, 8))
        db[0, k] = h
        assert np.isclose(
            gb[0, k], (V(a, b + db) - V(a, b - db))[0] / (2 * h), atol=1e-5
        )


def test_grad_fd_check_draw_order_is_two_normals():
    """flow_big.py's sampling depends on the FD check consuming exactly a then b from the rng."""
    r1, r2 = np.random.default_rng(1), np.random.default_rng(1)
    grad_fd_check(r1)
    r2.normal(size=(1, 8))
    r2.normal(size=(1, 8))
    assert np.array_equal(r1.normal(size=5), r2.normal(size=5))


# ------------------------------------------------------------------ fd_hessian / D


def test_fd_hessian_of_quadratic_form():
    A = RNG.normal(size=(5, 5))
    A = A + A.T
    f = lambda x: 0.5 * x @ A @ x  # noqa: E731
    assert np.allclose(fd_hessian(f, RNG.normal(size=5)), A, atol=1e-6)


def test_derivations_span_g2_and_satisfy_leibniz():
    """orbit_space.py (1): the 21 D_{e_i, e_j} span a 14-dim space and are derivations of 𝕆."""
    E = basis(8)
    ders = [D(E[i], E[j]) for i in range(1, 8) for j in range(i + 1, 8)]
    assert np.linalg.matrix_rank(np.array([d.ravel() for d in ders]), 1e-9) == 14
    x, y = RNG.normal(size=8), RNG.normal(size=8)
    for d in ders:
        assert np.allclose(d @ cd_mul(x, y), cd_mul(d @ x, y) + cd_mul(x, d @ y))
        assert np.allclose(d, -d.T)  # skew: in so(7)
        assert np.allclose(d @ E[0], 0)  # kills the identity
