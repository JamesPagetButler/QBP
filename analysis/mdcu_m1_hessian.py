"""M1 test: Hessian zero modes of phi^2 on the Stiefel manifold V_3(R^7) (MDCU R4 FORM mechanism).

Pre-registered computation for QBP#776 rung-2 (E6) design input, written against the
MDCU round-4 "FORM" reading (qbp-compute-unit doc/spikes/mdcu-round4-results.md; planning
table inter#194 issuecomment-6431920143).  See analysis/mdcu-m1-hessian-zero-modes.md for
the pre-registered expectations A/B/C, the method and the verdict.

What is computed
----------------
For a 3-form psi on R^7 define f(F) = psi(u, v, w)^2 on the Stiefel manifold
V_3(R^7) = {F = [u v w] in R^{7x3} : F^T F = I}  (dim 15).  At a point F the tangent space is
{X : F^T X + X^T F = 0}; we build an orthonormal (Frobenius) basis of it and form the 15x15
Riemannian Hessian of f two independent ways:

  * analytic: Hess f[X, Y] = D^2 fbar[X, Y] - tr(X^T Y S),  S = sym(F^T grad fbar(F)),
    the embedded-Stiefel Hessian (Absil-Mahony-Sepulchre 2008 sec. 5.3; Edelman-Arias-Smith
    1998), where fbar is the ambient function and D^2 fbar is written out from the
    trilinearity of psi;
  * finite differences: central second differences of t -> f(qf(F + t X)) along the QR
    retraction with step h = 1e-4.  At a critical point the Hessian of f o R is independent
    of the (first-order) retraction (Absil et al. Prop. 5.5.5), so the two must agree there.

Eigenvalues are classified as zero (|lambda| < TOL = 1e-6), negative or positive.

Octonion convention
-------------------
phi_{abc} = (e_a e_b)_c for a, b, c in 1..7, with the product taken from the repo's numerical
Cayley-Dickson implementation analysis/473-dirac-probe/cdalg.py::cd_mul (the ratified F3 formula
of docs/conventions/cd-doubling.md).  The script asserts that the resulting 3-form is totally
antisymmetric and that it is +1 on exactly the seven oriented Fano triples ratified in
docs/conventions/fano-orientation.md (F4); no table is typed in by hand.

Run:  run-bounded 2G 120 python3 analysis/mdcu_m1_hessian.py        (numpy only)
"""

from __future__ import annotations

import itertools
import pathlib
import sys
import time

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "473-dirac-probe"))
from cdalg import D as inner_derivation  # noqa: E402
from cdalg import cd_mul  # noqa: E402

TOL = 1e-6  # |lambda| < TOL counts as a zero eigenvalue (pre-registered)
H_FD = 1e-4  # finite-difference step (pre-registered "h ~ 1e-4")
S_DEFORM = 0.1  # MDCU S2 sampler scale used here (pre-registered)
DIM = 7
K = 3
TANGENT_DIM = DIM * K - K * (K + 1) // 2  # 15

# Seven oriented Fano triples, 1-indexed, exactly as ratified in
# docs/conventions/fano-orientation.md ("Triple | Product rule" table):
#   e1e2=e3, e1e4=e5, e1e7=e6, e2e4=e6, e2e5=e7, e3e4=e7, e3e6=e5
FANO_F4 = [(1, 2, 3), (1, 4, 5), (1, 7, 6), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 6, 5)]


# --------------------------------------------------------------------------- 3-forms


def octonion_phi() -> np.ndarray:
    """phi_{abc} = (e_a e_b)_c on Im O, from the F3 Cayley-Dickson product (cdalg.cd_mul)."""
    E = np.eye(8)
    phi = np.zeros((DIM, DIM, DIM))
    for a in range(DIM):
        for b in range(DIM):
            phi[a, b, :] = cd_mul(E[a + 1], E[b + 1])[1:]
    assert_antisymmetric(phi, "phi")
    # F4 check: +1 on each ratified oriented triple, 42 = 7 x 3! nonzero entries total.
    for a, b, c in FANO_F4:
        assert abs(phi[a - 1, b - 1, c - 1] - 1.0) < 1e-12, (
            a,
            b,
            c,
            phi[a - 1, b - 1, c - 1],
        )
    assert np.count_nonzero(np.abs(phi) > 1e-12) == 42
    return phi


def split_cd_mul(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """Split Cayley-Dickson doubling H -> split-O: (a,b)(c,d) = (ac + conj(d) b, d a + b conj(c)).

    Same F3 shape as cd_mul with the sign of the conj(d) b term flipped (the new unit squares to
    +1).  Only used to build the split-G2 control 3-form; nothing about QBP's octonions is
    changed.
    """
    a, b, c, d = x[:4], x[4:], y[:4], y[4:]
    cj = lambda q: np.concatenate([q[:1], -q[1:]])  # noqa: E731  (quaternion conjugate)
    return np.concatenate(
        [cd_mul(a, c) + cd_mul(cj(d), b), cd_mul(d, a) + cd_mul(b, cj(c))]
    )


def split_g2_form() -> np.ndarray:
    """A 3-form on R^7 of split-G2 type: phi~_{abc} = eta_c (e_a * e_b)_c with eta = diag(1,1,1,-1,-1,-1,-1)
    (the split-octonion norm has signature (3,4) on the imaginary part)."""
    E = np.eye(8)
    eta = np.array([1, 1, 1, -1, -1, -1, -1], dtype=float)
    f = np.zeros((DIM, DIM, DIM))
    for a in range(DIM):
        for b in range(DIM):
            f[a, b, :] = eta * split_cd_mul(E[a + 1], E[b + 1])[1:]
    assert_antisymmetric(f, "split form")
    return f


def assert_antisymmetric(t: np.ndarray, name: str) -> None:
    for perm, sign in [
        ((1, 0, 2), -1),
        ((0, 2, 1), -1),
        ((2, 1, 0), -1),
        ((1, 2, 0), 1),
        ((2, 0, 1), 1),
    ]:
        assert np.allclose(
            t, sign * np.transpose(t, perm), atol=1e-12
        ), f"{name} not totally antisymmetric"


def antisymmetrise(t: np.ndarray) -> np.ndarray:
    out = np.zeros_like(t)
    for perm in itertools.permutations(range(3)):
        out += perm_sign(perm) * np.transpose(t, perm)
    return out / 6.0


def perm_sign(p) -> int:
    p = list(p)
    sign = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                sign = -sign
    return sign


def pullback(psi: np.ndarray, g: np.ndarray) -> np.ndarray:
    """(g . psi)(u, v, w) := psi(g u, g v, g w)."""
    return np.einsum("abc,ai,bj,ck->ijk", psi, g, g, g)


def frobenius_match(psi: np.ndarray, ref: np.ndarray) -> np.ndarray:
    return psi * (np.linalg.norm(ref) / np.linalg.norm(psi))


def s2_form(
    rng: np.random.Generator, phi: np.ndarray, s: float = S_DEFORM
) -> tuple[np.ndarray, dict]:
    """MDCU S2 sampler (qbp-compute-unit emulator/mdcu/r3forms.go::SampleS2): psi = g . phi,
    g = exp(s S), S = sym(Gaussian 7x7) made traceless; then Frobenius-matched to |phi|.
    """
    G = rng.standard_normal((DIM, DIM))
    S = 0.5 * (G + G.T)
    S -= np.trace(S) / DIM * np.eye(DIM)
    w, V = np.linalg.eigh(S)
    g = V @ np.diag(np.exp(s * w)) @ V.T
    psi = frobenius_match(pullback(phi, g), phi)
    cond = np.exp(s * (w.max() - w.min())) ** 2  # condition number of g g^T
    return psi, {
        "s": s,
        "cond_gg": cond,
        "dist": np.linalg.norm(psi - phi) / np.sqrt(42),
    }


def random_form(rng: np.random.Generator, phi: np.ndarray) -> np.ndarray:
    return frobenius_match(antisymmetrise(rng.standard_normal((DIM, DIM, DIM))), phi)


# --------------------------------------------------------------------------- Hitchin signature


def hitchin_B(psi: np.ndarray) -> np.ndarray:
    """B_psi(u, v) e^{1..7} = (iota_u psi) ^ (iota_v psi) ^ psi, as the symmetric 7x7 matrix
    B_ij = sum_{perms p of 0..6} sgn(p) psi_{i p0 p1} psi_{j p2 p3} psi_{p4 p5 p6}
    (overall normalisation irrelevant for the signature).  Definite <=> G2-type (Hitchin 2000);
    signature (3,4)/(4,3) <=> split type."""
    B = np.zeros((DIM, DIM))
    for p in itertools.permutations(range(DIM)):
        s = perm_sign(p)
        B += (
            s * np.outer(psi[:, p[0], p[1]], psi[:, p[2], p[3]]) * psi[p[4], p[5], p[6]]
        )
    return B


def signature(B: np.ndarray, tol: float = 1e-9) -> tuple[int, int, int]:
    w = np.linalg.eigvalsh(B)
    scale = max(1.0, np.abs(w).max())
    return (
        int((w > tol * scale).sum()),
        int((w < -tol * scale).sum()),
        int((np.abs(w) <= tol * scale).sum()),
    )


def stability_label(B: np.ndarray) -> str:
    p, n, z = signature(B)
    if z:
        return f"NOT STABLE ({p},{n},{z} zero)"
    if p == DIM or n == DIM:
        return f"definite ({p},{n})"
    return f"split ({p},{n})"


# --------------------------------------------------------------------------- G2 sampling


def g2_basis(phi: np.ndarray) -> np.ndarray:
    """Basis of g2 = Der(O) restricted to Im O, from the standard inner derivations
    D_{e_a, e_b} (cdalg.D); asserts dim 14 and that each element annihilates phi."""
    E = np.eye(8)
    mats = []
    for a in range(1, 8):
        for b in range(a + 1, 8):
            Dab = inner_derivation(E[a], E[b])
            assert np.allclose(Dab[0, :], 0) and np.allclose(
                Dab[:, 0], 0
            )  # kills / avoids the real unit
            mats.append(Dab[1:, 1:])
    M = np.array([m.ravel() for m in mats])
    U, sv, Vt = np.linalg.svd(M)
    rank = int((sv > 1e-9 * sv[0]).sum())
    assert rank == 14, rank
    basis = Vt[:rank].reshape(rank, DIM, DIM)
    for A in basis:
        assert np.allclose(A, -A.T, atol=1e-12)
        lie = (
            np.einsum("abc,ai->ibc", phi, A)
            + np.einsum("abc,bj->ajc", phi, A)
            + np.einsum("abc,ck->abk", phi, A)
        )
        assert np.allclose(lie, 0, atol=1e-10), "derivation does not annihilate phi"
    return basis


def expm_skew(A: np.ndarray) -> np.ndarray:
    w, V = np.linalg.eig(A)
    return (V @ np.diag(np.exp(w)) @ np.linalg.inv(V)).real


def random_g2(
    rng: np.random.Generator, basis: np.ndarray, phi: np.ndarray
) -> np.ndarray:
    A = np.einsum("i,ijk->jk", rng.standard_normal(len(basis)), basis)
    g = expm_skew(A)
    assert np.allclose(g.T @ g, np.eye(DIM), atol=1e-10)
    assert np.allclose(pullback(phi, g), phi, atol=1e-9), "sampled element is not in G2"
    return g


def random_so3(rng: np.random.Generator) -> np.ndarray:
    Q, R = np.linalg.qr(rng.standard_normal((K, K)))
    Q = Q * np.sign(np.diag(R))
    if np.linalg.det(Q) < 0:
        Q[:, 0] *= -1
    return Q


# --------------------------------------------------------------------------- Stiefel geometry


def qf(M: np.ndarray) -> np.ndarray:
    """QR retraction with the sign convention diag(R) > 0 (makes qf smooth near the identity)."""
    Q, R = np.linalg.qr(M)
    return Q * np.sign(np.diag(R))


def form(psi: np.ndarray, u, v, w) -> float:
    return float(np.einsum("abc,a,b,c", psi, u, v, w))


def f_val(psi: np.ndarray, F: np.ndarray) -> float:
    return form(psi, F[:, 0], F[:, 1], F[:, 2]) ** 2


def dT(psi, F, X) -> float:
    u, v, w = F.T
    return (
        form(psi, X[:, 0], v, w) + form(psi, u, X[:, 1], w) + form(psi, u, v, X[:, 2])
    )


def d2T(psi, F, X, Y) -> float:
    u, v, w = F.T
    return (
        form(psi, X[:, 0], Y[:, 1], w)
        + form(psi, Y[:, 0], X[:, 1], w)
        + form(psi, X[:, 0], v, Y[:, 2])
        + form(psi, Y[:, 0], v, X[:, 2])
        + form(psi, u, X[:, 1], Y[:, 2])
        + form(psi, u, Y[:, 1], X[:, 2])
    )


def euclid_grad(psi, F) -> np.ndarray:
    """grad of fbar(F) = psi(u,v,w)^2 in R^{7x3}: column i = 2 T psi(..., slot i, ...)."""
    u, v, w = F.T
    T = form(psi, u, v, w)
    g = np.column_stack(
        [
            np.einsum("abc,b,c->a", psi, v, w),
            np.einsum("abc,a,c->b", psi, u, w),
            np.einsum("abc,a,b->c", psi, u, v),
        ]
    )
    return 2.0 * T * g


def riem_grad(psi, F) -> np.ndarray:
    G = euclid_grad(psi, F)
    S = F.T @ G
    return G - F @ (0.5 * (S + S.T))


def tangent_basis(F: np.ndarray) -> list[np.ndarray]:
    """Orthonormal basis of T_F V_3(R^7) = {F A + F_perp B : A skew 3x3, B 4x3}, dim 15."""
    U = np.linalg.svd(F, full_matrices=True)[0]
    Fperp = U[:, K:]
    basis = []
    for i in range(K):
        for j in range(i + 1, K):
            A = np.zeros((K, K))
            A[i, j], A[j, i] = 1.0, -1.0
            basis.append(F @ A / np.sqrt(2.0))
    for k in range(DIM - K):
        for l in range(K):
            B = np.zeros((DIM - K, K))
            B[k, l] = 1.0
            basis.append(Fperp @ B)
    assert len(basis) == TANGENT_DIM
    Gram = np.array([[np.sum(X * Y) for Y in basis] for X in basis])
    assert np.allclose(Gram, np.eye(TANGENT_DIM), atol=1e-12)
    for X in basis:  # tangency: F^T X skew
        assert np.allclose(F.T @ X + X.T @ F, 0, atol=1e-12)
    return basis


def hessian_analytic(psi, F, basis) -> np.ndarray:
    u, v, w = F.T
    T = form(psi, u, v, w)
    G = euclid_grad(psi, F)
    S = 0.5 * (F.T @ G + G.T @ F)
    d = [dT(psi, F, X) for X in basis]
    n = len(basis)
    H = np.zeros((n, n))
    for a in range(n):
        for b in range(a, n):
            H[a, b] = (
                2.0 * d[a] * d[b]
                + 2.0 * T * d2T(psi, F, basis[a], basis[b])
                - np.trace(basis[a].T @ basis[b] @ S)
            )
            H[b, a] = H[a, b]
    return H


def hessian_fd(psi, F, basis, h: float = H_FD) -> np.ndarray:
    n = len(basis)
    f0 = f_val(psi, F)
    H = np.zeros((n, n))
    for a in range(n):
        Xa = basis[a]
        H[a, a] = (
            f_val(psi, qf(F + h * Xa)) - 2.0 * f0 + f_val(psi, qf(F - h * Xa))
        ) / h**2
        for b in range(a + 1, n):
            Xb = basis[b]
            H[a, b] = (
                f_val(psi, qf(F + h * (Xa + Xb)))
                - f_val(psi, qf(F + h * (Xa - Xb)))
                - f_val(psi, qf(F + h * (-Xa + Xb)))
                + f_val(psi, qf(F - h * (Xa + Xb)))
            ) / (4.0 * h**2)
            H[b, a] = H[a, b]
    return H


H_FD4 = 1e-2  # step for the 4th-order stencil (truncation ~h^4, roundoff ~eps f/h^2 ~ 1e-11)


def hessian_fd4(psi, F, basis, h: float = H_FD4) -> np.ndarray:
    """Second FD check: 4th-order 5-point stencil for Q(X) = d^2/dt^2 f(qf(F + tX)) at t = 0,
    and polarisation H_ab = (Q(X_a + X_b) - Q(X_a) - Q(X_b)) / 2.  Used because the 2nd-order
    stencil at the pre-registered h = 1e-4 has a roundoff floor 4 eps f / h^2 ~ 1e-6 ~ TOL.
    """

    def Q(X):
        fx = lambda t: f_val(psi, qf(F + t * X))  # noqa: E731
        return (-fx(2 * h) + 16 * fx(h) - 30 * fx(0.0) + 16 * fx(-h) - fx(-2 * h)) / (
            12 * h**2
        )

    n = len(basis)
    q = [Q(X) for X in basis]
    H = np.zeros((n, n))
    for a in range(n):
        H[a, a] = q[a]
        for b in range(a + 1, n):
            H[a, b] = H[b, a] = 0.5 * (Q(basis[a] + basis[b]) - q[a] - q[b])
    return H


def classify(H: np.ndarray, tol: float = TOL) -> dict:
    w = np.linalg.eigvalsh(0.5 * (H + H.T))
    nz = w[np.abs(w) >= tol]
    return {
        "zero": int((np.abs(w) < tol).sum()),
        "neg": int((w <= -tol).sum()),
        "pos": int((w >= tol).sum()),
        "min_abs_nonzero": float(np.abs(nz).min()) if len(nz) else float("nan"),
        "max_abs_zero": (
            float(np.abs(w[np.abs(w) < tol]).max()) if (np.abs(w) < tol).any() else 0.0
        ),
        "eigs": w,
    }


# --------------------------------------------------------------------------- maximiser search


def ascend(psi, F, iters: int = 3000, gtol: float = 1e-9) -> np.ndarray:
    alpha = 0.5
    f = f_val(psi, F)
    for _ in range(iters):
        G = riem_grad(psi, F)
        gn = np.linalg.norm(G)
        if gn < gtol:
            break
        while True:
            Fn = qf(F + alpha * G)
            fn = f_val(psi, Fn)
            if fn >= f + 1e-4 * alpha * gn**2:
                F, f = Fn, fn
                alpha = min(alpha * 1.5, 10.0)
                break
            alpha *= 0.5
            if alpha < 1e-12:
                return F
    return F


def newton_polish(psi, F, iters: int = 30, gtol: float = 1e-13) -> np.ndarray:
    for _ in range(iters):
        G = riem_grad(psi, F)
        if np.linalg.norm(G) < gtol:
            break
        basis = tangent_basis(F)
        H = hessian_analytic(psi, F, basis)
        g = np.array([np.sum(G * X) for X in basis])
        x = -np.linalg.pinv(H, rcond=1e-8) @ g
        F = qf(F + sum(xi * X for xi, X in zip(x, basis)))
    return F


def multistart_max(psi, rng, nstart: int = 20) -> tuple[np.ndarray, int]:
    """Best of nstart gradient ascents + Newton polish; also how many starts reached the best value."""
    results = []
    for _ in range(nstart):
        F = newton_polish(psi, ascend(psi, qf(rng.standard_normal((DIM, K)))))
        results.append((f_val(psi, F), F))
    best_val, best_F = max(results, key=lambda r: r[0])
    n_at_best = sum(1 for v, _ in results if abs(v - best_val) < 1e-8)
    return best_F, n_at_best


# --------------------------------------------------------------------------- driver


def analyse(label, psi, F, extra=""):
    basis = tangent_basis(F)
    Ha = hessian_analytic(psi, F, basis)
    Hf = hessian_fd(psi, F, basis)
    Hf4 = hessian_fd4(psi, F, basis)
    ca, cf, cf4 = classify(Ha), classify(Hf), classify(Hf4)
    agree = np.abs(Ha - Hf).max()
    agree4 = np.abs(Ha - Hf4).max()
    row = {
        "label": label,
        "f": f_val(psi, F),
        "T": form(psi, *F.T),
        "rgrad": np.linalg.norm(riem_grad(psi, F)),
        "an": ca,
        "fd": cf,
        "fd4": cf4,
        "agree": agree,
        "agree4": agree4,
        "extra": extra,
    }
    return row


def fmt_row(r) -> str:
    a, f, f4 = r["an"], r["fd"], r["fd4"]
    return (
        f"| {r['label']} | {r['f']:.6f} | {r['rgrad']:.1e} | {a['zero']}/{a['neg']}/{a['pos']} | "
        f"{f['zero']}/{f['neg']}/{f['pos']} | {f4['zero']}/{f4['neg']}/{f4['pos']} | "
        f"{a['min_abs_nonzero']:.3e} | {a['max_abs_zero']:.1e} | {r['agree']:.1e} | {r['agree4']:.1e} | {r['extra']} |"
    )


HEADER = (
    "| form / point | f = psi^2 | \\|grad_R f\\| | analytic #0/#neg/#pos | FD2 h=1e-4 #0/#neg/#pos | "
    "FD4 h=1e-2 #0/#neg/#pos | min \\|nonzero\\| (an.) | max \\|zero-class\\| (an.) | "
    "max \\|H_fd2 - H_an\\| | max \\|H_fd4 - H_an\\| | notes |\n"
    "|---|---|---|---|---|---|---|---|---|---|---|"
)


def main() -> int:
    t0 = time.time()
    phi = octonion_phi()
    print(
        "phi: F3/F4 convention check PASSED (totally antisymmetric; +1 on the 7 ratified Fano triples; 42 nonzeros)"
    )
    print(f"Hitchin B_phi: {stability_label(hitchin_B(phi))}")
    g2 = g2_basis(phi)
    print(
        f"g2 = Der(O)|Im O: dim {len(g2)} (asserted 14), every element annihilates phi"
    )
    print(
        f"TOL (zero class) = {TOL:g};  FD step h = {H_FD:g};  tangent dim = {TANGENT_DIM}\n"
    )

    rows_A, rows_B, rows_C, rows_split = [], [], [], []

    # ---- Expectation A: associative frames of phi
    rng = np.random.default_rng(20261027)
    for i in range(5):
        a, b, c = FANO_F4[i]
        F0 = np.eye(DIM)[:, [a - 1, b - 1, c - 1]]
        F = random_g2(rng, g2, phi) @ F0 @ random_so3(rng)
        rows_A.append(
            analyse(
                f"phi, assoc. frame #{i+1} (g.Fano({a}{b}{c}).R)",
                phi,
                F,
                f"T={form(phi, *F.T):+.6f}",
            )
        )
    # also the bare Fano frame, no rotation at all
    F0 = np.eye(DIM)[:, [0, 1, 2]]
    rows_A.append(
        analyse("phi, bare Fano(123) frame", phi, F0, f"T={form(phi, *F0.T):+.6f}")
    )

    # ---- Expectation B: generic definite psi = g.phi (S2 sampler, s = 0.1)
    for seed in range(5):
        rng_s = np.random.default_rng(1000 + seed)
        psi, info = s2_form(rng_s, phi)
        lab = stability_label(hitchin_B(psi))
        F, n_best = multistart_max(psi, rng_s)
        rows_B.append(
            analyse(
                f"psi_S2 seed {1000+seed}, Euclid.-max.",
                psi,
                F,
                f"B_psi {lab}; cond(gg^T)={info['cond_gg']:.2f}; d={info['dist']:.3f}; {n_best}/20 starts at max",
            )
        )

    # ---- Expectation C (control): random 3-forms, and the split-G2 form (no expectation)
    for seed in range(3):
        rng_r = np.random.default_rng(2000 + seed)
        psi = random_form(rng_r, phi)
        lab = stability_label(hitchin_B(psi))
        F, n_best = multistart_max(psi, rng_r)
        rows_C.append(
            analyse(
                f"random 3-form seed {2000+seed}, Euclid.-max.",
                psi,
                F,
                f"B_psi {lab}; {n_best}/20 starts at max",
            )
        )

    split = split_g2_form()
    lab = stability_label(hitchin_B(split))
    rng_sp = np.random.default_rng(3000)
    F, n_best = multistart_max(split, rng_sp)
    rows_split.append(
        analyse(
            "split-G2 form, Euclid.-max. (multistart)",
            split,
            F,
            f"B {lab}; {n_best}/20 starts at max",
        )
    )
    F0 = np.eye(DIM)[:, [0, 1, 2]]
    rows_split.append(
        analyse(
            "split-G2 form, bare (123) frame",
            split,
            F0,
            f"B {lab}; T={form(split, *F0.T):+.6f}",
        )
    )

    # ---- report
    def section(title, rows):
        print(f"### {title}\n{HEADER}")
        for r in rows:
            print(fmt_row(r))
        print()

    section(
        "Expectation A — phi at associative frames (expect 11 zero / 4 negative / 0 positive)",
        rows_A,
    )
    section(
        "Expectation B — generic definite psi = g.phi at its Euclidean maximiser (expect 3 / 12 / 0)",
        rows_B,
    )
    section("Expectation C — random 3-form controls (expect 3 / 12 / 0)", rows_C)
    section("Split-G2 form (no expectation; report only)", rows_split)

    def verdict(rows, z, n, p, name):
        ok = all(
            r["an"]["zero"] == z and r["an"]["neg"] == n and r["an"]["pos"] == p
            for r in rows
        )
        ok_fd = all(
            r["fd"]["zero"] == z and r["fd"]["neg"] == n and r["fd"]["pos"] == p
            for r in rows
        )
        ok_fd4 = all(
            r["fd4"]["zero"] == z and r["fd4"]["neg"] == n and r["fd4"]["pos"] == p
            for r in rows
        )
        print(
            f"{name}: analytic {'PASS' if ok else 'FAIL'}; FD2 (h=1e-4, pre-reg) {'PASS' if ok_fd else 'FAIL'}; "
            f"FD4 (h=1e-2) {'PASS' if ok_fd4 else 'FAIL'}  (expected {z}/{n}/{p})"
        )
        return ok and ok_fd4

    print("### Verdicts")
    vA = verdict(rows_A, 11, 4, 0, "Expectation A")
    vB = verdict(rows_B, 3, 12, 0, "Expectation B")
    vC = verdict(rows_C, 3, 12, 0, "Expectation C (random control)")
    allrows = rows_A + rows_B + rows_C + rows_split
    print(
        f"FD2 vs analytic: worst max|H_fd2 - H_an| over all points = {max(r['agree'] for r in allrows):.2e}"
    )
    print(
        f"FD4 vs analytic: worst max|H_fd4 - H_an| over all points = {max(r['agree4'] for r in allrows):.2e}"
    )
    np.set_printoptions(precision=4, suppress=True, linewidth=150)
    print("\n### Spectra (analytic Hessian, sorted)")
    for r in [rows_A[-1], rows_A[0], rows_B[0], rows_C[0]] + rows_split:
        print(f"{r['label']}: {r['an']['eigs']}")
    print(f"\nruntime {time.time()-t0:.1f} s")
    return 0 if (vA and vB and vC) else 1


if __name__ == "__main__":
    sys.exit(main())
