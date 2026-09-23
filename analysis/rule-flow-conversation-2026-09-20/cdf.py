import numpy as np


def _mul_rec(x, y):
    n = len(x)
    if n == 1:
        return x * y
    h = n // 2
    a, b = x[:h], x[h:]
    c, d = y[:h], y[h:]
    return np.concatenate(
        [_mul_rec(a, c) - _mul_rec(_conj(d), b), _mul_rec(d, a) + _mul_rec(b, _conj(c))]
    )


def _conj(x):
    n = len(x)
    if n == 1:
        return x.copy()
    h = n // 2
    return np.concatenate([_conj(x[:h]), -x[h:]])


D = 16
S = np.zeros((D, D))  # sign table: e_i e_j = S[i,j] e_{i^j}
IDX = np.zeros((D, D), dtype=int)
for i in range(D):
    for j in range(D):
        p = _mul_rec(np.eye(D)[i], np.eye(D)[j])
        k = int(np.argmax(np.abs(p)))
        S[i, j] = p[k]
        IDX[i, j] = k
        assert abs(abs(p[k]) - 1) < 1e-12 and np.count_nonzero(np.abs(p) > 1e-12) == 1
        assert k == (i ^ j)
FLAT = IDX.ravel()


def mul(x, y):
    prod = (np.outer(x, y) * S).ravel()
    return np.bincount(FLAT, weights=prod, minlength=D)


def conj(x):
    c = -x.copy()
    c[0] = x[0]
    return c


def N(x):
    return float(x @ x)


def comm(s):
    a, b = s[:8], s[8:]
    return mul8(a, b) - mul8(b, a)


# octonion sub-table
S8 = S[:8, :8]
IDX8 = IDX[:8, :8]
FLAT8 = IDX8.ravel()


def mul8(x, y):
    return np.bincount(FLAT8, weights=(np.outer(x, y) * S8).ravel(), minlength=8)


def conj8(x):
    c = -x.copy()
    c[0] = x[0]
    return c


def V(s):
    return float(comm(s) @ comm(s))


def gradV(s):
    a, b = s[:8], s[8:]
    C = comm(s)
    cb, ca = conj8(b), conj8(a)
    lo = 2.0 * (mul8(C, cb) - mul8(cb, C))
    hi = 2.0 * (mul8(ca, C) - mul8(C, ca))
    return np.concatenate([lo, hi])


def ruleField(s):
    g = gradV(s)
    one = np.zeros(16)
    one[0] = 1.0
    return -(g - (g @ s) * s - g[0] * one)


def Lmat(s):
    return (
        np.einsum("i,ij->ij", np.ones(D), np.zeros((D, D)))
        + np.array([mul(s, np.eye(D)[i]) for i in range(D)]).T
    )


def Rmat(s):
    return np.array([mul(np.eye(D)[i], s) for i in range(D)]).T
