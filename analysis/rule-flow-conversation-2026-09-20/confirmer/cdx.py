"""Independent Cayley-Dickson implementation. (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c))."""

import numpy as np


def mul_tensor(n):
    """M[i,j,k] : (e_i e_j)_k for CDAlg R n, dim 2^n."""
    if n == 0:
        return np.ones((1, 1, 1))
    Mlo = mul_tensor(n - 1)
    m = Mlo.shape[0]
    d = 2 * m
    C = conj_mat(n - 1)  # m x m
    M = np.zeros((d, d, d))
    # basis element index i < m  -> (e_i, 0);  i >= m -> (0, e_{i-m})
    for i in range(d):
        for j in range(d):
            if i < m and j < m:  # (a,0)(c,0) = (ac, 0)
                M[i, j, :m] = Mlo[i, j]
            elif i < m and j >= m:  # (a,0)(0,d) = (0, d a)
                dvec = np.zeros(m)
                dvec[j - m] = 1
                avec = np.zeros(m)
                avec[i] = 1
                M[i, j, m:] = np.einsum("p,q,pqk->k", dvec, avec, Mlo)
            elif i >= m and j < m:  # (0,b)(c,0) = (0, b conj(c))
                bvec = np.zeros(m)
                bvec[i - m] = 1
                cb = C[:, j]  # conj(e_j)
                M[i, j, m:] = np.einsum("p,q,pqk->k", bvec, cb, Mlo)
            else:  # (0,b)(0,d) = (-conj(d) b, 0)
                bvec = np.zeros(m)
                bvec[j - m] = 1  # careful: i>=m is b, j>=m is d
                db = np.zeros(m)
                db[j - m] = 1
                dbar = C @ db
                bb = np.zeros(m)
                bb[i - m] = 1
                M[i, j, :m] = -np.einsum("p,q,pqk->k", dbar, bb, Mlo)
    return M


def conj_mat(n):
    d = 2**n
    C = np.eye(d)
    if n > 0:
        C[0, 0] = 1
        for i in range(1, d):
            C[i, i] = -1
    return C


M8 = mul_tensor(3)
M16 = mul_tensor(4)


def omul(x, y):  # octonions, batched (...,8)
    return np.einsum("...i,...j,ijk->...k", x, y, M8)


def smul(x, y):  # sedenions, batched (...,16)
    return np.einsum("...i,...j,ijk->...k", x, y, M16)


def Lmat(s):  # left-mult matrix in sedenions: (L_s)[k,j] = sum_i s_i M[i,j,k]
    return np.einsum("i,ijk->kj", s, M16)


def Rmat(s):
    return np.einsum("j,ijk->ki", s, M16)


def comm(s):
    a, b = s[..., :8], s[..., 8:]
    return omul(a, b) - omul(b, a)


def V(s):
    c = comm(s)
    return (c * c).sum(-1)


def N(s):
    return (s * s).sum(-1)
