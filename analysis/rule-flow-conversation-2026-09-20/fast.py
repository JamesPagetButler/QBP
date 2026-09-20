import numpy as np
from cd import mul, conj


def tensor(n):
    I = np.eye(n)
    M = np.zeros((n, n, n))
    for i in range(n):
        for j in range(n):
            M[i, j] = mul(I[i], I[j])
    return M


M8 = tensor(8)
M16 = tensor(16)


def o(x, y):
    return np.einsum("...i,...j,ijk->...k", x, y, M8)


def V(s):
    a, b = s[..., :8], s[..., 8:]
    c = o(a, b) - o(b, a)
    return (c * c).sum(-1)


def gradV(s):
    a, b = s[..., :8], s[..., 8:]
    c = o(a, b) - o(b, a)
    # dV/da_k = 2<c, e_k b - b e_k> = 2 sum_j c_m (M[k,j,m] b_j - M[j,k,m] b_j)
    ga = 2 * np.einsum("...m,kjm,...j->...k", c, M8, b) - 2 * np.einsum(
        "...m,jkm,...j->...k", c, M8, b
    )
    gb = 2 * np.einsum("...m,jkm,...j->...k", c, M8, a) - 2 * np.einsum(
        "...m,kjm,...j->...k", c, M8, a
    )
    return np.concatenate([ga, gb], axis=-1)


def F(s):
    g = gradV(s)
    t = -(g - (g * s).sum(-1, keepdims=True) * s)
    t[..., 0] = 0.0
    return t


def Lmat(s):
    return np.einsum("i,ijk->kj", s, M16)  # (s*y)_k = sum_ij s_i y_j M[i,j,k]
