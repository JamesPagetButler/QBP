import numpy as np


# Cayley-Dickson: (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c))
def conj(x):
    y = x.copy()
    y[..., 1:] *= -1
    return y


def mul(x, y):
    n = x.shape[-1]
    if n == 1:
        return x * y
    h = n // 2
    a, b = x[..., :h], x[..., h:]
    c, d = y[..., :h], y[..., h:]
    return np.concatenate(
        [mul(a, c) - mul(conj(d), b), mul(d, a) + mul(b, conj(c))], axis=-1
    )


def V(s):  # s: (...,16)
    a, b = s[..., :8], s[..., 8:]
    c = mul(a, b) - mul(b, a)
    return (c * c).sum(-1)


def gradV_num(s, h=1e-6):
    g = np.zeros_like(s)
    for k in range(16):
        e = np.zeros(16)
        e[k] = h
        g[..., k] = (V(s + e) - V(s - e)) / (2 * h)
    return g


def proj(s, g):  # tangent to {coord0=0, |s|=1}
    t = g.copy()
    t[..., 0] = 0.0
    t = t - (t * s).sum(-1, keepdims=True) * s
    return t


def Lmat(s):  # left-multiplication matrix, 16x16
    I = np.eye(16)
    return np.stack([mul(s, I[k]) for k in range(16)], axis=1)
