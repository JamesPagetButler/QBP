import numpy as np, cdx


def gradV(s):
    a, b = s[..., :8], s[..., 8:]
    c = cdx.omul(a, b) - cdx.omul(b, a)
    bb = b.copy()
    bb[..., 1:] *= -1
    aa = a.copy()
    aa[..., 1:] *= -1
    ga = 2 * (cdx.omul(c, bb) - cdx.omul(bb, c))
    gb = 2 * (cdx.omul(aa, c) - cdx.omul(c, aa))
    return np.concatenate([ga, gb], axis=-1)


def F(s):
    g = gradV(s)
    dot = (g * s).sum(-1, keepdims=True)
    out = g - dot * s
    out[..., 0] -= g[..., 0]  # subtract (gradV)_0 * 1
    return -out
