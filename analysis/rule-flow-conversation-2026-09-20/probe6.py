import numpy as np
from fast import *
from cd import mul, conj

rng = np.random.default_rng(31)
# A) Gemini's corrected defect formula
err = 0.0
for _ in range(300):
    s = rng.normal(size=16)
    x = rng.normal(size=16)
    a, b = s[:8], s[8:]
    c, d = x[:8], x[8:]
    D = float((mul(s, x) ** 2).sum() - (s @ s) * (x @ x))
    pred = 2 * float(o(d, a) @ o(b, conj(c))) - 2 * float(o(a, c) @ o(conj(d), b))
    err = max(err, abs(D - pred))
print("A) max |Delta - 2<da,b cbar> + 2<ac, dbar b>| over 300:", err)


# B) divergence of F on the state sphere (intrinsic: trace of dF restricted to tangent space)
def dF(s, h=1e-5):
    J = np.zeros((16, 16))
    for k in range(16):
        e = np.zeros(16)
        e[k] = h
        J[:, k] = (F(s + e) - F(s - e)) / (2 * h)
    return J


def tang_basis(s):
    A = np.eye(16)
    A = np.delete(A, 0, axis=1)  # drop e0 direction
    A = A - np.outer(s, s @ A)  # project off s
    q, _ = np.linalg.qr(A)
    return q[:, :14]


res = []
for t in range(12):
    s = rng.normal(size=16)
    s[0] = 0
    s /= np.linalg.norm(s)
    T = tang_basis(s)
    J = dF(s)
    res.append((float(V(s)), float(np.trace(T.T @ J @ T))))
for v, dv in res:
    print("   V=%.4f  div_T F=%+.4f" % (v, dv))
print(
    "B) sign summary: negatives %d / %d" % (sum(1 for _, d in res if d < 0), len(res))
)
# C) V <= N^2 elementary route: check ||x cross y||^2 = |x|^2|y|^2 - <x,y>^2 for imaginary octonions
e = 0.0
for _ in range(200):
    x = rng.normal(size=8)
    x[0] = 0
    y = rng.normal(size=8)
    y[0] = 0
    cr = 0.5 * (o(x, y) - o(y, x))
    e = max(e, abs(float(cr @ cr) - (float(x @ x) * float(y @ y) - float(x @ y) ** 2)))
print("C) max |‖x×y‖² − (|x|²|y|² − <x,y>²)| over 200 imaginary octonion pairs:", e)
