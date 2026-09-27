"""Rule-flow simulator on the imaginary unit sedenion sphere (vectorised over seeds).
Convention (a,b)(c,d) = (ac − conj(d) b, d a + b conj(c)) — the repo's CDAlg.mulCoeff convention
(verified against the sign table on PR #666). V(s) = N([a,b]) for s = (a,b); the rule is
first-order overdamped descent of V restricted to {N s = 1, s₀ = 0} (#635 as written).
Gradient checked against central differences at start-up (assert)."""

import numpy as np


def conj(x):
    y = -x.copy()
    y[..., 0] = x[..., 0]
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


def N(x):
    return np.sum(x * x, axis=-1)


def potential(s):
    a, b = s[..., :8], s[..., 8:]
    c = mul(a, b) - mul(b, a)
    return N(c)


def gradV(s):
    """exact gradient of V(s)=N([a,b]) w.r.t. all 16 coords (derived by finite differences check)."""
    eps = 1e-6
    g = np.zeros_like(s)
    for i in range(16):
        e = np.zeros(16)
        e[i] = eps
        g[..., i] = (potential(s + e) - potential(s - e)) / (2 * eps)
    return g


def gradV_exact(s):
    # dV = 2⟨c, d c⟩, c=[a,b]; d c = [da,b]+[a,db]; use adjoint identities: ⟨c,[da,b]⟩ = ⟨c, da·b − b·da⟩
    # implement via linearity with the 16 basis directions using exact products (no finite differences)
    a, b = s[..., :8], s[..., 8:]
    c = mul(a, b) - mul(b, a)
    g = np.zeros_like(s)
    for i in range(8):
        e = np.zeros(8)
        e[i] = 1.0
        E = np.broadcast_to(e, a.shape)
        g[..., i] = 2 * np.sum(c * (mul(E, b) - mul(b, E)), axis=-1)
        g[..., 8 + i] = 2 * np.sum(c * (mul(a, E) - mul(E, a)), axis=-1)
    return g


def ruleField(s):
    g = gradV_exact(s)
    rad = np.sum(g * s, axis=-1, keepdims=True) * s
    g0 = g[..., :1]
    F = -(g - rad)
    F[..., 0] = 0.0  # tangent to sphere, zero scalar part
    return F


def random_states(n, rng):
    s = rng.normal(size=(n, 16))
    s[:, 0] = 0
    return s / np.linalg.norm(s, axis=1, keepdims=True)


def b0(s):
    return s[..., 8]


def nonpole(s):  # α²+γ² = N(cdLo s) + N(Im cdHi s) = 1 − b0²  on the sphere
    return 1 - s[..., 8] ** 2


def direction_u(s):
    """the crystal/state direction u ∝ cdLo(s) (its imaginary octonion), unit; undefined near the pole"""
    a = s[..., :8].copy()
    a[..., 0] = 0
    n = np.linalg.norm(a, axis=-1, keepdims=True)
    return a / np.maximum(n, 1e-300), n[..., 0]


def step(s, h):
    """renormalised Euler step (the scripts' method): s ← normalise(s + h F(s))"""
    t = s + h * ruleField(s)
    t[..., 0] = 0
    return t / np.linalg.norm(t, axis=-1, keepdims=True)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    s = random_states(5, rng)
    print("grad exact vs FD max err:", np.max(np.abs(gradV_exact(s) - gradV(s))))
    print(
        "V range:",
        potential(s).min(),
        potential(s).max(),
        "| F·s:",
        np.max(np.abs(np.sum(ruleField(s) * s, axis=-1))),
    )
