import numpy as np, sys
import os

sys.path.insert(
    0, os.path.dirname(os.path.abspath(__file__))
)  # flowlib.py sits beside this file
import flowlib as fl

rng = np.random.default_rng(688)


def omul(x, y):  # octonion product = CD product on 8-vectors, same convention
    return fl.mul(x, y)


def Hs_basis(s):
    a = s[:8].copy()
    b = s[8:].copy()
    c = b.copy()
    c[0] = 0
    one = np.zeros(8)
    one[0] = 1
    return np.stack([one, a, c, omul(a, c)], 1)  # 8x4


def Os_basis(s):
    H = Hs_basis(s)
    Z = np.zeros_like(H)
    return np.block([[H, Z], [Z, H]])  # 16x8 : H ⊕ Hℓ  (ℓ=(0,1))


def dist(v, B):
    Q, _ = np.linalg.qr(B)
    return np.linalg.norm(v - Q @ (Q.T @ v))


worst_g = worst_f = 0
worst_rank = 8
for s in fl.random_states(200, rng):
    if fl.potential(s) < 1e-6:
        continue
    B = Os_basis(s)
    worst_rank = min(worst_rank, np.linalg.matrix_rank(B, 1e-9))
    g = fl.gradV(s)
    f = fl.ruleField(s)
    worst_g = max(worst_g, dist(g, B) / max(np.linalg.norm(g), 1e-300))
    worst_f = max(worst_f, dist(f, B) / max(np.linalg.norm(f), 1e-300))
print(
    "rank CD(H_s):", worst_rank, " max rel dist ∇V->𝕆_s:", worst_g, " F->𝕆_s:", worst_f
)
# ℓ ∈ 𝕆_s and ℓ-axis map stays in leaf; Langevin step leaves it
s = next(iter(fl.random_states(1, rng)))
B = Os_basis(s)
ell = np.zeros(16)
ell[8] = 1
t = (s + ell) / np.linalg.norm(s + ell)
print("ℓ-axis image dist to 𝕆_s:", dist(t, B), " ℓ dist:", dist(ell, B))
noise = rng.normal(size=16)
noise[0] = 0
noise -= noise @ s * s
noise *= 1e-3
print("Langevin-type noisy step dist to 𝕆_s (expected ~1e-3):", dist(s + noise, B))


# Hessian of V restricted transverse to the leaf at an in-flight s: is F's derivative purely tangential? (Gemini S4 kill)
def num_jac(s, h=1e-6):
    J = np.zeros((16, 16))
    for i in range(16):
        e = np.zeros(16)
        e[i] = h
        J[:, i] = (fl.ruleField(s + e) - fl.ruleField(s - e)) / (2 * h)
    return J


Q, _ = np.linalg.qr(B)
P = Q @ Q.T
Pt = np.eye(16) - P
J = num_jac(s)
print(
    "|P⊥ J P| (transverse response to in-leaf motion; must be ~0 by invariance):",
    np.linalg.norm(Pt @ J @ P),
    " |P⊥ J P⊥|:",
    np.linalg.norm(Pt @ J @ Pt),
    " |P J P⊥| (leaf response to transverse kick):",
    np.linalg.norm(P @ J @ Pt),
)
