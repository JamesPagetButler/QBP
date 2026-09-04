import numpy as np

exec(open("dirac_probe.py").read().split("np.set_printoptions")[0])
E = basis(16)
x = E[1] + E[10]
y = E[4] - E[15]  # ZD pair (partner found earlier)
print("xy =", np.round(cd_mul(x, y), 6).any())
J = np.column_stack([R(y, 16), L(x, 16)])  # d(xy) = (dx) y + x (dy)
H = 2 * J.T @ J
print("ledger-type Hessian spec:", spec(H))
print("Tr H, Tr H^2 =", np.trace(H), np.trace(H @ H))
print(
    "block xx == -2 R_y^2 :",
    np.allclose(H[:16, :16], -2 * R(y, 16) @ R(y, 16)),
    spec(H[:16, :16]),
)
print(
    "block yy == -2 L_x^2 :",
    np.allclose(H[16:, 16:], -2 * L(x, 16) @ L(x, 16)),
    spec(H[16:, 16:]),
)
