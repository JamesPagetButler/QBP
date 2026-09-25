"""ATTACK 1 / leg B — numerical Hessian isotropy at random vacua.
At a vacuum x (V=0, global min on R^16 so ∇V=0 there) the intrinsic Hessian of V on T_x S^14 equals the ambient
Hessian restricted to T_x S^14. V is a quartic, so the Richardson combination (4Q(h)-Q(2h))/3 of central
differences Q(h) = (V(x+hv)+V(x-hv)-2V(x))/h² is exact up to rounding. Expect: 8 zero eigenvalues, 6 equal to 8(1-b0²).
"""

import numpy as np
from flowlib import potential, gradV_exact

rng = np.random.default_rng(473)
out = open("hessian_isotropy_out.txt", "w")


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    out.write(s + "\n")


def vacuum(b0, theta, u):
    r = np.sqrt(1 - b0 * b0)
    x = np.zeros(16)
    x[1:8] = r * np.cos(theta) * u
    x[8] = b0
    x[9:16] = r * np.sin(theta) * u
    return x


def D2(x, v, h=1e-2):
    Vx = potential(x)
    Q = lambda hh: (potential(x + hh * v) + potential(x - hh * v) - 2 * Vx) / hh**2
    return (4 * Q(h) - Q(2 * h)) / 3


worst_zero, worst_iso, worst_grad = 0, 0, 0
b0s = list(rng.uniform(-0.95, 0.95, 47)) + [0.0, 0.99, -0.999]
for k, b0 in enumerate(b0s):
    theta = rng.uniform(0, 2 * np.pi)
    u = rng.normal(size=7)
    u /= np.linalg.norm(u)
    x = vacuum(b0, theta, u)
    assert abs(np.dot(x, x) - 1) < 1e-14 and potential(x) < 1e-28
    worst_grad = max(worst_grad, np.abs(gradV_exact(x)).max())
    # orthonormal basis of T_x S^14 ∩ {x0=0}
    E = np.eye(16)[1:]
    E = E - np.outer(E @ x, x)
    Q, _ = np.linalg.qr(E.T)
    T = Q[:, :14].T  # 14 x 16 (rank check below)
    assert np.linalg.matrix_rank(E, 1e-10) == 14
    H = np.zeros((14, 14))
    for i in range(14):
        H[i, i] = D2(x, T[i])
        for j in range(i):
            H[i, j] = H[j, i] = (D2(x, T[i] + T[j]) - D2(x, T[i] - T[j])) / 4
    ev = np.sort(np.linalg.eigvalsh(H))
    lam = 8 * (1 - b0 * b0)
    z = np.abs(ev[:8]).max()
    iso = np.abs(ev[8:] - lam).max()
    worst_zero, worst_iso = max(worst_zero, z), max(worst_iso, iso)
    if k < 5 or k >= 47:
        P(
            "vacuum %2d  b0=%+.4f  8(1-b0^2)=%.6f  ev[0:8] max|.|=%.1e  ev[8:14]=%s"
            % (k, b0, lam, z, np.array2string(ev[8:], precision=7))
        )
P(
    "\n50 random vacua: max |zero eigenvalue| = %.2e ; max |ev - 8(1-b0^2)| over the 6 transverse eigenvalues = %.2e ; max |gradV| at vacua = %.1e"
    % (worst_zero, worst_iso, worst_grad)
)
P(
    "PASS (rank 6, single transverse eigenvalue 8(1-b0^2) to 1e-6)"
    if worst_iso < 1e-6 and worst_zero < 1e-6
    else "FAIL"
)
out.close()
