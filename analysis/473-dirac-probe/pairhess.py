import numpy as np

exec(open("dirac_probe.py").read().split("np.set_printoptions")[0])
exec(open("landscape.py").read().split("E=basis(16)")[0].split("def report")[0])
n = 16
E = basis(16)
x = (E[1] + E[10]) / np.sqrt(2)
# find ZD partner among basis pair combos
part = None
for c in range(1, 8):
    for d in range(9, 16):
        for sd in (1, -1):
            y = (E[c] + sd * E[d]) / np.sqrt(2)
            if np.allclose(cd_mul(x, y), 0):
                part = (c, d, sd, y)
                print("partner: e%d %+d e%d" % (c, sd, d))
y = part[3]
g = lambda z: (lambda p: (p @ p))(cd_mul(z[:16], z[16:])) - (z[:16] @ z[:16]) * (
    z[16:] @ z[16:]
)
H = hess(g, np.concatenate([x, y]))
w = np.linalg.eigvalsh((H + H.T) / 2)
vals, cnt = np.unique(np.round(w, 3), return_counts=True)
print("Hessian of N(xy)-N(x)N(y) at ZD pair (32-dim):", list(zip(vals, cnt)))
# and the Hessian of the associator-norm-type function |[x,x,y]|^2 ?
T = lambda z: (
    lambda s, t: (lambda v: v @ v)(cd_mul(cd_mul(s, s), t) - cd_mul(s, cd_mul(s, t)))
)(z[:16], z[16:])
H2 = hess(T, np.concatenate([x, y]))
w = np.linalg.eigvalsh((H2 + H2.T) / 2)
vals, cnt = np.unique(np.round(w, 3), return_counts=True)
print("Hessian of |[x,x,y]|^2 at ZD pair:", list(zip(vals, cnt)))
