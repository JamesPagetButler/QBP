import numpy as np

exec(open("dirac_probe.py").read().split("np.set_printoptions")[0])
n = 16


def V(s):  # ||[a,b]||^2  with s=(a,b), a in O (first 8), b in O
    a, b = s[:8], s[8:]
    c = cd_mul(a, b) - cd_mul(b, a)
    return c @ c


def Vsphere(s):
    return V(s / np.linalg.norm(s))


def hess(f, s, h=1e-4):
    m = len(s)
    H = np.zeros((m, m))
    for i in range(m):
        for j in range(m):
            ei = np.zeros(m)
            ej = np.zeros(m)
            ei[i] = h
            ej[j] = h
            H[i, j] = (
                f(s + ei + ej) - f(s + ei - ej) - f(s - ei + ej) + f(s - ei - ej)
            ) / (4 * h * h)
    return H


def report(name, s):
    s = s / np.linalg.norm(s)
    H = hess(
        Vsphere, s
    )  # Hessian of V restricted to sphere via normalisation (radial dir = 0)
    # project to tangent space of S^14 inside Im S (drop e0 which V ignores anyway)
    w = np.linalg.eigvalsh((H + H.T) / 2)
    vals, cnt = np.unique(np.round(w, 3), return_counts=True)
    print(f"{name}: V={V(s):.4f}  Hessian(V|S^14) spectrum:", list(zip(vals, cnt)))


E = basis(16)
# delta=0 vacuum: s in an octonion subalgebra, e.g. a=e1 (b=0) ; also s=(e1, e1) ; also generic a||Im b
report("vac  s=e1        ", E[1])
report("vac  s=(e1+e9)/√2", E[1] + E[9])  # a=e1, b=e1 (Im b || a)
report("vac  s=ℓ=e8      ", E[8])  # a=0, b=1
report("vac  s=(e1+e8)/√2", E[1] + E[8])  # a=e1, b=1 (Im b=0)
rng = np.random.default_rng(5)
u = rng.normal(size=8)
u[0] = 0
u /= np.linalg.norm(u)
sv = np.concatenate([0.6 * u, 0.5 * u])
sv[8] = 0.3
report("vac  generic a||Imb ", sv)
# ZD maximum: a=e1, b=e2 -> s=(e1+e10)/√2
report("max  s=(e1+e10)/√2", E[1] + E[10])
a = rng.normal(size=8)
a[0] = 0
a /= np.linalg.norm(a)
b = rng.normal(size=8)
b[0] = 0
b -= (b @ a) * a
b /= np.linalg.norm(b)
report("max  generic a⊥Imb", np.concatenate([a, b]))
