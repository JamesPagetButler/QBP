import numpy as np, cdx, flow

rng = np.random.default_rng(5)
# identity  V(s) = 4(|Im a|^2 |Im b|^2 - <Im a, Im b>^2)   for arbitrary s in CDAlg R 4
S = rng.normal(size=(4000, 16)) * rng.uniform(0.2, 3, size=(4000, 1))
a, b = S[:, :8], S[:, 8:]
ia = a.copy()
ia[:, 0] = 0
ib = b.copy()
ib[:, 0] = 0
pred = 4 * ((ia * ia).sum(1) * (ib * ib).sum(1) - ((ia * ib).sum(1)) ** 2)
print(
    "V = 4(|Ia|^2|Ib|^2 - <Ia,Ib>^2) : max abs err %.3e over 4000 arbitrary s"
    % np.abs(cdx.V(S) - pred).max()
)
print("N^2 - V >= 0 : min %.6f" % (cdx.N(S) ** 2 - cdx.V(S)).min())
# equality locus: a0=b0=0, |a|^2=|b|^2=N/2, <a,b>=0  -> V = N^2 and s is a zero divisor
kd = []
vs = []
for k in range(200):
    u = rng.normal(size=8)
    u[0] = 0
    w = rng.normal(size=8)
    w[0] = 0
    w = w - (w @ u) / (u @ u) * u
    u /= np.linalg.norm(u)
    w /= np.linalg.norm(w)
    r = rng.uniform(0.3, 2.0)
    s = np.concatenate([r * u, r * w]) / np.sqrt(2)
    sv = np.linalg.svd(cdx.Lmat(s), compute_uv=False)
    kd.append(int((sv < 1e-9).sum()))
    vs.append(cdx.V(s) - cdx.N(s) ** 2)
print(
    "constructed equality points (200): max |V - N^2| = %.2e ; kernel dims = %s"
    % (max(abs(np.array(vs))), sorted(set(kd)))
)
# locus dimension on S^14 by parameter count (a in S^6 scaled, b in S^6 cap a-perp)
print(
    "locus parametrisation dim: a-direction 6 + b-direction 5 = 11  (codim 3 in S^14)"
)
# empirical: tangent rank at a locus point
p = np.concatenate([np.eye(8)[1], np.eye(8)[2]]) / np.sqrt(2)
D = []
for k in range(400):
    u = rng.normal(size=8)
    u[0] = 0
    w = rng.normal(size=8)
    w[0] = 0
    w = w - (w @ u) / (u @ u) * u
    u /= np.linalg.norm(u)
    w /= np.linalg.norm(w)
    q = np.concatenate([u, w]) / np.sqrt(2)
    if np.linalg.norm(q - p) < 0.25:
        D.append(q - p)
D = np.array(D)
sv = np.linalg.svd(D, compute_uv=False)
print(
    "empirical locus tangent rank (n=%d nearby points):" % len(D),
    int((sv / sv[0] > 0.05).sum()),
    " rel sv:",
    np.round(sv[:14] / sv[0], 3),
)
