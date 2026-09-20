import numpy as np, sys

sys.path.insert(
    0,
    "/home/prime/Documents/QBP/.claude/worktrees/probe-encode-bundle/analysis/473-dirac-probe",
)
from dirac_probe import cd_mul

N = 16


def V(s):
    a = np.r_[s[:8], np.zeros(8)]
    b = np.r_[s[8:], np.zeros(8)]
    return float(np.sum((cd_mul(a, b)[:8] - cd_mul(b, a)[:8]) ** 2))


def vacuum(u, al, ga, b0):
    s = np.zeros(N)
    s[:8] = al * u
    s[8] = b0
    s[8:] += ga * u
    return s


def hess_trace_and_spec(s, h=1e-4):
    # tangent space to S^13 inside Im(S) (coords 1..15), orthogonal to s
    E = np.eye(N)[1:]  # 15 vectors
    P = E - np.outer(E @ s, s)
    Q, R = np.linalg.qr(P.T)
    keep = np.abs(np.diag(R)) > 1e-8
    B = Q.T[keep[: Q.T.shape[0]]] if keep.shape[0] >= Q.T.shape[0] else Q.T
    B = B[:14]
    f = lambda x: V(x / np.linalg.norm(x))
    m = B.shape[0]
    H = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            H[i, j] = H[j, i] = (
                f(s + h * B[i] + h * B[j])
                - f(s + h * B[i] - h * B[j])
                - f(s - h * B[i] + h * B[j])
                + f(s - h * B[i] - h * B[j])
            ) / (4 * h * h)
    e = np.linalg.eigvalsh(H)
    return e.sum(), e


rng = np.random.default_rng(11)
u = rng.normal(size=8)
u[0] = 0
u /= np.linalg.norm(u)
print(" b0      trace      48*(1-b0^2)   max eig   #nonzero eig")
for b0 in [0.0, 0.3, 0.5, 0.7071, 0.866, 0.95, 1.0]:
    r = np.sqrt(max(0.0, 1 - b0**2))
    al, ga = r * 0.6, r * 0.8
    s = vacuum(u, al, ga, b0)
    assert V(s) < 1e-20
    tr, e = hess_trace_and_spec(s)
    print(
        f" {b0:5.3f}  {tr:9.4f}   {48*(1-b0**2):9.4f}   {e.max():7.4f}   {(abs(e)>1e-6).sum():3d}"
    )
# independence of u and of the (alpha,gamma) phase at fixed b0
b0 = 0.5
vals = []
for _ in range(4):
    uu = rng.normal(size=8)
    uu[0] = 0
    uu /= np.linalg.norm(uu)
    th = rng.uniform(0, 2 * np.pi)
    r = np.sqrt(1 - b0**2)
    tr, _ = hess_trace_and_spec(vacuum(uu, r * np.cos(th), r * np.sin(th), b0))
    vals.append(tr)
print("b0=0.5 fixed, random u and phase: traces", [round(v, 4) for v in vals])
