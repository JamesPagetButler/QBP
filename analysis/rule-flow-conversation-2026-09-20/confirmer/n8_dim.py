import numpy as np, cdx, flow

rng = np.random.default_rng(9)


def locus_pt(u, w):
    u = u.copy()
    u[0] = 0
    w = w.copy()
    w[0] = 0
    w = w - (w @ u) / (u @ u) * u
    u /= np.linalg.norm(u)
    w /= np.linalg.norm(w)
    return np.concatenate([u, w]) / np.sqrt(2)


u0 = np.eye(8)[1].copy()
w0 = np.eye(8)[2].copy()
p = locus_pt(u0, w0)
D = []
for k in range(600):
    q = locus_pt(u0 + 1e-3 * rng.normal(size=8), w0 + 1e-3 * rng.normal(size=8))
    D.append(q - p)
D = np.array(D)
sv = np.linalg.svd(D, compute_uv=False)
print("locus tangent rel singular values:", np.round(sv[:14] / sv[0], 4))
print(
    "locus dimension (rel tol 0.02):",
    int((sv / sv[0] > 0.02).sum()),
    " => codim in S^14 =",
    14 - int((sv / sv[0] > 0.02).sum()),
)
print(
    "max |V-1| over the 600 locus points: %.2e"
    % max(
        abs(
            cdx.V(
                locus_pt(u0 + 1e-3 * rng.normal(size=8), w0 + 1e-3 * rng.normal(size=8))
            )
            - 1
        )
        for _ in range(50)
    )
)
# F = 0 on the whole locus?
mx = 0
for k in range(300):
    q = locus_pt(rng.normal(size=8), rng.normal(size=8))
    mx = max(mx, np.linalg.norm(flow.F(q)))
print("max ||F|| over 300 random locus points: %.3e" % mx)
