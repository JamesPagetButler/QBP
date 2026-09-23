import numpy as np, time, cdx, flow

rng = np.random.default_rng(1)
N = 2000


def proj(s):
    s = s.copy()
    s[..., 0] = 0
    return s / np.linalg.norm(s, axis=-1, keepdims=True)


s = proj(rng.normal(size=(N, 16)))
t0 = time.time()
h = 0.02
for it in range(5000):
    s = proj(s + h * flow.F(s))
    if it % 2500 == 0:
        print(it, "max V %.3e" % cdx.V(s).max(), "%.1fs" % (time.time() - t0))
V = cdx.V(s)
b0 = s[:, 8]
print("steps done in %.1fs" % (time.time() - t0))
print(
    "max endpoint V = %.3e ; fraction with V<1e-8 = %.4f" % (V.max(), (V < 1e-8).mean())
)
print(
    "endpoint <b0^2> = %.4f  (SE %.4f) ;  Haar 1/15 = %.4f ; 1/7 = %.4f"
    % ((b0**2).mean(), (b0**2).std() / np.sqrt(N), 1 / 15, 1 / 7)
)
print("quantiles b0^2:", np.round(np.quantile(b0**2, [0.1, 0.25, 0.5, 0.75, 0.9]), 4))
print(
    "endpoint |a|^2 mean %.4f  |Im b|^2 mean %.4f"
    % ((s[:, :8] ** 2).sum(1).mean(), (s[:, 9:] ** 2).sum(1).mean())
)
