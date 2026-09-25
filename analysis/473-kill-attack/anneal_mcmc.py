"""ATTACK 1 / leg B — MCMC Gibbs anneal on S^14, weight e^{-beta V}, V = flowlib.potential (full sedenion
commutator; NO reduction to invariants). Random-walk Metropolis with the symmetric proposal
x' = normalise(x + eps*xi), xi ~ N(0, I_15) (density depends only on <x,x'>, hence symmetric).
K independent chains -> SE of the grand mean = std(chain means)/sqrt(K) (chains are iid).
Two initial ensembles: (I) Haar; (II) all chains near the pole +l (b0 ≈ 0.999). Agreement = mixing along M.
"""

import sys, time
import numpy as np
from flowlib import potential, random_states

K = 8192
BETAS = [10, 30, 100, 300, 1000]
STEPS = {
    10: (2000, 4000),
    30: (2000, 4000),
    100: (3000, 6000),
    300: (4000, 8000),
    1000: (6000, 12000),
}
out = open("anneal_mcmc_out.txt", "a")


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    out.write(s + "\n")
    out.flush()


def run(init, rng, tag):
    x = init.copy()
    V = potential(x)
    eps = 0.3
    P("\n== init %s ==  <b0^2>_init = %.4f" % (tag, (x[:, 8] ** 2).mean()))
    P(
        "beta   eps      acc     <b0^2>   SE       <b0^2>(first half)  (second half)  <V>"
    )
    for beta in BETAS:
        nb, ns = STEPS[beta]
        acc_hist = []
        sums = np.zeros(K)
        sums1 = np.zeros(K)
        vsum = 0.0
        for it in range(nb + ns):
            xi = rng.normal(size=(K, 16))
            xi[:, 0] = 0
            y = x + eps * xi
            y /= np.linalg.norm(y, axis=1, keepdims=True)
            Vy = potential(y)
            accept = rng.random(K) < np.exp(-beta * (Vy - V))
            x[accept] = y[accept]
            V[accept] = Vy[accept]
            a = accept.mean()
            acc_hist.append(a)
            if it < nb:
                if it % 50 == 49:  # adapt eps toward acceptance 0.30 during burn-in
                    m = np.mean(acc_hist[-50:])
                    eps *= np.exp(0.5 * (m - 0.30))
            else:
                b2 = x[:, 8] ** 2
                sums += b2
                if it - nb < ns // 2:
                    sums1 += b2
                vsum += V.mean()
        cm = sums / ns
        mean, se = cm.mean(), cm.std(ddof=1) / np.sqrt(K)
        P(
            "%-6d %.4f   %.3f   %.4f   %.4f   %.4f              %.4f         %.4e"
            % (
                beta,
                eps,
                np.mean(acc_hist[nb:]),
                mean,
                se,
                (sums1 / (ns // 2)).mean(),
                ((sums - sums1) / (ns - ns // 2)).mean(),
                vsum / ns,
            )
        )
    return x


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "haar"
    rng = np.random.default_rng(2026 if which == "haar" else 924)
    t0 = time.time()
    if which == "haar":
        init = random_states(K, rng)
    else:
        init = random_states(K, rng) * 0.045
        init[:, 8] += 1.0
        init /= np.linalg.norm(init, axis=1, keepdims=True)
    run(init, rng, which)
    P("wall %.0f s" % (time.time() - t0))
