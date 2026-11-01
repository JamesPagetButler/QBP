#!/usr/bin/env python3
"""qbp-kz-g2 round 1 — director's independent recompute of the frozen §3 reading.

Reads the four committed raw files (raw/qbp-kz-g2-r1-0b-tau<τ>.jsonl), recomputes
gap(τ) = max over the 41 grid points of |mean S_cool − mean S_heat| from the `stage0b`
record (seed-mean curves), applies the frozen rule with precedence (b) → (a) → (c),
the OLS slope of ln gap on ln τ_Q (2 dof), P4, and the jump clause, and draws the two
HVR plots. It is deliberately independent of the Go analyzer (`mdcu-kz -analyze-0b`):
it uses only the raw `grid`, `cool`, `heat`, `cool_series`, `heat_series` arrays and
never reads the analyzer's own `max_gap*` fields except to print them beside the
recomputed values for comparison.

Usage (from spikes/qbp-kz-g2/):  python3 qbp-kz-g2-r1-recompute.py [--plots]
Exit 0; prints the table and the verdict. Pure stdlib + matplotlib (plots only).
"""

import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TAUS = [1600, 3200, 6400, 12800]
TC = 1.0666262219986817
B_THRESH = 0.05  # frozen §3 (b)
A_RATIO = 0.6  # frozen §3 (a)
JUMP = 0.10  # frozen §3 jump clause, fraction of S_max = 1


def load(tau):
    path = os.path.join(HERE, "raw", f"qbp-kz-g2-r1-0b-tau{tau}.jsonl")
    recs = [json.loads(line) for line in open(path)]
    kinds = {r["kind"] for r in recs}
    assert kinds == {"meta", "stage0b", "end"}, kinds
    meta = next(r for r in recs if r["kind"] == "meta")
    s = next(r for r in recs if r["kind"] == "stage0b")
    end = next(r for r in recs if r["kind"] == "end")
    assert meta["tau"] == tau and s["tau"] == tau and end["exit_code"] == 0
    assert meta["rerun"] is False and meta["rerun_amend_sha"] == ""
    return meta, s, end


def seed_mean_jump(series):
    """largest |step| of the seed-mean curve over consecutive recorded steps."""
    n = len(series[0])
    means = [sum(row[i] for row in series) / len(series) for i in range(n)]
    best = 0.0
    for i in range(1, n):
        best = max(best, abs(means[i] - means[i - 1]))
    return best


def per_seed_jump(series):
    """POST-HOC SUPPLEMENTARY (Gemini r1 on PR #796; not pre-registered, non-gating):
    largest |step| over consecutive recorded steps for EACH seed's own series, returned as
    (max over seeds, min over seeds, count of seeds whose largest step > JUMP)."""
    per = []
    for row in series:
        best = 0.0
        for i in range(1, len(row)):
            best = max(best, abs(row[i] - row[i - 1]))
        per.append(best)
    return max(per), min(per), sum(1 for b in per if b > JUMP)


def main():
    gaps, data, rows = {}, {}, []
    for tau in TAUS:
        meta, s, end = load(tau)
        grid, cool, heat = s["grid"], s["cool"], s["heat"]
        assert len(grid) == len(cool) == len(heat) == meta["ngrid"] == 41
        diffs = [abs(c - h) for c, h in zip(cool, heat)]
        i = max(range(len(diffs)), key=lambda k: diffs[k])
        gaps[tau] = diffs[i]
        data[tau] = (grid, cool, heat)
        cj = seed_mean_jump(s["cool_series"])
        hj = seed_mean_jump(s["heat_series"])
        rows.append(
            (
                tau,
                diffs[i],
                i,
                grid[i],
                len(s["seeds"]),
                cj,
                hj,
                s["max_gap"],
                s["max_gap_idx"],
            )
        )
    print(
        "| tau_Q | gap (recomputed) | idx | T | seeds | max cool step | max heat step | jump>0.10 | analyzer max_gap (idx) |"
    )
    print("|---|---|---|---|---|---|---|---|---|")
    for tau, g, i, T, n, cj, hj, ag, ai in rows:
        print(
            f"| {tau} | {g:.4f} | {i} | {T:.4f} | {n} | {cj:.4f} | {hj:.4f} | {'yes' if max(cj, hj) > JUMP else 'no'} | {ag:.4f} ({ai}) |"
        )
    g = gaps
    b_fires = g[12800] < B_THRESH
    a_fires = g[12800] >= A_RATIO * g[1600]
    print(f"(b) gap(12800)={g[12800]:.4f} < {B_THRESH} -> {b_fires}")
    print(
        f"(a) gap(12800)={g[12800]:.4f} >= {A_RATIO}*gap(1600)={A_RATIO * g[1600]:.4f} -> {a_fires}"
    )
    if b_fires:
        tstar = min(t for t in TAUS if g[t] < B_THRESH)
        verdict = f"H-slow by rule (b); premise restored at tau_Q = {tstar}"
    elif a_fires:
        verdict = "H-first by rule (a)"
    else:
        verdict = "inconclusive (rate) by rule (c)"
    print(f"OUTCOME: {verdict}")
    fit = [t for t in TAUS if g[t] > 0]
    xs, ys = [math.log(t) for t in fit], [math.log(g[t]) for t in fit]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx
    icpt = my - slope * mx
    res = [y - (icpt + slope * x) for x, y in zip(xs, ys)]
    se = math.sqrt((sum(r * r for r in res) / (n - 2)) / sxx)
    print(
        f"OLS slope ln gap vs ln tau_Q: {slope:.4f} +/- {se:.4f} (n={n}, {n - 2} dof)"
    )
    p4 = abs(g[1600] - 0.5176) < 0.05
    print(f"P4: gap(1600)={g[1600]:.4f} vs round-1 0.5176 -> {'hit' if p4 else 'miss'}")
    print(
        "post-hoc supplementary, NOT pre-registered, decides nothing (Gemini r1 on PR #796): per-seed largest single-step |dS|"
    )
    print(
        "| tau_Q | cool: max / min over seeds | cool seeds > 0.10 | heat: max / min over seeds | heat seeds > 0.10 |"
    )
    print("|---|---|---|---|---|")
    for tau in TAUS:
        _, s, _ = load(tau)
        cmax, cmin, cn = per_seed_jump(s["cool_series"])
        hmax, hmin, hn = per_seed_jump(s["heat_series"])
        print(
            f"| {tau} | {cmax:.4f} / {cmin:.4f} | {cn}/{len(s['seeds'])} | {hmax:.4f} / {hmin:.4f} | {hn}/{len(s['seeds'])} |"
        )
    if "--plots" in sys.argv:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        os.makedirs(os.path.join(HERE, "plots"), exist_ok=True)
        fig, axs = plt.subplots(1, 4, figsize=(16, 4), sharey=True)
        for ax, tau in zip(axs, TAUS):
            grid, cool, heat = data[tau]
            ax.plot(grid, cool, "o-", ms=3, label="cool (T↓)")
            ax.plot(grid, heat, "s-", ms=3, label="heat (T↑)")
            ax.axvline(TC, color="gray", ls=":", lw=1)
            ax.set_title(f"τ_Q = {tau}   gap = {g[tau]:.3f}")
            ax.set_xlabel("T")
            ax.grid(alpha=0.3)
        axs[0].set_ylabel("seed-mean order parameter S / S_max")
        axs[0].legend()
        fig.suptitle(
            "qbp-kz-g2 round 1, Stage 0b: cool vs heat curves, L=16, 10 seeds per rung (hysteresis persists to τ_Q = 12800)"
        )
        fig.tight_layout()
        fig.savefig(os.path.join(HERE, "plots", "kz-g2-r1-curves.png"), dpi=110)
        fig2, ax = plt.subplots(figsize=(5, 4))
        ax.loglog(TAUS, [g[t] for t in TAUS], "o-", label="gap(τ_Q)")
        ax.axhline(B_THRESH, color="r", ls="--", label="(b) H-slow threshold 0.05")
        ax.axhline(A_RATIO * g[1600], color="g", ls="--", label="(a) 0.6·gap(1600)")
        ax.set_xlabel("τ_Q")
        ax.set_ylabel("max |S_cool − S_heat| / S_max")
        ax.set_ylim(0.02, 1)
        ax.legend(fontsize=8)
        ax.grid(alpha=0.3, which="both")
        ax.set_title(f"gap vs τ_Q; OLS slope {slope:.3f} ± {se:.3f}")
        fig2.tight_layout()
        fig2.savefig(os.path.join(HERE, "plots", "kz-g2-r1-gap-vs-tau.png"), dpi=110)
        print("plots written")
    return 0


if __name__ == "__main__":
    sys.exit(main())
