#!/usr/bin/env python3
"""qbp-kz-g2 round 3 — director's independent recompute of the FROZEN-v1 §3 reading.

Recomputes every §3 statistic from the RAW per-seed series only (the `e_series`,
`s_series`, `seed`, `start` fields of each run in the `eq` record, plus L / T /
t_index from the record header). No harness-derived field (tau_int_rec, n_eff,
undersampled, sokal_w) and no analyzer output is read for the computation; the
analyzer's text report is parsed ONLY for the side-by-side comparison table.

Frozen rule: QBP PR #800 @ ae37319, spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md,
sha256 132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623.

usage: python3 qbp-kz-g2-r3-recompute.py --raw <dir> --out <dir> [--plots] [--analyzer <analyze-eq.out>]
stdlib + matplotlib only.
"""

import argparse
import glob
import json
import math
import os
import re
import sys

FROZEN_SHA = "132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623"
FROZEN_SHORT = FROZEN_SHA[:8]
NBINS = 60
SMOOTH = 3
SIGMA_FLOOR = 3.0
DF0 = math.log(2.0)
EPS_FLOOR = 0.2
BLOCK = 250
D_THRESH = 3.0
NEFF_MIN = 20.0
T_GRID = [1.08, 1.10, 1.12, 1.13, 1.14, 1.15, 1.16, 1.17, 1.18, 1.20]
L_LIST = [8, 12, 16]
EXPECTED_T = {8: [0, 1, 2, 4, 6, 8, 9], 12: list(range(10)), 16: list(range(10))}

# ----------------------------------------------------------------------------
# loading
# ----------------------------------------------------------------------------


def load_raw(raw_dir):
    """Return {(L, t): point} with point = {L, T, t, runs: [{seed, start, e, s}]}.
    Only raw series fields are kept."""
    files = sorted(glob.glob(os.path.join(raw_dir, "qbp-kz-g2-r3-eq-L*-t*.jsonl")))
    pts = {}
    for f in files:
        meta = eq = end = None
        with open(f) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                d = json.loads(line)
                k = d.get("kind")
                if k == "meta":
                    meta = d
                elif k == "eq":
                    eq = d
                elif k == "end":
                    end = d
        if meta is None or eq is None or end is None:
            raise SystemExit("incomplete raw file (meta/eq/end missing): %s" % f)
        if meta.get("mode") != "eq":
            raise SystemExit("mode is not eq: %s" % f)
        if meta.get("prereg_sha") != FROZEN_SHA:
            raise SystemExit(
                "prereg_sha mismatch in %s: %s" % (f, meta.get("prereg_sha"))
            )
        if end.get("exit_code") != 0 or end.get("verdict") != "eq complete":
            raise SystemExit("run not complete: %s" % f)
        L = int(eq["L"])
        t = int(eq["t_index"])
        T = float(eq["T"])
        runs = []
        for r in eq["runs"]:
            e = [float(x) for x in r["e_series"]]
            s = [float(x) for x in r["s_series"]]
            if len(e) != 5000 or len(s) != 5000:
                raise SystemExit("series length != 5000 in %s seed %s" % (f, r["seed"]))
            runs.append({"seed": int(r["seed"]), "start": r["start"], "e": e, "s": s})
        if [r["start"] for r in runs] != ["haar", "haar", "aligned"]:
            raise SystemExit("unexpected start pattern in %s" % f)
        pts[(L, t)] = {"L": L, "T": T, "t": t, "runs": runs, "file": f}
    # completeness: exactly 27 (L, t) points of §2
    want = sorted((L, t) for L in L_LIST for t in EXPECTED_T[L])
    if sorted(pts.keys()) != want:
        raise SystemExit("not a complete set: have %s" % sorted(pts.keys()))
    return pts


# ----------------------------------------------------------------------------
# §3 statistics
# ----------------------------------------------------------------------------


def mean(xs):
    return sum(xs) / len(xs)


def bin_edges(lo, hi):
    w = (hi - lo) / NBINS
    return lo, w


def histogram(xs, lo, w):
    h = [0.0] * NBINS
    for x in xs:
        i = int((x - lo) / w)
        if i < 0:
            i = 0
        if i >= NBINS:
            i = NBINS - 1
        h[i] += 1.0
    return h


def smooth3(h):
    """3-bin moving average; the two edge bins average the available neighbours
    (truncated window)."""
    n = len(h)
    out = [0.0] * n
    for i in range(n):
        lo = max(0, i - 1)
        hi = min(n - 1, i + 1)
        out[i] = sum(h[lo : hi + 1]) / (hi - lo + 1)
    return out


def local_maxima(hs):
    """Strict local maxima: a bin strictly above both neighbours. Edge bins have
    only one neighbour and are not candidates."""
    return [i for i in range(1, len(hs) - 1) if hs[i] > hs[i - 1] and hs[i] > hs[i + 1]]


def barrier(hs):
    """Return dict(dF, resolved, i, j, valley_bin, h_lower, h_valley, depth_sigma).
    Candidate pair = two strict local maxima with >= 1 bin between them; the pair
    with the largest RESOLVED barrier is chosen. Resolved iff
    n_lower - n_valley > 3 sqrt(n_lower + n_valley) on the smoothed counts.
    h_valley = 0 -> 0.5 before the log only. Unresolved / unimodal -> dF = 0."""
    peaks = local_maxima(hs)
    best = None
    for a in range(len(peaks)):
        for b in range(a + 1, len(peaks)):
            i, j = peaks[a], peaks[b]
            if j - i < 2:
                continue
            seg = hs[i + 1 : j]
            hv = min(seg)
            vbin = i + 1 + seg.index(hv)
            hl = min(hs[i], hs[j])
            depth = hl - hv
            sig = math.sqrt(hl + hv) if (hl + hv) > 0 else 0.0
            resolved = depth > SIGMA_FLOOR * sig
            if not resolved:
                continue
            hv_log = hv if hv > 0 else 0.5
            dF = math.log(hl / hv_log)
            cand = {
                "dF": dF,
                "resolved": True,
                "i": i,
                "j": j,
                "valley_bin": vbin,
                "h_lower": hl,
                "h_valley": hv_log,
                "h_valley_raw": hv,
                "depth_sigma": depth / sig if sig > 0 else float("inf"),
            }
            if best is None or cand["dF"] > best["dF"]:
                best = cand
    if best is None:
        return {
            "dF": 0.0,
            "resolved": False,
            "i": None,
            "j": None,
            "valley_bin": None,
            "h_lower": 0.0,
            "h_valley": 0.0,
            "h_valley_raw": 0.0,
            "depth_sigma": 0.0,
        }
    return best


def jackknife_se(vals):
    n = len(vals)
    m = mean(vals)
    return math.sqrt((n - 1.0) / n * sum((v - m) ** 2 for v in vals))


def blocked_se(series_list, block):
    """Blocked standard error of the mean of the concatenation of the given
    series, with blocks that never straddle two series (each series is split
    into len/block blocks). SE = sqrt( sum (b_i - bbar)^2 / (Nb (Nb-1)) )."""
    bm = []
    for s in series_list:
        nb = len(s) // block
        for k in range(nb):
            bm.append(mean(s[k * block : (k + 1) * block]))
    nb = len(bm)
    m = mean(bm)
    var = sum((b - m) ** 2 for b in bm) / (nb - 1)
    return math.sqrt(var / nb)


def autocorr_tau_sokal(x):
    """tau(W) = 1/2 + sum_{k=1}^{W} rho(k); W = smallest W with W >= 6 tau(W).
    rho(k) = c(k)/c(0), c(k) = (1/(N-k)) sum (x_i - xbar)(x_{i+k} - xbar).
    Returns (tau, W). Record units."""
    n = len(x)
    m = mean(x)
    d = [v - m for v in x]
    c0 = sum(v * v for v in d) / n
    if c0 == 0:
        return 0.5, 0
    tau = 0.5
    W = 0
    while True:
        W += 1
        if W >= n - 1:
            break
        ck = 0.0
        for i in range(n - W):
            ck += d[i] * d[i + W]
        ck /= n - W
        tau += ck / c0
        if W >= 6.0 * tau:
            break
    return tau, W


def binder(xs):
    m2 = mean([v * v for v in xs])
    m4 = mean([v**4 for v in xs])
    return 1.0 - m4 / (3.0 * m2 * m2)


def max_step(xs):
    """Largest single-record change |x[k+1] - x[k]|; the index reported is k, the
    0-based index of the earlier record of the pair (the frozen text names no index
    convention; this is the one the analyzer's table uses)."""
    best, idx = 0.0, 0
    for i in range(1, len(xs)):
        dlt = abs(xs[i] - xs[i - 1])
        if dlt > best:
            best, idx = dlt, i - 1
    return best, idx


def analyse(pts):
    res = {"L": {}, "points": {}, "runs": []}
    for L in L_LIST:
        ts = EXPECTED_T[L]
        pooled_e = [v for t in ts for r in pts[(L, t)]["runs"] for v in r["e"]]
        pooled_s = [v for t in ts for r in pts[(L, t)]["runs"] for v in r["s"]]
        e_lo, e_hi = min(pooled_e), max(pooled_e)
        s_lo, s_hi = min(pooled_s), max(pooled_s)
        _, e_w = bin_edges(e_lo, e_hi)
        _, s_w = bin_edges(s_lo, s_hi)
        res["L"][L] = {
            "e_lo": e_lo,
            "e_hi": e_hi,
            "e_w": e_w,
            "s_lo": s_lo,
            "s_hi": s_hi,
            "s_w": s_w,
        }
        for t in ts:
            p = pts[(L, t)]
            runs = p["runs"]
            T = p["T"]
            e_all = [v for r in runs for v in r["e"]]
            s_all = [v for r in runs for v in r["s"]]
            # per-seed raw and smoothed histograms (smoothing is linear: pooled smoothed = sum)
            h_seed = [histogram(r["e"], e_lo, e_w) for r in runs]
            h_raw = [sum(h[i] for h in h_seed) for i in range(NBINS)]
            hs = smooth3(h_raw)
            bar = barrier(hs)
            # jackknife: leave one seed out, fixed bins
            jk = []
            for k in range(3):
                hk = [h_raw[i] - h_seed[k][i] for i in range(NBINS)]
                jk.append(barrier(smooth3(hk))["dF"])
            sigma = jackknife_se(jk)
            # S histogram, same test, descriptive
            hs_s = smooth3(histogram(s_all, s_lo, s_w))
            bar_s = barrier(hs_s)
            # start dependence
            hot_e = [runs[0]["e"], runs[1]["e"]]
            cold_e = [runs[2]["e"]]
            hot_s = [runs[0]["s"], runs[1]["s"]]
            cold_s = [runs[2]["s"]]
            mh_e = mean(hot_e[0] + hot_e[1])
            mc_e = mean(cold_e[0])
            mh_s = mean(hot_s[0] + hot_s[1])
            mc_s = mean(cold_s[0])
            se_h_e = blocked_se(hot_e, BLOCK)
            se_c_e = blocked_se(cold_e, BLOCK)
            se_h_s = blocked_se(hot_s, BLOCK)
            se_c_s = blocked_se(cold_s, BLOCK)
            D_e = abs(mc_e - mh_e) / math.sqrt(se_c_e**2 + se_h_e**2)
            D_S = abs(mc_s - mh_s) / math.sqrt(se_c_s**2 + se_h_s**2)
            start_dep = max(D_e, D_S) > D_THRESH
            # per run
            runrows = []
            any_under = False
            for r in runs:
                tau, W = autocorr_tau_sokal(r["e"])
                n_eff = 5000.0 / (2.0 * tau)
                under = n_eff < NEFF_MIN
                any_under = any_under or under
                mse, msi = max_step(r["e"])
                mss, mssi = max_step(r["s"])
                row = {
                    "L": L,
                    "t": t,
                    "T": T,
                    "seed": r["seed"],
                    "start": r["start"],
                    "tau": tau,
                    "W": W,
                    "n_eff": n_eff,
                    "undersampled": under,
                    "mean_e": mean(r["e"]),
                    "mean_s": mean(r["s"]),
                    "se10": blocked_se([r["e"]], 10),
                    "se50": blocked_se([r["e"]], 50),
                    "se250": blocked_se([r["e"]], 250),
                    "se250_s": blocked_se([r["s"]], 250),
                    "max_step_e": (mse, msi),
                    "max_step_s": (mss, mssi),
                }
                runrows.append(row)
                res["runs"].append(row)
            # peak separation
            de = (bar["j"] - bar["i"]) * e_w if bar["resolved"] else 0.0
            # weights split at the valley bin (raw counts; valley bin half to each side)
            w_low = w_high = None
            if bar["resolved"]:
                vb = bar["valley_bin"]
                w_low = sum(h_raw[:vb]) + 0.5 * h_raw[vb]
                w_high = sum(h_raw[vb + 1 :]) + 0.5 * h_raw[vb]
            # phase locking: seeds whose whole e-series stays on one side of the valley bin centre
            lock = None
            if bar["resolved"]:
                vc = e_lo + (bar["valley_bin"] + 0.5) * e_w
                lock = 0
                for r in runs:
                    mn, mx = min(r["e"]), max(r["e"])
                    if mx < vc or mn > vc:
                        lock += 1
            res["points"][(L, t)] = {
                "L": L,
                "t": t,
                "T": T,
                "dF": bar["dF"],
                "sigma": sigma,
                "resolved": bar["resolved"],
                "bar": bar,
                "jk": jk,
                "V": binder(e_all),
                "D_e": D_e,
                "D_S": D_S,
                "start_dep": start_dep,
                "undersampled": any_under,
                "S_bimodal": bar_s["resolved"],
                "bar_s": bar_s,
                "h_raw": h_raw,
                "hs": hs,
                "h_seed": h_seed,
                "de": de,
                "w_low": w_low,
                "w_high": w_high,
                "lock": lock,
                "runs": runrows,
                "mean_hot_e": mh_e,
                "mean_cold_e": mc_e,
                "mean_hot_s": mh_s,
                "mean_cold_s": mc_s,
                "file": p["file"],
            }
    # primary per L
    prim = {}
    for L in L_LIST:
        ts = EXPECTED_T[L]
        best_t = None
        for t in ts:
            dF = res["points"][(L, t)]["dF"]
            if best_t is None or dF > res["points"][(L, best_t)]["dF"]:
                best_t = t  # strict > keeps the first T in ascending order on ties
        vmin_t = min(ts, key=lambda t: res["points"][(L, t)]["V"])
        prim[L] = {
            "dF_star": res["points"][(L, best_t)]["dF"],
            "t_star": best_t,
            "T_star": res["points"][(L, best_t)]["T"],
            "sigma_star": res["points"][(L, best_t)]["sigma"],
            "V_min": res["points"][(L, vmin_t)]["V"],
            "V_min_T": res["points"][(L, vmin_t)]["T"],
            "de_star": res["points"][(L, best_t)]["de"],
        }
    res["primary"] = prim

    # rule
    def eps(L1, L2):
        return max(
            EPS_FLOOR,
            2.0 * math.sqrt(prim[L1]["sigma_star"] ** 2 + prim[L2]["sigma_star"] ** 2),
        )

    e1612, e128 = eps(16, 12), eps(12, 8)
    a1 = prim[16]["dF_star"] >= DF0
    a2 = prim[16]["dF_star"] >= prim[12]["dF_star"] - e1612
    a3 = prim[12]["dF_star"] >= prim[8]["dF_star"] - e128
    a_clauses = a1 and a2 and a3
    a_gate_under = res["points"][(16, prim[16]["t_star"])]["undersampled"]
    a_fires = a_clauses and not a_gate_under
    big = [(L, t) for L in (12, 16) for t in EXPECTED_T[L]]
    b_all_zero = all(res["points"][k]["dF"] == 0.0 for k in big)
    b_gate_under = any(res["points"][k]["undersampled"] for k in big)
    b_gate_sdep = any(res["points"][k]["start_dep"] for k in big)
    sdep_no_pair = any(
        res["points"][k]["start_dep"] and not res["points"][k]["resolved"] for k in big
    )
    b_fires = b_all_zero and not b_gate_under and not b_gate_sdep
    if a_fires:
        outcome, rule, sub = "H-FO", "(a)", ""
    elif b_fires:
        outcome, rule, sub = "H-CONT", "(b)", ""
    else:
        outcome, rule = "inconclusive", "(c)"
        sampling_block = (a_clauses and a_gate_under) or (b_all_zero and b_gate_under)
        if sampling_block:
            sub = "(sampling)"
        elif (not a_fires) and sdep_no_pair:
            sub = "(metastability)"
        else:
            sub = ""
    res["rule"] = {
        "eps_16_12": e1612,
        "eps_12_8": e128,
        "a1": a1,
        "a2": a2,
        "a3": a3,
        "a_clauses": a_clauses,
        "a_gate_under": a_gate_under,
        "a_fires": a_fires,
        "b_all_zero": b_all_zero,
        "b_gate_under": b_gate_under,
        "b_gate_sdep": b_gate_sdep,
        "sdep_no_pair": sdep_no_pair,
        "b_fires": b_fires,
        "outcome": outcome,
        "rule": rule,
        "sub": sub,
    }
    # secondaries
    x12, x16 = 1.0 / 12**3, 1.0 / 16**3
    v12, v16 = prim[12]["V_min"], prim[16]["V_min"]
    v_star = v16 - (v12 - v16) * x16 / (x12 - x16)
    # coexistence at L=16: interpolated sign change of (w_low - w_high)/total between
    # consecutive resolved-bimodal grid points
    bim16 = [t for t in EXPECTED_T[16] if res["points"][(16, t)]["resolved"]]
    coex_T = None
    if len(bim16) >= 2:
        for a, b in zip(bim16[:-1], bim16[1:]):
            if b != a + 1:
                continue  # consecutive grid points only
            pa, pb = res["points"][(16, a)], res["points"][(16, b)]
            fa = (pa["w_low"] - pa["w_high"]) / (pa["w_low"] + pa["w_high"])
            fb = (pb["w_low"] - pb["w_high"]) / (pb["w_low"] + pb["w_high"])
            if fa == 0:
                coex_T = pa["T"]
                break
            if fa * fb < 0:
                coex_T = pa["T"] + (pb["T"] - pa["T"]) * fa / (fa - fb)
                break
    res["secondary"] = {
        "v_star": v_star,
        "n_bimodal_16": len(bim16),
        "coex_T": coex_T,
        "de_16": res["points"][(16, prim[16]["t_star"])]["de"],
        "lock_16": res["points"][(16, prim[16]["t_star"])]["lock"],
        "reported_16": prim[16]["dF_star"] > 0,
        "s_bimodal_count": sum(1 for p in res["points"].values() if p["S_bimodal"]),
    }
    return res


# ----------------------------------------------------------------------------
# report
# ----------------------------------------------------------------------------


def fmt_b(b):
    return "true" if b else "false"


def report(res, out_lines):
    P = out_lines.append
    P("# qbp-kz-g2 round 3 — independent recompute of the FROZEN-v1 §3 reading")
    P("")
    P(
        "Frozen rule sha256 `%s` (QBP PR #800 @ ae37319). Computed from the raw per-seed series only; no harness-derived or analyzer field used."
        % FROZEN_SHA
    )
    P(
        "bins: 60 per L over the pooled e; smoothing 3-bin (truncated edges); floor 3 sigma; dF0 = ln 2 = %.4f; eps floor %.2f; block %d; D > %g"
        % (DF0, EPS_FLOOR, BLOCK, D_THRESH)
    )
    P("")
    P("## Per-(L, T) table")
    P("")
    P(
        "| L | t | T | dF_L(T) | sigma_dF | resolved | peaks (bins) | h_lower | h_valley | depth/sigma | V_L(T) | D_e | D_S | start-dep | undersampled | S bimodal |"
    )
    P("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for L in L_LIST:
        for t in EXPECTED_T[L]:
            p = res["points"][(L, t)]
            b = p["bar"]
            peaks = (
                ("%d,%d (valley %d)" % (b["i"], b["j"], b["valley_bin"]))
                if p["resolved"]
                else "-"
            )
            P(
                "| %d | %d | %.2f | %.4f | %.4f | %s | %s | %.1f | %.1f | %.2f | %.6f | %.2f | %.2f | %s | %s | %s |"
                % (
                    L,
                    t,
                    p["T"],
                    p["dF"],
                    p["sigma"],
                    fmt_b(p["resolved"]),
                    peaks,
                    b["h_lower"],
                    b["h_valley"],
                    b["depth_sigma"],
                    p["V"],
                    p["D_e"],
                    p["D_S"],
                    fmt_b(p["start_dep"]),
                    fmt_b(p["undersampled"]),
                    fmt_b(p["S_bimodal"]),
                )
            )
    P("")
    P(
        "## Per-seed table (tau_int in RECORD units from the e record series; n_eff = 5000/(2 tau); undersampled iff n_eff < 20)"
    )
    P("")
    P(
        "| L | t | T | seed | start | <e> | SE250(e) | <S> | SE250(S) | tau_int_rec | W | n_eff | undersampled | max step e (rec k, 0-based) | max step S (rec k) |"
    )
    P("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in res["runs"]:
        P(
            "| %d | %d | %.2f | %d | %s | %.6f | %.2e | %.6f | %.2e | %.3f | %d | %.1f | %s | %.4f (%d) | %.4f (%d) |"
            % (
                r["L"],
                r["t"],
                r["T"],
                r["seed"],
                r["start"],
                r["mean_e"],
                r["se250"],
                r["mean_s"],
                r["se250_s"],
                r["tau"],
                r["W"],
                r["n_eff"],
                fmt_b(r["undersampled"]),
                r["max_step_e"][0],
                r["max_step_e"][1],
                r["max_step_s"][0],
                r["max_step_s"][1],
            )
        )
    P("")
    P("## Primary")
    P("")
    P(
        "| L | dF*(L) | T*(L) (t) | sigma*(L) | V_min(L) at T | bins [lo, hi] | de at T* |"
    )
    P("|---|---|---|---|---|---|---|")
    for L in L_LIST:
        q = res["primary"][L]
        bl = res["L"][L]
        P(
            "| %d | %.4f | %.2f (%d) | %.4f | %.6f at %.2f | [%.5f, %.5f] | %.4f |"
            % (
                L,
                q["dF_star"],
                q["T_star"],
                q["t_star"],
                q["sigma_star"],
                q["V_min"],
                q["V_min_T"],
                bl["e_lo"],
                bl["e_hi"],
                q["de_star"],
            )
        )
    P("")
    P(
        "Leave-one-seed-out dF at each L's T*(L): "
        + "; ".join(
            "L=%d %s"
            % (
                L,
                ", ".join(
                    "%.4f" % v
                    for v in res["points"][(L, res["primary"][L]["t_star"])]["jk"]
                ),
            )
            for L in L_LIST
        )
    )
    P("")
    R = res["rule"]
    pr = res["primary"]
    P("## Rule evaluation (precedence (a) -> (b) -> (c))")
    P("")
    P("- eps(16,12) = %.4f ; eps(12,8) = %.4f" % (R["eps_16_12"], R["eps_12_8"]))
    P(
        "- (a) dF*(16) = %.4f >= ln 2 = %.4f ? %s"
        % (pr[16]["dF_star"], DF0, fmt_b(R["a1"]))
    )
    P(
        "- (a) dF*(16) = %.4f >= dF*(12) - eps(16,12) = %.4f ? %s"
        % (pr[16]["dF_star"], pr[12]["dF_star"] - R["eps_16_12"], fmt_b(R["a2"]))
    )
    P(
        "- (a) dF*(12) = %.4f >= dF*(8) - eps(12,8) = %.4f ? %s"
        % (pr[12]["dF_star"], pr[8]["dF_star"] - R["eps_12_8"], fmt_b(R["a3"]))
    )
    P("- (a) clauses all true ? %s" % fmt_b(R["a_clauses"]))
    P(
        "- (a)-side gate: any undersampled run at (16, T*(16) = %.2f) ? %s"
        % (pr[16]["T_star"], fmt_b(R["a_gate_under"]))
    )
    P("- (a) fires ? %s" % fmt_b(R["a_fires"]))
    P("- (b) dF_16(T) = 0 and dF_12(T) = 0 at every T ? %s" % fmt_b(R["b_all_zero"]))
    P(
        "- (b)-side gate: undersampled run at any (L in {12,16}, T) ? %s"
        % fmt_b(R["b_gate_under"])
    )
    P(
        "- (b)-side gate: start-dependent point at any (L in {12,16}, T) ? %s (start-dependent without a resolved pair: %s)"
        % (fmt_b(R["b_gate_sdep"]), fmt_b(R["sdep_no_pair"]))
    )
    P("- (b) fires ? %s" % fmt_b(R["b_fires"]))
    P("")
    P(
        "**OUTCOME: %s by rule %s%s**"
        % (R["outcome"], R["rule"], (" " + R["sub"]) if R["sub"] else "")
    )
    P("")
    S = res["secondary"]
    P("## Secondaries (non-gating)")
    P("")
    P(
        "- V_min: L=8 %.6f, L=12 %.6f, L=16 %.6f; two-point 1/L^3 extrapolation V* = %.6f (2/3 = %.6f)"
        % (pr[8]["V_min"], pr[12]["V_min"], pr[16]["V_min"], S["v_star"], 2.0 / 3.0)
    )
    if S["reported_16"]:
        P(
            "- at (16, T*(16) = %.2f): de (peak separation) = %.4f; phase-locking count = %s of 3 seeds"
            % (pr[16]["T_star"], S["de_16"], S["lock_16"])
        )
    else:
        P(
            "- every dF_16(T) = 0: the (16, T*(16)) secondaries are not reported (T*(16) by tiebreak only)"
        )
    P(
        "- de trend at each L's own T*: L=8 %.4f, L=12 %.4f, L=16 %.4f (0 = no resolved pair there)"
        % (pr[8]["de_star"], pr[12]["de_star"], pr[16]["de_star"])
    )
    if S["coex_T"] is not None:
        P(
            "- equal-weight coexistence T at L = 16: %.4f (interpolated; %d bimodal grid points)"
            % (S["coex_T"], S["n_bimodal_16"])
        )
    else:
        P(
            "- no coexistence T readable at L = 16 (%d bimodal grid point(s); needs >= 2 with an equal-weight crossing)"
            % S["n_bimodal_16"]
        )
    P(
        "- weights at the L=16 resolved points (w_low - w_high)/total: "
        + ", ".join(
            "T=%.2f %+.3f"
            % (
                res["points"][(16, t)]["T"],
                (res["points"][(16, t)]["w_low"] - res["points"][(16, t)]["w_high"])
                / 15000.0,
            )
            for t in EXPECTED_T[16]
            if res["points"][(16, t)]["resolved"]
        )
    )
    P(
        "- S histograms: %d of 27 points resolved-bimodal (descriptive only)"
        % S["s_bimodal_count"]
    )
    P("")


# ----------------------------------------------------------------------------
# comparison against the frozen analyzer's text output (parsed only for the diff)
# ----------------------------------------------------------------------------


def parse_analyzer(path):
    A = {"points": {}, "runs": {}, "primary": {}, "rule": {}}
    with open(path) as fh:
        lines = fh.read().splitlines()
    section = None
    for ln in lines:
        s = ln.strip()
        if s.startswith("| L | t | T | dF_L(T)"):
            section = "points"
            continue
        if s.startswith("| L | t | seed |"):
            section = "runs"
            continue
        if s.startswith("| L | dF*(L) |"):
            section = "primary"
            continue
        if s.startswith("|---"):
            continue
        if s.startswith("|") and section:
            cells = [c.strip() for c in s.strip("|").split("|")]
            if section == "points":
                L, t = int(cells[0]), int(cells[1])
                A["points"][(L, t)] = {
                    "T": float(cells[2]),
                    "dF": float(cells[3]),
                    "sigma": float(cells[4]),
                    "resolved": cells[5] == "true",
                    "peaks": cells[6],
                    "h_lower": float(cells[7]),
                    "h_valley": float(cells[8]),
                    "depth_sigma": float(cells[9]),
                    "V": float(cells[10]),
                    "D_e": float(cells[11]),
                    "D_S": float(cells[12]),
                    "start_dep": cells[13] == "true",
                    "undersampled": cells[14] == "true",
                    "S_bimodal": cells[15] == "true",
                }
            elif section == "runs":
                seed = int(cells[2])
                A["runs"][seed] = {
                    "tau": float(cells[4]),
                    "W": int(cells[5]),
                    "n_eff": float(cells[6]),
                    "undersampled": cells[7] == "true",
                    "mean_e": float(cells[9]),
                    "se10": float(cells[10]),
                    "se50": float(cells[11]),
                    "se250": float(cells[12]),
                    "mean_s": float(cells[13]),
                    "max_step_e": cells[14],
                    "max_step_s": cells[15],
                }
            elif section == "primary":
                L = int(cells[0])
                m = re.match(r"([\d.]+) \((\d+)\)", cells[2])
                mv = re.match(r"([\d.]+) at ([\d.]+)", cells[4])
                A["primary"][L] = {
                    "dF_star": float(cells[1]),
                    "T_star": float(m.group(1)),
                    "t_star": int(m.group(2)),
                    "sigma_star": float(cells[3]),
                    "V_min": float(mv.group(1)),
                    "V_min_T": float(mv.group(2)),
                    "de_star": float(cells[6]),
                }
        else:
            if (
                s.startswith("|") is False
                and section in ("points", "runs", "primary")
                and s == ""
            ):
                section = None
        m = re.search(r"eps\(16,12\) = ([\d.]+)\s+eps\(12,8\) = ([\d.]+)", s)
        if m:
            A["rule"]["eps_16_12"], A["rule"]["eps_12_8"] = float(m.group(1)), float(
                m.group(2)
            )
        m = re.match(r"OUTCOME: (.*)$", s)
        if m:
            A["rule"]["outcome_line"] = m.group(1)
        m = re.search(r"extrapolation V\* = ([\d.]+)", s)
        if m:
            A["rule"]["v_star"] = float(m.group(1))
        m = re.search(
            r"de \(peak separation\) = ([\d.]+); phase-locking count = (\d+) of 3", s
        )
        if m:
            A["rule"]["de_16"], A["rule"]["lock_16"] = float(m.group(1)), int(
                m.group(2)
            )
        m = re.search(r"S histograms: (\d+) of 27", s)
        if m:
            A["rule"]["s_bimodal_count"] = int(m.group(1))
        if "no coexistence T readable" in s:
            A["rule"]["coex_T"] = None
    return A


def compare(res, A, out_lines):
    P = out_lines.append
    P("## Recompute vs frozen analyzer (analyzer text parsed for this table only)")
    P("")
    P(
        "Differences are |recompute - analyzer| on the analyzer's printed precision; a flag mismatch prints MISMATCH."
    )
    P("")
    P(
        "| L | t | T | d dF | d sigma_dF | d V_L | d D_e | d D_S | d h_lower | d h_valley | peaks | resolved | start-dep | undersampled | S bimodal | d tau (3 seeds) | d <e> (3 seeds) |"
    )
    P("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    mx = {
        "dF": 0.0,
        "sigma": 0.0,
        "V": 0.0,
        "D_e": 0.0,
        "D_S": 0.0,
        "h_lower": 0.0,
        "h_valley": 0.0,
        "tau": 0.0,
        "mean_e": 0.0,
        "mean_s": 0.0,
        "n_eff": 0.0,
        "se250": 0.0,
        "depth_sigma": 0.0,
    }
    flag_mismatch = []
    for L in L_LIST:
        for t in EXPECTED_T[L]:
            p = res["points"][(L, t)]
            a = A["points"].get((L, t))
            if a is None:
                P("| %d | %d | %.2f | analyzer row missing |" % (L, t, p["T"]))
                flag_mismatch.append(("row", L, t))
                continue
            b = p["bar"]
            d = {
                "dF": abs(p["dF"] - a["dF"]),
                "sigma": abs(p["sigma"] - a["sigma"]),
                "V": abs(p["V"] - a["V"]),
                "D_e": abs(p["D_e"] - a["D_e"]),
                "D_S": abs(p["D_S"] - a["D_S"]),
                "h_lower": abs(b["h_lower"] - a["h_lower"]),
                "h_valley": abs(b["h_valley"] - a["h_valley"]),
                "depth_sigma": abs(b["depth_sigma"] - a["depth_sigma"]),
            }
            for k in d:
                mx[k] = max(mx[k], d[k])
            peaks = (
                ("%d,%d (valley %d)" % (b["i"], b["j"], b["valley_bin"]))
                if p["resolved"]
                else "-"
            )
            pk_ok = peaks == a["peaks"]
            flags = []
            for name, mine, theirs in (
                ("resolved", p["resolved"], a["resolved"]),
                ("start_dep", p["start_dep"], a["start_dep"]),
                ("undersampled", p["undersampled"], a["undersampled"]),
                ("S_bimodal", p["S_bimodal"], a["S_bimodal"]),
            ):
                ok = mine == theirs
                flags.append("ok" if ok else "MISMATCH")
                if not ok:
                    flag_mismatch.append((name, L, t))
            if not pk_ok:
                flag_mismatch.append(("peaks", L, t))
            dtau = []
            dme = []
            for r in p["runs"]:
                ar = A["runs"].get(r["seed"])
                if ar is None:
                    dtau.append(float("nan"))
                    dme.append(float("nan"))
                    flag_mismatch.append(("run-row", L, t, r["seed"]))
                    continue
                dtau.append(abs(r["tau"] - ar["tau"]))
                dme.append(abs(r["mean_e"] - ar["mean_e"]))
                mx["tau"] = max(mx["tau"], abs(r["tau"] - ar["tau"]))
                mx["mean_e"] = max(mx["mean_e"], abs(r["mean_e"] - ar["mean_e"]))
                mx["mean_s"] = max(mx["mean_s"], abs(r["mean_s"] - ar["mean_s"]))
                mx["n_eff"] = max(mx["n_eff"], abs(r["n_eff"] - ar["n_eff"]))
                mx["se250"] = max(
                    mx["se250"], abs(r["se250"] - ar["se250"]) / ar["se250"]
                )
                if r["undersampled"] != ar["undersampled"]:
                    flag_mismatch.append(("run-undersampled", L, t, r["seed"]))
                if r["W"] != ar["W"]:
                    flag_mismatch.append(("sokal-W", L, t, r["seed"], r["W"], ar["W"]))
                if ("%.4f (%d)" % r["max_step_e"]) != ar["max_step_e"]:
                    flag_mismatch.append(
                        (
                            "max-step-e",
                            L,
                            t,
                            r["seed"],
                            "%.4f (%d)" % r["max_step_e"],
                            ar["max_step_e"],
                        )
                    )
                if ("%.4f (%d)" % r["max_step_s"]) != ar["max_step_s"]:
                    flag_mismatch.append(
                        (
                            "max-step-S",
                            L,
                            t,
                            r["seed"],
                            "%.4f (%d)" % r["max_step_s"],
                            ar["max_step_s"],
                        )
                    )
            P(
                "| %d | %d | %.2f | %.1e | %.1e | %.1e | %.2f | %.2f | %.1f | %.1f | %s | %s | %s | %s | %s | %s | %s |"
                % (
                    L,
                    t,
                    p["T"],
                    d["dF"],
                    d["sigma"],
                    d["V"],
                    d["D_e"],
                    d["D_S"],
                    d["h_lower"],
                    d["h_valley"],
                    "ok" if pk_ok else "MISMATCH %s vs %s" % (peaks, a["peaks"]),
                    flags[0],
                    flags[1],
                    flags[2],
                    flags[3],
                    "/".join("%.3f" % x for x in dtau),
                    "/".join("%.1e" % x for x in dme),
                )
            )
    P("")
    P("Primary / rule comparison:")
    P("")
    P("| quantity | recompute | analyzer | abs diff |")
    P("|---|---|---|---|")
    for L in L_LIST:
        q, a = res["primary"][L], A["primary"].get(L, {})
        for key, fmt in (
            ("dF_star", "%.4f"),
            ("T_star", "%.2f"),
            ("sigma_star", "%.4f"),
            ("V_min", "%.6f"),
            ("de_star", "%.4f"),
        ):
            if key in a:
                P(
                    "| %s(L=%d) | %s | %s | %.1e |"
                    % (key, L, fmt % q[key], fmt % a[key], abs(q[key] - a[key]))
                )
    R, S = res["rule"], res["secondary"]
    for key, mine, fmt in (
        ("eps_16_12", R["eps_16_12"], "%.4f"),
        ("eps_12_8", R["eps_12_8"], "%.4f"),
        ("v_star", S["v_star"], "%.6f"),
        ("de_16", S["de_16"], "%.4f"),
    ):
        if key in A["rule"]:
            P(
                "| %s | %s | %s | %.1e |"
                % (key, fmt % mine, fmt % A["rule"][key], abs(mine - A["rule"][key]))
            )
    if "lock_16" in A["rule"]:
        P(
            "| phase-lock count (16,T*) | %s | %d | %s |"
            % (
                S["lock_16"],
                A["rule"]["lock_16"],
                "ok" if S["lock_16"] == A["rule"]["lock_16"] else "MISMATCH",
            )
        )
    if "s_bimodal_count" in A["rule"]:
        P(
            "| S-bimodal count | %d | %d | %s |"
            % (
                S["s_bimodal_count"],
                A["rule"]["s_bimodal_count"],
                (
                    "ok"
                    if S["s_bimodal_count"] == A["rule"]["s_bimodal_count"]
                    else "MISMATCH"
                ),
            )
        )
    if "coex_T" in A["rule"]:
        P(
            "| coexistence T (16) | %s | %s | %s |"
            % (
                S["coex_T"],
                A["rule"]["coex_T"],
                "ok" if S["coex_T"] == A["rule"]["coex_T"] else "MISMATCH",
            )
        )
    mine_out = "%s by rule %s%s" % (
        R["outcome"],
        R["rule"],
        (" " + R["sub"]) if R["sub"] else "",
    )
    P(
        "| OUTCOME | %s | %s | %s |"
        % (
            mine_out.strip(),
            A["rule"].get("outcome_line", "?"),
            (
                "ok"
                if mine_out.strip() == A["rule"].get("outcome_line", "").strip()
                else "CHECK"
            ),
        )
    )
    P("")
    P(
        "Max absolute differences over all 27 points / 81 runs: dF %.2e, sigma_dF %.2e, V_L %.2e, D_e %.2e, D_S %.2e, h_lower %.2e, h_valley %.2e, depth/sigma %.2e, tau_int %.2e, n_eff %.2e, <e> %.2e, <S> %.2e, SE250 (relative) %.2e"
        % (
            mx["dF"],
            mx["sigma"],
            mx["V"],
            mx["D_e"],
            mx["D_S"],
            mx["h_lower"],
            mx["h_valley"],
            mx["depth_sigma"],
            mx["tau"],
            mx["n_eff"],
            mx["mean_e"],
            mx["mean_s"],
            mx["se250"],
        )
    )
    tol_ok = (
        mx["dF"] <= 5.1e-5
        and mx["sigma"] <= 5.1e-5
        and mx["V"] <= 5.1e-7
        and mx["D_e"] <= 5.1e-3
        and mx["D_S"] <= 5.1e-3
        and mx["h_lower"] <= 0.051
        and mx["h_valley"] <= 0.051
        and mx["tau"] <= 5.1e-4
        and mx["mean_e"] <= 5.1e-7
        and mx["n_eff"] <= 0.051
    )
    if flag_mismatch:
        P("")
        P("Flag / integer mismatches: %s" % "; ".join(str(x) for x in flag_mismatch))
    else:
        P("")
        P("No flag, peak-index, Sokal-W, max-step or outcome mismatch.")
    P("")
    P(
        "Agreement to the analyzer's printed precision: **%s**"
        % ("YES" if (tol_ok and not flag_mismatch) else "NO — see above")
    )
    P("")
    return tol_ok and not flag_mismatch


# ----------------------------------------------------------------------------
# plots (Human Visual Review)
# ----------------------------------------------------------------------------

HOT1, HOT2, COLD = "#2a78d6", "#7fb0ec", "#e34948"
GRID = "#d9d8d3"
INK = "#0b0b0b"
INK2 = "#52514e"


def style_ax(ax):
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)
    ax.spines["left"].set_color(INK2)
    ax.spines["bottom"].set_color(INK2)
    ax.grid(True, color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    ax.tick_params(colors=INK2, labelsize=9)


def plots(res, pts, out_dir):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch

    plt.rcParams.update(
        {
            "font.size": 10,
            "axes.titlesize": 11,
            "axes.labelsize": 10,
            "text.color": INK,
            "axes.labelcolor": INK2,
            "figure.facecolor": "white",
        }
    )
    sha = FROZEN_SHORT

    def per_seed_series(key, ylabel, fname, title):
        fig, axes = plt.subplots(3, 1, figsize=(9, 10), sharex=True)
        for ax, L in zip(axes, L_LIST):
            style_ax(ax)
            for t in EXPECTED_T[L]:
                p = res["points"][(L, t)]
                if p["start_dep"]:
                    ax.axvspan(
                        p["T"] - 0.0045,
                        p["T"] + 0.0045,
                        color="#f5e6c8",
                        zorder=0,
                        lw=0,
                    )
                for k, r in enumerate(p["runs"]):
                    y = r["mean_e"] if key == "e" else r["mean_s"]
                    se = r["se250"] if key == "e" else r["se250_s"]
                    if r["start"] == "haar":
                        ax.errorbar(
                            p["T"] + (-0.0012 if k == 0 else 0.0012),
                            y,
                            yerr=3 * se,
                            fmt="o",
                            ms=6,
                            color=HOT1 if k == 0 else HOT2,
                            mec="white",
                            mew=0.8,
                            ecolor=INK2,
                            elinewidth=1,
                            capsize=2,
                            zorder=3,
                        )
                    else:
                        ax.errorbar(
                            p["T"],
                            y,
                            yerr=3 * se,
                            fmt="s",
                            ms=6,
                            color=COLD,
                            mec="white",
                            mew=0.8,
                            ecolor=INK2,
                            elinewidth=1,
                            capsize=2,
                            zorder=4,
                        )
            ax.set_ylabel(ylabel)
            ax.set_title("L = %d" % L, loc="left")
            ax.set_xticks(T_GRID)
        axes[-1].set_xlabel(
            "T (J)   — grid points; shaded = start-dependent (max(D_e, D_S) > 3)"
        )
        handles = [
            Line2D(
                [],
                [],
                marker="o",
                color=HOT1,
                ls="",
                ms=6,
                label="hot seed j=0 (Haar start)",
            ),
            Line2D(
                [],
                [],
                marker="o",
                color=HOT2,
                ls="",
                ms=6,
                label="hot seed j=1 (Haar start)",
            ),
            Line2D(
                [],
                [],
                marker="s",
                color=COLD,
                ls="",
                ms=6,
                label="cold seed j=2 (aligned start)",
            ),
            Patch(facecolor="#f5e6c8", label="start-dependent point"),
        ]
        axes[0].legend(handles=handles, loc="best", frameon=False, fontsize=9)
        fig.suptitle(
            "%s\nerror bars = 3 × blocked SE (250 records); frozen rule %s"
            % (title, sha),
            fontsize=12,
        )
        fig.tight_layout(rect=(0, 0, 1, 0.96))
        fig.savefig(os.path.join(out_dir, fname), dpi=110)
        plt.close(fig)

    per_seed_series(
        "e",
        "⟨e⟩ per seed",
        "kz-g2-r3-eseries-hot-cold.png",
        "qbp-kz-g2 r3: per-seed ⟨e⟩ vs T, hot vs cold start",
    )
    per_seed_series(
        "s",
        "⟨S⟩ per seed",
        "kz-g2-r3-S-vs-T.png",
        "qbp-kz-g2 r3: per-seed ⟨S⟩ vs T, hot vs cold start",
    )

    # (ii) histogram panels at T = 1.14 (t=4) and 1.16 (t=6)
    fig, axes = plt.subplots(2, 3, figsize=(13, 7.5))
    for row, t in enumerate((4, 6)):
        for col, L in enumerate(L_LIST):
            ax = axes[row][col]
            style_ax(ax)
            p = res["points"][(L, t)]
            bl = res["L"][L]
            centres = [bl["e_lo"] + (i + 0.5) * bl["e_w"] for i in range(NBINS)]
            hot = smooth3([p["h_seed"][0][i] + p["h_seed"][1][i] for i in range(NBINS)])
            cold = smooth3(p["h_seed"][2])
            w = bl["e_w"] * 0.92
            ax.bar(
                centres,
                hot,
                width=w,
                color=HOT1,
                label="hot seeds (j=0,1), smoothed",
                lw=0,
            )
            ax.bar(
                centres,
                cold,
                width=w,
                bottom=hot,
                color=COLD,
                label="cold seed (j=2), smoothed",
                lw=0,
            )
            if p["resolved"]:
                b = p["bar"]
                vc = centres[b["valley_bin"]]
                ax.axvline(vc, color=INK, lw=1, ls="--")
                ax.annotate(
                    "valley bin %d\nΔF = %.2f (σ %.2f)"
                    % (b["valley_bin"], p["dF"], p["sigma"]),
                    xy=(vc, max(hot[i] + cold[i] for i in range(NBINS)) * 0.95),
                    ha="center",
                    va="top",
                    fontsize=9,
                    bbox=dict(boxstyle="round,pad=0.3", fc="white", ec=GRID),
                )
            else:
                ax.text(
                    0.97,
                    0.92,
                    "no resolved pair — ΔF = 0",
                    transform=ax.transAxes,
                    ha="right",
                    fontsize=9,
                    bbox=dict(boxstyle="round,pad=0.3", fc="white", ec=GRID),
                )
            ax.set_title(
                "L = %d, T = %.2f%s"
                % (L, p["T"], "  (start-dep)" if p["start_dep"] else ""),
                loc="left",
            )
            ax.set_xlabel("e (chordal energy per bond)")
            if col == 0:
                ax.set_ylabel("smoothed count (3-bin MA, 15,000 samples)")
    h, lab = axes[0][0].get_legend_handles_labels()
    fig.legend(
        h,
        lab,
        loc="upper center",
        bbox_to_anchor=(0.5, 0.955),
        ncol=2,
        frameon=False,
        fontsize=9,
    )
    fig.suptitle(
        "qbp-kz-g2 r3: pooled e histograms, hot and cold contributions stacked   [frozen %s]"
        % sha,
        fontsize=12,
    )
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    fig.savefig(os.path.join(out_dir, "kz-g2-r3-hist-panels.png"), dpi=110)
    plt.close(fig)

    # (iii) V_L(T)
    fig, ax = plt.subplots(figsize=(8.5, 5))
    style_ax(ax)
    cols = {8: "#1baf7a", 12: "#4a3aa7", 16: "#eb6834"}
    for L in L_LIST:
        xs = [res["points"][(L, t)]["T"] for t in EXPECTED_T[L]]
        ys = [res["points"][(L, t)]["V"] for t in EXPECTED_T[L]]
        ax.plot(
            xs,
            ys,
            "-o",
            color=cols[L],
            lw=2,
            ms=6,
            mec="white",
            mew=0.8,
            label="L = %d" % L,
        )
        q = res["primary"][L]
        off = {8: (8, 4), 12: (8, -4), 16: (-8, -14)}[L]
        ax.annotate(
            "V_min(%d) = %.4f" % (L, q["V_min"]),
            xy=(q["V_min_T"], q["V_min"]),
            xytext=off,
            textcoords="offset points",
            fontsize=9,
            color=INK2,
            ha="right" if L == 16 else "left",
        )
    ax.axhline(2.0 / 3.0, color=INK2, lw=1, ls="--")
    ax.text(
        T_GRID[0], 2.0 / 3.0, " 2/3 (Gaussian)", va="bottom", fontsize=9, color=INK2
    )
    ax.set_xticks(T_GRID)
    ax.set_xlabel("T (J)")
    ax.set_ylabel("V_L(T) = 1 − ⟨e⁴⟩ / (3⟨e²⟩²)")
    ax.legend(frameon=False)
    ax.set_title(
        "qbp-kz-g2 r3: Binder cumulant of e (secondary, non-gating); V* = %.4f   [frozen %s]"
        % (res["secondary"]["v_star"], sha),
        loc="left",
    )
    fig.tight_layout()
    fig.savefig(os.path.join(out_dir, "kz-g2-r3-VL.png"), dpi=110)
    plt.close(fig)

    # (v) traces at (16, 1.14) and (8, 1.16)
    fig, axes = plt.subplots(2, 1, figsize=(13, 7.5))
    for ax, (L, t) in zip(axes, ((16, 4), (8, 6))):
        style_ax(ax)
        p = res["points"][(L, t)]
        bl = res["L"][L]
        idx = list(range(1, 5001))
        handles = []
        for k, r in enumerate(pts[(L, t)]["runs"]):
            c = (HOT1, HOT2, COLD)[k]
            ax.plot(idx, r["e"], color=c, lw=0.6)
            handles.append(
                Line2D(
                    [],
                    [],
                    color=c,
                    lw=2,
                    label="seed %d (%s start)" % (r["seed"], r["start"]),
                )
            )
        if p["resolved"]:
            vc = bl["e_lo"] + (p["bar"]["valley_bin"] + 0.5) * bl["e_w"]
            ax.axhline(vc, color=INK, lw=1, ls="--")
            ax.text(
                4950,
                vc,
                "valley bin centre e = %.3f" % vc,
                va="bottom",
                ha="right",
                fontsize=9,
            )
        ax.set_title(
            "L = %d, T = %.2f — ΔF = %.2f, phase-locking %s of 3 seeds"
            % (L, p["T"], p["dF"], p["lock"]),
            loc="left",
        )
        ax.set_ylabel("e")
        ax.legend(
            handles=handles,
            frameon=False,
            fontsize=9,
            loc="center left",
            bbox_to_anchor=(1.005, 0.5),
        )
    axes[-1].set_xlabel(
        "record index (one record per 10 sampling steps; 5,000 records = 50,000 steps)"
    )
    fig.suptitle(
        "qbp-kz-g2 r3: per-seed e traces — phase locking (L=16) vs tunnelling (L=8)   [frozen %s]"
        % sha,
        fontsize=12,
    )
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    fig.savefig(os.path.join(out_dir, "kz-g2-r3-traces-L16-T114.png"), dpi=110)
    plt.close(fig)


# ----------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--plots", action="store_true")
    ap.add_argument(
        "--analyzer",
        default=None,
        help="path to the frozen analyzer's analyze-eq.out (default: <out>/../analysis/analyze-eq.out)",
    )
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    pts = load_raw(args.raw)
    res = analyse(pts)
    lines = []
    report(res, lines)
    apath = args.analyzer or os.path.join(args.out, "..", "analysis", "analyze-eq.out")
    agree = None
    if os.path.exists(apath):
        A = parse_analyzer(apath)
        agree = compare(res, A, lines)
    else:
        lines.append("(analyzer output not found at %s; no comparison)" % apath)
    if args.plots:
        plots(res, pts, args.out)
        lines.append(
            "Plots written: kz-g2-r3-eseries-hot-cold.png, kz-g2-r3-hist-panels.png, kz-g2-r3-VL.png, kz-g2-r3-S-vs-T.png, kz-g2-r3-traces-L16-T114.png (dpi 110)"
        )
    text = "\n".join(lines) + "\n"
    sys.stdout.write(text)
    with open(os.path.join(args.out, "recompute-tables.md"), "w") as fh:
        fh.write(text)
    return 0 if agree in (None, True) else 2


if __name__ == "__main__":
    sys.exit(main())
