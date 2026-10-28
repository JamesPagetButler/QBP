"""Fit driver for the qbp-desi-fit round-1 spike. Writes ONE raw JSON; no analysis here.

Usage: python3 fit.py --out raw/qbp-desi-fit-r1-raw-2026-10-27.json [--quick]
Models and priors exactly as in spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md section 3:
  shared  Om flat [0.1, 0.6]; h flat [0.5, 0.9]; omega_b Planck compressed prior (flat box
          [0.015, 0.030] only to bound the minimiser); r_d from (omega_b, omega_m); M marginalised.
  A       QBP, z_t = 0.70 fixed                 (k = 3, same as LCDM)
  B       QBP, z_t free, flat [0.1, 2.0]        (k = 4)
  LCDM                                          (k = 3)
  CPL     w0 flat [-3, 1], wa flat [-3, 2]      (k = 5)
"""

import argparse
import hashlib
import json
import os
import resource
import subprocess
import sys
import time

import numpy as np
from scipy.optimize import minimize
from scipy.stats import qmc

import cosmo
from likelihoods import BAO, Pantheon, PlanckCompressed

HERE = os.path.dirname(os.path.abspath(__file__))
PAUSE_FILE = os.path.expanduser("~/.federation-watcher/box-pause/qbp-desi")

SHARED = {"Om": (0.1, 0.6), "h": (0.5, 0.9), "ob": (0.015, 0.030)}
MODELS = {
    "A": {"de": "QBP", "free": {}, "fixed": {"zt": cosmo.ZT_RECORD}},
    "B": {"de": "QBP", "free": {"zt": (0.1, 2.0)}, "fixed": {}},
    "LCDM": {"de": "LCDM", "free": {}, "fixed": {}},
    "CPL": {"de": "CPL", "free": {"w0": (-3.0, 1.0), "wa": (-3.0, 2.0)}, "fixed": {}},
    # robustness line (frozen section 3): not an arm
    "A_zt0.718": {"de": "QBP", "free": {}, "fixed": {"zt": cosmo.ZT_ROBUST}},
    # diagnostics, NOT pre-registered (see results doc, deviations): the density whose w(z)
    # equals the frozen section-1 w_eff formula literally.
    "DIAG_mirror_zt0.70": {
        "de": "QBP_MIRROR",
        "free": {},
        "fixed": {"zt": cosmo.ZT_RECORD},
    },
    "DIAG_mirror_ztfree": {"de": "QBP_MIRROR", "free": {"zt": (0.1, 2.0)}, "fixed": {}},
}
ARMS = ["A", "B", "LCDM", "CPL"]


def n_params(model):
    return len(SHARED) + len(MODELS[model]["free"])


def param_spec(model, extra_fixed=None):
    names = list(SHARED) + list(MODELS[model]["free"])
    bounds = [SHARED[n] for n in SHARED] + [
        MODELS[model]["free"][n] for n in MODELS[model]["free"]
    ]
    fixed = dict(MODELS[model]["fixed"])
    if extra_fixed:
        for k, v in extra_fixed.items():
            if k in names:
                i = names.index(k)
                names.pop(i)
                bounds.pop(i)
            fixed[k] = v
    return names, bounds, fixed


class Likelihood:
    def __init__(self, data_dir=None):
        kw = {"data_dir": data_dir} if data_dir else {}
        self.bao = BAO(**kw)
        self.sne = Pantheon(**kw)
        self.cmb = PlanckCompressed(**kw)
        self.N = self.bao.n + self.sne.n + self.cmb.n
        self.nevals = 0

    def parts(self, model, p):
        bg = cosmo.Background(MODELS[model]["de"], p)
        return {
            "bao": self.bao.chi2(bg),
            "sne": self.sne.chi2(bg),
            "planck": self.cmb.chi2(bg),
        }

    def chi2(self, model, p):
        self.nevals += 1
        c = self.parts(model, p)
        return c["bao"] + c["sne"] + c["planck"]


def check_pause():
    if os.path.exists(PAUSE_FILE):
        print(f"PAUSE FILE PRESENT ({PAUSE_FILE}) — aborting", file=sys.stderr)
        sys.exit(3)


def fit_model(lk, model, n_starts=12, seed=775, extra_fixed=None):
    """Bounded multi-start minimisation (L-BFGS-B from Sobol starts, Nelder-Mead polish)."""
    names, bounds, fixed = param_spec(model, extra_fixed)
    lo = np.array([b[0] for b in bounds])
    hi = np.array([b[1] for b in bounds])

    def unpack(x):
        p = dict(fixed)
        p.update(zip(names, x))
        return p

    def obj(x):
        x = np.clip(x, lo, hi)
        try:
            v = lk.chi2(model, unpack(x))
        except (FloatingPointError, ValueError):
            return 1e30
        return v if np.isfinite(v) else 1e30

    # starts: Planck-like anchor + Sobol points inside the box
    anchor = {"Om": 0.31, "h": 0.68, "ob": 0.0224, "zt": 0.7, "w0": -1.0, "wa": 0.0}
    starts = [np.array([anchor[n] for n in names])]
    sob = qmc.Sobol(d=len(names), scramble=True, seed=seed).random(max(n_starts - 1, 1))
    starts += list(lo + sob * (hi - lo))
    best = None
    for x0 in starts:
        r = minimize(
            obj,
            x0,
            method="L-BFGS-B",
            bounds=list(zip(lo, hi)),
            options={"maxiter": 500},
        )
        if best is None or r.fun < best.fun:
            best = r
    r2 = minimize(
        obj,
        best.x,
        method="Nelder-Mead",
        options={"xatol": 1e-7, "fatol": 1e-7, "maxiter": 4000},
    )
    if r2.fun < best.fun:
        best = r2
    x = np.clip(best.x, lo, hi)
    p = unpack(x)
    parts = lk.parts(model, p)
    at_bound = {
        n: bool(abs(x[i] - lo[i]) < 1e-6 or abs(x[i] - hi[i]) < 1e-6)
        for i, n in enumerate(names)
    }
    return {
        "model": model,
        "de": MODELS[model]["de"],
        "params": {k: float(v) for k, v in p.items()},
        "free_params": names,
        "k": len(names),
        "at_bound": at_bound,
        "chi2": float(sum(parts.values())),
        "chi2_parts": {k: float(v) for k, v in parts.items()},
        "H0": 100.0 * float(p["h"]),
        "n_starts": len(starts),
    }


def profile_h(lk, model, fit, half_width=0.025, n=7):
    """1-sigma on h from a parabola through the profile chi2(h) (others minimised)."""
    h0 = fit["params"]["h"]
    hs = np.linspace(h0 - half_width, h0 + half_width, n)
    c = []
    for hv in hs:
        c.append(fit_model(lk, model, n_starts=3, extra_fixed={"h": hv})["chi2"])
    a, b, cc = np.polyfit(hs, c, 2)
    sigma_h = float(1.0 / np.sqrt(a)) if a > 0 else float("nan")
    return {
        "h_grid": hs.tolist(),
        "chi2_grid": [float(v) for v in c],
        "sigma_h": sigma_h,
        "sigma_H0": 100.0 * sigma_h,
    }


def profile_zt(lk, grid):
    out = []
    for zt in grid:
        check_pause()
        r = fit_model(lk, "B", n_starts=4, extra_fixed={"zt": float(zt)})
        out.append(
            {"zt": float(zt), "chi2": r["chi2"], "H0": r["H0"], "Om": r["params"]["Om"]}
        )
    return out


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def git(*args):
    return subprocess.run(
        ["git", "-C", HERE] + list(args), capture_output=True, text=True
    ).stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument(
        "--quick", action="store_true", help="coarse grids (smoke test only)"
    )
    args = ap.parse_args()
    np.seterr(all="raise", under="ignore")

    t0 = time.time()
    check_pause()
    lk = Likelihood()
    N = lk.N
    print(
        f"data: BAO n={lk.bao.n}, SNe n={lk.sne.n}, Planck n={lk.cmb.n}, N={N}",
        flush=True,
    )

    results = {}
    for m in ARMS + ["A_zt0.718", "DIAG_mirror_zt0.70", "DIAG_mirror_ztfree"]:
        check_pause()
        ts = time.time()
        r = fit_model(lk, m, n_starts=4 if args.quick else 12)
        r["AIC"] = r["chi2"] + 2 * r["k"]
        r["BIC"] = r["chi2"] + r["k"] * np.log(N)
        r["fit_seconds"] = time.time() - ts
        results[m] = r
        print(
            f"{m:>20s}: chi2={r['chi2']:.3f} {r['chi2_parts']} k={r['k']} H0={r['H0']:.3f} ({r['fit_seconds']:.1f}s)",
            flush=True,
        )

    check_pause()
    for m in ["A", "B", "LCDM"]:
        results[m]["H0_profile"] = profile_h(
            lk, m, results[m], n=5 if args.quick else 7
        )
        print(
            f"{m}: H0 = {results[m]['H0']:.3f} +/- {results[m]['H0_profile']['sigma_H0']:.3f}",
            flush=True,
        )

    check_pause()
    zt_grid = np.round(np.arange(0.1, 2.0 + 1e-9, 0.25 if args.quick else 0.05), 4)
    zt_profile = profile_zt(lk, zt_grid)

    wall = time.time() - t0
    rss_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    data_dir = os.path.join(HERE, "data")
    pins = {
        f: {
            "sha256": sha256_file(os.path.join(data_dir, f)),
            "bytes": os.path.getsize(os.path.join(data_dir, f)),
        }
        for f in sorted(os.listdir(data_dir))
        if not f.startswith(".")
    }
    raw = {
        "spike": "qbp-desi-fit round 1",
        "frozen_prereg": "spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md",
        "frozen_sha256": sha256_file(
            os.path.join(HERE, "..", "prereg", "qbp-desi-fit-r1-prereg-FROZEN-v1.md")
        ),
        "code_commit": git("rev-parse", "HEAD"),
        "code_dirty": bool(git("status", "--porcelain", "--", HERE)),
        "run_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t0)),
        "wall_seconds": wall,
        "max_rss_MB": rss_kb / 1024.0,
        "chi2_evaluations": lk.nevals,
        "quick_mode": args.quick,
        "N_data": {"bao": lk.bao.n, "sne": lk.sne.n, "planck": lk.cmb.n, "total": N},
        "sne_cuts": {
            "zHD_min": 0.01,
            "ceph_dist_used": False,
            "calibrator_host_sne_kept_as_hubble_flow": lk.sne.n_calibrator_hosts_kept,
        },
        "parameter_counts": {m: n_params(m) for m in ARMS},
        "priors": {
            "shared": SHARED,
            "model_specific": {m: MODELS[m]["free"] for m in ARMS},
            "fixed": {m: MODELS[m]["fixed"] for m in ARMS},
        },
        "fits": results,
        "zt_profile_B": zt_profile,
        "data_pins": pins,
        "versions": {
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "scipy": __import__("scipy").__version__,
        },
    }
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as fh:
        json.dump(raw, fh, indent=1)
    print(
        f"wrote {args.out}  wall={wall:.1f}s  maxrss={rss_kb/1024:.0f} MB  evals={lk.nevals}",
        flush=True,
    )


if __name__ == "__main__":
    main()
