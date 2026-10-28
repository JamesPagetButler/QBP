"""Gaussian likelihoods for the qbp-desi-fit round-1 spike: DESI DR2 BAO, Pantheon+ (no SH0ES,
analytic M marginalisation), Planck 2018 compressed distance priors (Chen, Huang & Wang 2019).
"""

import json
import os

import numpy as np
from scipy.linalg import cho_factor, cho_solve

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")


class BAO:
    def __init__(self, data_dir=DATA):
        rows = []
        with open(
            os.path.join(data_dir, "desi_gaussian_bao_ALL_GCcomb_mean.txt")
        ) as fh:
            for line in fh:
                if line.strip() and not line.startswith("#"):
                    z, v, q = line.split()
                    rows.append((float(z), float(v), q))
        self.z = np.array([r[0] for r in rows])
        self.d = np.array([r[1] for r in rows])
        self.kind = [r[2] for r in rows]
        self.cov = np.loadtxt(
            os.path.join(data_dir, "desi_gaussian_bao_ALL_GCcomb_cov.txt")
        )
        assert self.cov.shape == (len(rows), len(rows))
        self.icov = np.linalg.inv(self.cov)
        self.n = len(rows)

    def theory(self, bg):
        rd = bg.r_d()
        DM = bg.D_M_grid(self.z)
        DH = bg.D_H(self.z)
        DV = np.cbrt(self.z * DM**2 * DH)
        out = np.empty(self.n)
        for i, k in enumerate(self.kind):
            out[i] = {"DM_over_rs": DM[i], "DH_over_rs": DH[i], "DV_over_rs": DV[i]}[
                k
            ] / rd
        return out

    def chi2(self, bg):
        r = self.d - self.theory(bg)
        return float(r @ self.icov @ r)


class Pantheon:
    """Pantheon+ without SH0ES: Cepheid host distances (CEPH_DIST) are never read, so no SH0ES
    calibration enters; the standard cosmology-sample cut zHD > zmin (default 0.01) is applied,
    as in the public cobaya PantheonPlus likelihood (1590 light curves).
    chi2 is marginalised analytically over the absolute magnitude M with a flat prior:
        chi2_marg = A - B^2/C + ln(C / 2 pi),   A = r'Cinv r, B = 1'Cinv r, C = 1'Cinv 1,
    where r = m_b_corr - mu_theory (i.e. the residual at M = 0)."""

    def __init__(self, data_dir=DATA, zmin=0.01):
        dat = os.path.join(data_dir, "Pantheon+SH0ES.dat")
        with open(dat) as fh:
            cols = fh.readline().split()
        raw = np.genfromtxt(
            dat, skip_header=1, dtype=None, encoding="utf-8", names=cols
        )
        mask = raw["zHD"] > zmin
        self.n_calibrator_hosts_kept = int(raw["IS_CALIBRATOR"][mask].sum())
        self.mask = mask
        self.zhd = raw["zHD"][mask].astype(float)
        self.zhel = raw["zHEL"][mask].astype(float)
        self.mb = raw["m_b_corr"][mask].astype(float)
        self.n = int(mask.sum())
        covfile = os.path.join(data_dir, "Pantheon+SH0ES_STAT+SYS.cov")
        flat = np.loadtxt(covfile)
        N = int(flat[0])
        full = flat[1:].reshape(N, N)
        assert N == len(raw)
        self.cov = full[np.ix_(mask, mask)]
        cf = cho_factor(self.cov)
        self.icov = cho_solve(cf, np.eye(self.n))
        ones = np.ones(self.n)
        self.icov_ones = self.icov @ ones
        self.C = float(ones @ self.icov_ones)

    def residual(self, bg):
        return self.mb - bg.mu(self.zhd, self.zhel)

    def chi2(self, bg):
        r = self.residual(bg)
        return marginalised_chi2(r, self.icov, self.icov_ones, self.C)

    def chi2_explicit(self, bg, M):
        r = self.residual(bg) - M
        return float(r @ self.icov @ r)


def marginalised_chi2(r, icov, icov_ones=None, C=None):
    if icov_ones is None:
        icov_ones = icov @ np.ones(len(r))
    if C is None:
        C = float(np.ones(len(r)) @ icov_ones)
    A = float(r @ icov @ r)
    B = float(r @ icov_ones)
    return A - B * B / C + np.log(C / (2.0 * np.pi))


class PlanckCompressed:
    def __init__(self, data_dir=DATA):
        with open(
            os.path.join(data_dir, "planck2018_distance_priors_chen2019.json")
        ) as fh:
            j = json.load(fh)
        self.mean = np.array(j["mean"])
        self.icov = np.array(j["inverse_covariance"])
        self.n = 3

    def chi2(self, bg):
        r = bg.planck_compressed() - self.mean
        return float(r @ self.icov @ r)
