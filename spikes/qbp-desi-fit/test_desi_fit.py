"""Tests-first harness checks for the qbp-desi-fit round-1 spike (pytest)."""

import os

import numpy as np
import pytest
from scipy.integrate import quad

import cosmo
import fit
import likelihoods

HERE = os.path.dirname(os.path.abspath(__file__))
HAVE_COV = os.path.exists(os.path.join(HERE, "data", "Pantheon+SH0ES_STAT+SYS.cov"))


# --- 1. LCDM distances vs an independent closed-form-grade quadrature -------------------
def test_lcdm_distances_known_cosmology():
    p = {"Om": 0.3, "h": 0.7, "ob": 0.0224}
    bg = cosmo.Background("LCDM", p, include_radiation=False)
    C = 299792.458

    def E_indep(z):
        return np.sqrt(0.3 * (1 + z) ** 3 + 0.7)

    for z in [0.1, 0.5, 1.0, 2.0]:
        ref = (
            C / 70.0 * quad(lambda zz: 1 / E_indep(zz), 0, z, epsabs=0, epsrel=1e-12)[0]
        )
        assert abs(bg.D_C_scalar(z) / ref - 1) < 1e-8
        assert abs(bg.D_M_grid(np.array([z]))[0] / ref - 1) < 1e-5
    # astropy FlatLambdaCDM(H0=70, Om0=0.3, Tcmb0=0).comoving_distance(1.0) = 3303.83 Mpc
    assert abs(bg.D_C_scalar(1.0) / 3303.83 - 1) < 1e-4
    assert abs(bg.D_H(1.0) - C / (70.0 * E_indep(1.0))) < 1e-9
    zs = np.array([0.3, 0.5, 1.0])
    DV = bg.D_V(zs)
    assert np.allclose(DV, np.cbrt(zs * bg.D_M_grid(zs) ** 2 * bg.D_H(zs)), rtol=1e-12)
    assert abs(bg.mu(1.0) - (5 * np.log10(2 * 3303.83) + 25)) < 1e-3


def test_grid_distances_match_quad_with_radiation():
    p = {"Om": 0.31, "h": 0.68, "ob": 0.0224, "zt": 0.7}
    for model in ["LCDM", "QBP", "CPL"]:
        pp = dict(p, w0=-0.9, wa=-0.3)
        bg = cosmo.Background(model, pp)
        z = np.array([0.01, 0.295, 0.706, 1.484, 2.33])
        grid = bg.D_M_grid(z)
        for zi, gi in zip(z, grid):
            assert abs(gi / bg.D_C_scalar(zi) - 1) < 1e-5, (model, zi)


# --- 2. The QBP curve ----------------------------------------------------------------
def test_qbp_curve_w_eff_zero_and_density_normalisation():
    zt = cosmo.ZT_RECORD
    assert (
        abs(cosmo.w_eff_frozen_s1(0.0, zt) - (-0.676)) < 1e-3
    )  # frozen section 1 / #774 table
    assert abs(cosmo.w_eff_frozen_s1(zt, zt) + 1.0) < 1e-12  # w = -1 at z_t
    assert abs(cosmo.w_eff_frozen_s1(1e6, zt) - (-5.0 / 3.0)) < 1e-6
    p = {"Om": 0.31, "h": 0.68, "ob": 0.0224, "zt": zt}
    bg = cosmo.Background("QBP", p)
    assert abs(cosmo.f_qbp(0.0, p) - 1.0) < 1e-14  # f(0) = Omega_DE (ratio 1)
    assert abs(bg.E(0.0) - 1.0) < 1e-14
    # the recorded density equals the #774 reading-I form [A(1+z)+B/(1+z)]^2 with (A+B)^2 = Omega_DE
    r = (1 + zt) ** 2
    A = 1.0 / (1 + r)
    B = r / (1 + r)
    z = np.linspace(0, 3, 50)
    assert np.allclose(cosmo.f_qbp(z, p), (A * (1 + z) + B / (1 + z)) ** 2, rtol=1e-13)


def test_frozen_s1_w_eff_is_mirror_of_s3_density_w():
    """Documents the pre-data inconsistency in the frozen text: the continuity-equation w(z) of
    the section-3 density f(z) is the reflection of the section-1 w_eff about w = -1
    (#774 step 6 uses -1/3 dln rho/dln(1+z); the continuity equation gives +1/3).
    The fit uses f(z) (section 3) verbatim; the section-1 formula is never used in a likelihood.
    """
    zt = cosmo.ZT_RECORD
    p = {"zt": zt}
    for z in [0.0, 0.3, 0.7, 1.5, 3.0]:
        w_f = cosmo.w_from_density(cosmo.f_qbp, z, p)
        w_s1 = cosmo.w_eff_frozen_s1(z, zt)
        assert abs((w_f + 1.0) + (w_s1 + 1.0)) < 1e-6
        # and the (not pre-registered) mirror density reproduces section 1 exactly
        assert abs(cosmo.w_from_density(cosmo.f_qbp_mirror, z, p) - w_s1) < 1e-6
    assert abs(cosmo.w_from_density(cosmo.f_qbp, 0.0, p) - (-1.324)) < 1e-3


# --- 3. analytic M marginalisation == explicit marginalisation on a toy ------------------
def test_analytic_M_marginalisation_matches_numerical():
    rng = np.random.default_rng(775)
    n = 6
    L = rng.normal(size=(n, n))
    cov = L @ L.T + n * np.eye(n)
    icov = np.linalg.inv(cov)
    r = rng.normal(size=n) + 19.0
    analytic = likelihoods.marginalised_chi2(r, icov)

    def like(M):
        rr = r - M
        return np.exp(-0.5 * rr @ icov @ rr)

    integral = quad(like, -200, 200, epsabs=0, epsrel=1e-12, limit=500)[0]
    numeric = -2.0 * np.log(integral)
    assert abs(analytic - numeric) < 1e-6
    # and it equals min_M chi2(M) + ln(C/2pi)
    C = float(np.ones(n) @ icov @ np.ones(n))
    Mbest = float(np.ones(n) @ icov @ r) / C
    rr = r - Mbest
    assert abs(analytic - (rr @ icov @ rr + np.log(C / (2 * np.pi)))) < 1e-9


# --- 4. parameter counts; 5. CPL -> LCDM -------------------------------------------------
def test_model_A_has_exactly_lcdm_parameter_count():
    assert fit.n_params("A") == fit.n_params("LCDM") == 3
    assert fit.n_params("B") == 4
    assert fit.n_params("CPL") == 5
    assert fit.MODELS["A"]["fixed"]["zt"] == 0.70
    assert fit.MODELS["B"]["free"]["zt"] == (0.1, 2.0)
    assert fit.MODELS["CPL"]["free"] == {"w0": (-3.0, 1.0), "wa": (-3.0, 2.0)}
    assert fit.SHARED == {"Om": (0.1, 0.6), "h": (0.5, 0.9), "ob": (0.015, 0.030)}


def test_cpl_reduces_to_lcdm():
    p = {"Om": 0.3, "h": 0.7, "ob": 0.0224}
    z = np.linspace(0, 1100, 300)
    e_l = cosmo.Background("LCDM", p).E(z)
    e_c = cosmo.Background("CPL", dict(p, w0=-1.0, wa=0.0)).E(z)
    assert np.allclose(e_l, e_c, rtol=1e-13, atol=0)
    # wCDM check of the CPL closed form against (1+z)^{3(1+w)}
    e_w = cosmo.f_cpl(z, {"w0": -0.8, "wa": 0.0})
    assert np.allclose(e_w, (1 + z) ** (3 * 0.2), rtol=1e-12)


# --- 6. early-time quantities vs the CAMB Planck-2018 reference ------------------------
def test_rd_and_rs_against_camb_reference():
    h = 0.6736
    ob, oc = 0.02237, 0.1200
    om = ob + oc + 0.06 / 93.14  # Planck 2018 omega_m h^2 = 0.1430
    bg = cosmo.Background("LCDM", {"Om": om / h**2, "h": h, "ob": ob})
    assert abs(bg.r_d() / 147.09 - 1) < 1e-3
    assert abs(bg.r_s(bg.z_star()) / 144.43 - 1) < 1e-3
    assert abs(bg.z_star() - 1089.9) < 1.5
    R, lA, obb = bg.planck_compressed()
    assert abs(R - 1.7502) < 0.01 and abs(lA - 301.47) < 0.5


# --- data loaders --------------------------------------------------------------------------
def test_bao_loader():
    bao = likelihoods.BAO()
    assert bao.n == 13
    assert np.allclose(bao.cov, bao.cov.T)
    assert np.all(np.linalg.eigvalsh(bao.cov) > 0)
    assert set(bao.kind) == {"DM_over_rs", "DH_over_rs", "DV_over_rs"}
    assert bao.z.min() == 0.295 and bao.z.max() == 2.33


def test_planck_loader_chi2_small_at_planck_bestfit():
    cmb = likelihoods.PlanckCompressed()
    h = 0.6736
    bg = cosmo.Background("LCDM", {"Om": 0.1430 / h**2, "h": h, "ob": 0.02237})
    assert cmb.chi2(bg) < 10.0


@pytest.mark.skipif(
    not HAVE_COV, reason="Pantheon+ covariance not cached (33 MB, see DATA-PINS.md)"
)
def test_pantheon_loader_and_marginalisation():
    sne = likelihoods.Pantheon()
    assert (
        sne.n == 1590
    )  # zHD > 0.01, cobaya PantheonPlus convention; CEPH_DIST never read
    assert sne.n_calibrator_hosts_kept == 10
    assert sne.cov.shape == (1590, 1590)
    bg = cosmo.Background("LCDM", {"Om": 0.33, "h": 0.7, "ob": 0.0224})
    c_marg = sne.chi2(bg)
    Ms = np.linspace(-19.6, -19.0, 61)
    c_exp = min(sne.chi2_explicit(bg, M) for M in Ms)
    assert abs((c_marg - np.log(sne.C / (2 * np.pi))) - c_exp) < 0.5
    assert 1400 < c_exp < 1800
