"""Background cosmology for the qbp-desi-fit round-1 spike (numpy/scipy only).

Models (frozen pre-registration spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md):
  LCDM : rho_DE(z)/rho_DE(0) = 1
  QBP  : f(z) = [(1+z) + r/(1+z)]^2 / (1+r)^2,  r = (1+z_t)^2   (frozen section 3, arm A/B)
         (= the #774 reading-I density  rho_DE = H_B^2 = [A(1+z) + B/(1+z)]^2 normalised to Omega_DE)
  CPL  : w(a) = w0 + wa (1-a)
Flat; Omega_DE = 1 - Omega_m - Omega_r.  Radiation follows the Chen, Huang & Wang 2019
convention (Omega_r = Omega_m / (1+z_eq)) because the Planck compressed priors were calibrated
with it; it is identical in every model.
"""

import numpy as np
from scipy.integrate import quad, cumulative_simpson

C_KMS = 299792.458
T_CMB = 2.7255
N_EFF = 3.044
ZT_RECORD = 0.70  # arm A, frozen section 3
ZT_ROBUST = (
    0.718  # frozen section 3 robustness line (= sqrt(B/A) - 1 from the rounded A, B)
)


# --- dark-energy density ratios rho_DE(z)/rho_DE(0) -------------------------------------
def f_lcdm(z, p):
    return np.ones_like(np.asarray(z, dtype=float))


def f_qbp(z, p):
    """Frozen section 3: f(z)/Omega_DE = [(1+z) + (1+z_t)^2/(1+z)]^2 / [1 + (1+z_t)^2]^2."""
    x = 1.0 + np.asarray(z, dtype=float)
    r = (1.0 + p["zt"]) ** 2
    return ((x + r / x) / (1.0 + r)) ** 2


def f_qbp_mirror(z, p):
    """NOT pre-registered. The density whose continuity-equation w(z) equals the frozen
    section-1 w_eff formula exactly (the reciprocal of f_qbp). Recorded as a diagnostic only.
    """
    return 1.0 / f_qbp(z, p)


def f_cpl(z, p):
    x = 1.0 + np.asarray(z, dtype=float)
    w0, wa = p["w0"], p["wa"]
    return x ** (3.0 * (1.0 + w0 + wa)) * np.exp(-3.0 * wa * (x - 1.0) / x)


def w_eff_frozen_s1(z, zt):
    """Frozen section 1 formula, verbatim: w = -1 - (2/3)[(1+z)^2 - (1+z_t)^2]/[(1+z)^2 + (1+z_t)^2]."""
    x2 = (1.0 + np.asarray(z, dtype=float)) ** 2
    r = (1.0 + zt) ** 2
    return -1.0 - (2.0 / 3.0) * (x2 - r) / (x2 + r)


def w_from_density(fratio, z, p, eps=1e-6):
    """w(z) = -1 + (1/3) dln rho / dln(1+z) (continuity equation; numerical derivative)."""
    x = 1.0 + z
    lnf = lambda xx: np.log(fratio(xx - 1.0, p))
    d = (lnf(x * (1 + eps)) - lnf(x * (1 - eps))) / (2 * eps)
    return -1.0 + d / 3.0


DE_RATIO = {"LCDM": f_lcdm, "QBP": f_qbp, "QBP_MIRROR": f_qbp_mirror, "CPL": f_cpl}


# --- background --------------------------------------------------------------------------
def omega_r(Om, h):
    zeq = 2.5e4 * Om * h * h * (T_CMB / 2.7) ** -4
    return Om / (1.0 + zeq)


class Background:
    """E(z) = H(z)/H0 and distances for one parameter point.

    p: dict with Om, h, ob (omega_b h^2) and the model's extra parameters (zt | w0, wa).
    """

    def __init__(self, model, p, include_radiation=True):
        self.model = model
        self.p = dict(p)
        self.Om = p["Om"]
        self.h = p["h"]
        self.H0 = 100.0 * self.h
        self.Or = omega_r(self.Om, self.h) if include_radiation else 0.0
        self.Ode = 1.0 - self.Om - self.Or
        self._f = DE_RATIO[model]

    def E(self, z):
        x = 1.0 + np.asarray(z, dtype=float)
        return np.sqrt(self.Or * x**4 + self.Om * x**3 + self.Ode * self._f(z, self.p))

    def H(self, z):
        return self.H0 * self.E(z)

    def D_H(self, z):
        return C_KMS / self.H(z)

    def D_C_scalar(self, z):
        val, _ = quad(lambda zz: 1.0 / self.E(zz), 0.0, z, limit=200, epsrel=1e-9)
        return C_KMS / self.H0 * val

    def D_M_grid(self, z, n=4001):
        """Comoving distance (flat: D_M = D_C) at an array of z via cumulative Simpson on a
        fine grid + linear interpolation. Accurate to << 1e-4 relative for z <= 3."""
        z = np.atleast_1d(np.asarray(z, dtype=float))
        zmax = max(float(z.max()), 1e-3)
        grid = np.linspace(0.0, zmax, n)
        integ = cumulative_simpson(1.0 / self.E(grid), x=grid, initial=0.0)
        return C_KMS / self.H0 * np.interp(z, grid, integ)

    def D_M(self, z):
        z = np.asarray(z, dtype=float)
        if z.ndim == 0:
            return self.D_C_scalar(float(z))
        return self.D_M_grid(z)

    def D_V(self, z):
        return np.cbrt(z * self.D_M(z) ** 2 * self.D_H(z))

    def D_L(self, z_hd, z_hel=None):
        if z_hel is None:
            z_hel = z_hd
        return (1.0 + np.asarray(z_hel)) * self.D_M(z_hd)

    def mu(self, z_hd, z_hel=None):
        return 5.0 * np.log10(self.D_L(z_hd, z_hel)) + 25.0

    # --- early-time quantities ---------------------------------------------------------
    def z_star(self):
        """Hu & Sugiyama 1996 fitting formula (as used by Chen, Huang & Wang 2019)."""
        ob = self.p["ob"]
        om = self.Om * self.h**2
        g1 = 0.0738 * ob**-0.238 / (1.0 + 39.5 * ob**0.763)
        g2 = 0.560 / (1.0 + 21.1 * ob**1.81)
        return 1048.0 * (1.0 + 0.00124 * ob**-0.738) * (1.0 + g1 * om**g2)

    def r_s(self, z):
        """Comoving sound horizon, Chen+2019 eq.: (c/H0) int_0^a da / (a^2 E sqrt(3(1+R_b a)))."""
        Rb = 31500.0 * self.p["ob"] * (T_CMB / 2.7) ** -4
        a_end = 1.0 / (1.0 + z)

        def integrand(a):
            zz = 1.0 / a - 1.0
            return 1.0 / (a * a * self.E(zz) * np.sqrt(3.0 * (1.0 + Rb * a)))

        val, _ = quad(integrand, 0.0, a_end, limit=200, epsrel=1e-9)
        return C_KMS / self.H0 * val

    def r_d(self):
        """BAO drag-epoch sound horizon from (omega_b, omega_m): Brieden, Gil-Marin & Verde 2023
        (arXiv:2212.04522) CAMB-calibrated fit, as used by DESI; identical in every model.
        """
        om = self.Om * self.h**2
        ob = self.p["ob"]
        return (
            147.05
            * (om / 0.1432) ** -0.23
            * (N_EFF / 3.04) ** -0.1
            * (ob / 0.02236) ** -0.13
        )

    def planck_compressed(self):
        """(R, l_A, omega_b) with the Chen+2019 definitions."""
        zs = self.z_star()
        DM = self.D_C_scalar(zs)  # (1+z*) D_A = D_M
        R = DM * np.sqrt(self.Om) * self.H0 / C_KMS
        lA = np.pi * DM / self.r_s(zs)
        return np.array([R, lA, self.p["ob"]])
