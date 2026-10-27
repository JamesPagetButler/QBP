#!/usr/bin/env python3
"""#772 AC2 — symbolic w_eff(z) for the QBP accretion model (DRAFT support script).

Source records (archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json, v6.19.0):
  PRED-H-equals-Mdot-over-M : H = Mdot/M
  PROOF-M-proportional-to-a : M = M0 * a = M0/(1+z)
  PRED-lambda-as-cross-term : Mdot = Mdot0 + beta*M^2  =>  H_B = A(1+z) + B/(1+z),
                              H_B^2 = A^2(1+z)^2 + 2AB + B^2(1+z)^-2 ; A~0.21, B~0.62, z_t~0.7
  PRED-w-not-minus-1        : w ~ -1 at z_t, w > -1 below z_t, w < -1 above z_t
  COMP-cmb-power-spectrum-accretion : CAMB used w(z) = -1.25 + 0.70 z/(1+z)

Everything below is algebra on those statements. Modelling choices are marked ASSUMED
in the companion analysis/772-accretion-wz-derivation-DRAFT.md.
Run:  run-bounded 2G 60 python3 analysis/772_wz_symbolic.py
"""

import sympy as sp

z, A, B, r, Om = sp.symbols("z A B r Omega_m", positive=True)
opz = 1 + z


def w_eff_from_rho(rho):
    """w_eff = -1 - (1/3) d ln rho / d ln(1+z)   (rho as a function of z)."""
    return sp.simplify(-1 - sp.Rational(1, 3) * opz * sp.diff(rho, z) / rho)


print("=" * 78)
print("STEP A  Mdot = Mdot0 + beta M^2, M = M0/(1+z)  =>  H_B = Mdot/M")
Mdot0, beta, M0 = sp.symbols("Mdot0 beta M0", positive=True)
M = M0 / opz
H_B_raw = (Mdot0 + beta * M**2) / M
H_B = sp.expand(H_B_raw)
print("  H_B =", H_B, "   (A := Mdot0/M0, B := beta*M0)")
H_B_AB = A * opz + B / opz
print(
    "  check H_B == A(1+z) + B/(1+z):",
    sp.simplify(H_B_raw.subs({Mdot0: A * M0, beta: B / M0}) - H_B_AB) == 0,
)
print("  H_B^2 expanded:", sp.expand(H_B_AB**2))

print("=" * 78)
print(
    "STEP B  Reading (I): rho_DE/rho_c0 = H_B^2/H0^2 (boundary rate is the DE sector only)"
)
rho_I = sp.expand(H_B_AB**2)
w_I = w_eff_from_rho(rho_I)
w_I_r = sp.simplify(w_I.subs(B, r * A))  # depends on r = B/A only
print("  w_eff(z) =", sp.factor(w_I))
print("  with r = B/A:  w_eff(z) =", sp.factor(w_I_r))
w_I_closed = -1 - sp.Rational(2, 3) * (opz**2 - r) / (opz**2 + r)
print(
    "  closed form -1 - (2/3)((1+z)^2 - r)/((1+z)^2 + r)  matches:",
    sp.simplify(w_I_r - w_I_closed) == 0,
)
print(
    "  w_eff(z) + 1 = 0  <=>  (1+z)^2 = r = B/A     (this is the mode-equality redshift)"
)
print(
    "  limits: z=0 ->",
    sp.simplify(w_I_closed.subs(z, 0)),
    " ; z->inf ->",
    sp.limit(w_I_closed, z, sp.oo),
)
zt = sp.symbols("z_t", positive=True)
w_I_zt = w_I_closed.subs(r, (1 + zt) ** 2)
print("  in terms of z_t ((1+z_t)^2 = B/A):  w_eff =", sp.simplify(w_I_zt))
print(
    "  CPL tangent at z=0 (s = z/(1+z)): w0 =",
    sp.simplify(w_I_closed.subs(z, 0)),
    "  wa = dw/ds|0 =",
    sp.simplify(
        sp.diff(
            w_I_closed.subs(z, sp.Symbol("s") / (1 - sp.Symbol("s"))), sp.Symbol("s")
        ).subs(sp.Symbol("s"), 0)
    ),
)

print("=" * 78)
print(
    "STEP C  Reconstruct the record's numbers: A~0.21, B~0.62, z_t~0.7, Omega_Lambda=0.685"
)
OmL = 0.685
r_num = 0.62 / 0.21
print(
    f"  B/A = {r_num:.3f}  ->  z_t = sqrt(B/A) - 1 = {r_num**0.5 - 1:.3f}   (record says z_t ~ 0.7)"
)
print(
    f"  (A+B)^2 = {(0.21+0.62)**2:.3f}  (= Omega_Lambda 0.685: matches HANDOFF 'A+B = sqrt(Omega_DE) ~ 0.83')"
)
print(
    f"  2AB = {2*0.21*0.62:.3f}  (record text says '2AB ~ 0.26 ~ Omega_Lambda' — 0.26 != 0.685; it is 38% of it)"
)
# solve A,B from (A+B)^2 = OmL and B/A = (1+0.7)^2
r_t = (1 + 0.7) ** 2
A_n = OmL**0.5 / (1 + r_t)
B_n = r_t * A_n
print(
    f"  From (A+B)^2=0.685 and (1+z_t)^2=B/A with z_t=0.7:  A={A_n:.3f}, B={B_n:.3f}, 2AB={2*A_n*B_n:.3f}"
)

print("=" * 78)
print(
    "STEP D  Reading (II): H_B is the TOTAL Hubble rate (H = adot/a = Mdot/M literally), matter inside"
)
rho_II = sp.expand(H_B_AB**2) - Om * opz**3
w_II = w_eff_from_rho(rho_II)
print("  rho_DE/rho_c0 = H_B^2/H0^2 - Omega_m (1+z)^3 ;  normalisation A+B = 1")
print("  w_eff(z) =", sp.simplify(w_II))
# acceleration under pure (II) with no matter: a(t): adot = A + B a^2 ... sign of addot
a_s = sp.symbols("a", positive=True)
H_a = A / a_s + B * a_s
adot = H_a * a_s
addot = sp.simplify(sp.diff(adot, a_s) * adot)
print(
    "  pure H_B with no matter: adot =",
    sp.expand(adot),
    " addot =",
    sp.factor(addot),
    " > 0 for all a  (never decelerates)",
)

print("=" * 78)
print(
    "STEP E  deceleration parameter q(z) under reading (I) + matter, Omega_m = 0.315, (A+B)^2 = 0.685"
)
Om_n = 0.315


def q_of_z(Hsq, zz):
    return float((-1 + sp.Rational(1, 2) * opz * sp.diff(Hsq, z) / Hsq).subs(z, zz))


Hsq_I = Om_n * opz**3 + (A_n * opz + B_n / opz) ** 2
import math

# find q=0 by bisection
lo, hi = 0.0, 3.0
for _ in range(60):
    mid = 0.5 * (lo + hi)
    if q_of_z(Hsq_I, mid) > 0:
        hi = mid
    else:
        lo = mid
z_q0 = 0.5 * (lo + hi)
print(
    f"  with z_t(mode-equality)=0.7 -> A={A_n:.3f}, B={B_n:.3f}: q=0 at z = {z_q0:.3f}"
)
Hsq_L = Om_n * opz**3 + (1 - Om_n)
lo, hi = 0.0, 3.0
for _ in range(60):
    mid = 0.5 * (lo + hi)
    if q_of_z(Hsq_L, mid) > 0:
        hi = mid
    else:
        lo = mid
print(f"  LCDM reference (Omega_m=0.315): q=0 at z = {0.5*(lo+hi):.3f}")
# scan r = B/A: how late can the q=0 transition be pushed under reading (I)?
import numpy as np


def z_q0_for_r(rr):
    An = OmL**0.5 / (1 + rr)
    Bn = rr * An
    Hs = Om_n * opz**3 + (An * opz + Bn / opz) ** 2
    lo2, hi2 = 0.0, 5.0
    if q_of_z(Hs, 0.0) >= 0:
        return float("nan")
    for _ in range(50):
        m2 = 0.5 * (lo2 + hi2)
        if q_of_z(Hs, m2) > 0:
            hi2 = m2
        else:
            lo2 = m2
    return 0.5 * (lo2 + hi2)


scan = [(rr, z_q0_for_r(rr)) for rr in np.logspace(0, 3, 25)]
best = max(scan, key=lambda t: (t[1] if t[1] == t[1] else -1))
print(
    "  scan of q=0 redshift vs r=B/A under (I): "
    + ", ".join(f"r={rr:.1f}:z={zq:.3f}" for rr, zq in scan[::4])
)
print(
    f"  maximum attainable q=0 redshift under (I) with Omega_m=0.315: z = {best[1]:.3f} at r = {best[0]:.1f}"
    "  -> q(z=0.7)=0 is NOT attainable for any A/B; z_t=0.7 can only be the mode-equality redshift"
)
print(
    "  H(z)/H_LCDM(z) under (I) with z_t=0.7:",
    ", ".join(
        f"z={zz}: {math.sqrt(float(Hsq_I.subs(z,zz))/float(Hsq_L.subs(z,zz))):.3f}"
        for zz in [0, 0.3, 0.5, 0.7, 1.0]
    ),
)

print("=" * 78)
print("STEP F  numeric table w_eff(z)")
w_I_num = w_I_closed.subs(r, r_t)  # reading (I), z_t = 0.7
A2 = 1 / (1 + r_t)
B2 = r_t / (1 + r_t)
w_II_num = w_II.subs({A: A2, B: B2, Om: Om_n})  # reading (II), A+B=1, Omega_m=0.315
rho_II_num = rho_II.subs({A: A2, B: B2, Om: Om_n})
w_CPL_comp = -1.25 + 0.70 * z / opz  # COMP record
w_CPL_desi = -0.55 - 1.3 * z / opz  # DESI Y1 numbers quoted in PRED-w-not-minus-1
zs = [0, 0.3, 0.7, 1, 2]
print(
    "| z | (I) r=(1+z_t)^2, z_t=0.7 | (II) total-H, Om=0.315 | rho_DE(II)/rho_c0 | COMP CPL -1.25+0.70 z/(1+z) | DESI Y1 CPL -0.55-1.3 z/(1+z) |"
)
print("|---|---|---|---|---|---|")
for zz in zs:
    rII = float(rho_II_num.subs(z, zz))
    wII = f"{float(w_II_num.subs(z, zz)):+.3f}" if rII > 0 else "undefined (rho_DE<0)"
    print(
        f"| {zz} | {float(w_I_num.subs(z, zz)):+.3f} | {wII} | {rII:+.3f} | {float(w_CPL_comp.subs(z, zz)):+.3f} | {float(w_CPL_desi.subs(z, zz)):+.3f} |"
    )
print()
print(
    "w = -1 crossings:  (I) z =",
    round(r_t**0.5 - 1, 3),
    "; COMP CPL z =",
    round(float(sp.nsolve(w_CPL_comp + 1, z, 0.5)), 3),
    "; DESI CPL z =",
    round(float(sp.nsolve(w_CPL_desi + 1, z, 0.5)), 3),
)
print(
    "sign of (w+1):  (I), DESI:    >0 below crossing (quintessence-like), <0 above (phantom-like)"
)
print(
    "                COMP CPL:       <0 below crossing (phantom-like), >0 above (quintessence-like)  — OPPOSITE"
)
print(
    "CPL tangent of (I) at z_t=0.7: w0 =",
    round(float(w_I_num.subs(z, 0)), 3),
    " wa =",
    round(float(-sp.Rational(8, 3) * r_t / (1 + r_t) ** 2), 3),
)
