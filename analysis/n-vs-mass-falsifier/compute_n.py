"""
n-vs-mass falsifier (#567 Test C verdict): apply QBP-APC's footprint rule to the
species used in Test C experiments and test whether n decouples from mass.
QBP-APC: n = 4 (ℍ base) + internal-structure DOF.
  Reading A (APC line 193): internal ~ mass/complexity  -> n tracks mass.
  Reading B (APC line 181): internal = spin states / hyperfine -> nuclear-spin DOF.
Discriminator: ISOTOPE pairs (near-equal mass, very different nuclear spin I).
The integer n-values are SCHEMATIC; the structural result is the ratio comparison.
"""

species = [
    ("9Be+", 9, 1.5),
    ("25Mg+", 25, 2.5),
    ("40Ca+", 40, 0.0),
    ("43Ca+", 43, 3.5),
    ("88Sr+", 88, 0.0),
    ("87Sr+", 87, 4.5),
]


def nstates(I):
    return int(round(2 * I + 1))


print(f"{'species':8}{'A':>4}{'I':>5}{'2I+1':>6}  nA(~mass)  nB(=4+2I+1)")
for name, A, I in species:
    print(f"{name:8}{A:>4}{I:>5}{nstates(I):>6}  {4+A:>9}  {4+nstates(I):>9}")
print("\n=== isotope discriminator (mass~equal, internal DOF very different) ===")
for (na, Aa, Ia), (nb, Ab, Ib) in [
    (("40Ca+", 40, 0.0), ("43Ca+", 43, 3.5)),
    (("88Sr+", 88, 0.0), ("87Sr+", 87, 4.5)),
]:
    mr = Ab / Aa
    rA = (4 + Aa) / (4 + Ab)
    rB = (4 + nstates(Ia)) / (4 + nstates(Ib))
    print(f"{na}/{nb}: mass ratio={mr:.3f}")
    print(
        f"   Reading A (n~mass): footprint ratio={rA:.3f} -> tracks mass -> DEGENERATE"
    )
    print(
        f"   Reading B (n~spin): footprint ratio={rB:.3f} -> diverges from mass -> TESTABLE"
    )
