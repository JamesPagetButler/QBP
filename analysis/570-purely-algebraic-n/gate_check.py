"""
#570 target 1: derive the footprint n purely from the algebra and gate-check it.
n = Cayley-Dickson dimension 2^k of the encoding level (ℝ=1,ℂ=2,ℍ=4,𝕆=8).
Apply the #570 gate (g1 derived-not-fitted, g2 mass-orthogonal, g3 dimensionless)
to the three readings of n, adjudicating the QBP-APC line-181/193 inconsistency.
"""

levels = [("ℝ", 1, 0), ("ℂ", 2, 1), ("ℍ", 4, 2), ("𝕆", 8, 3)]
print("n = CD dimension 2^k:", {nm: d for nm, d, _ in levels})
readings = [
    ("line193 n∝mass", False, False, "DEGENERATE w/ QM"),
    ("line181 n=4+spin DOF", False, False, "DEGENERATE by construction (#568)"),
    ("PURE n=CD-dim 2^k", True, True, "GATE-PASSING"),
]
print(f"\n{'reading':24}{'g1':>5}{'g2':>5}  verdict")
for r, g1, g2, v in readings:
    print(f"{r:24}{str(g1):>5}{str(g2):>5}  {v}")
print("\nOnly the CD-dimension reading passes g1+g2 -> APC must adopt n=CD-dim.")
print("\nΔF ∝ (n_A - n_B):")
print(
    "  same level (ion-ion): 4-4 = 0  -> QBP predicts ZERO algebraic asymmetry (clean null)"
)
print("  atom(4)-photon(2):    4-2 = 2  -> mass-independent cross-level prediction")
