#!/usr/bin/env python3
"""PR #663 round-3 fixes to the ten definition-conversation PROOF anchors (Red Team M1–M4 +
Gemini's name fix), applied as a SECOND confined edit (the round-1 encoder is one-shot).

M1  the family anchor over-claimed "constant along L_u-complex lines": the only proved statement
    is `quatDouble u (u·w) = quatDouble u w` (one step). The anchor is RE-IDENTIFIED — remove +
    append under an honest id — and its description says exactly the one step; the
    transitivity anchor's prediction_chain and the manifest follow the rename.
M2  the ρ-invariant-doubles anchor's NAME said "a continuum of candidates" while its description
    disclaimed any count; "refutes 'exactly 7'" softened to what the Lean shows.
M3  the rho-moves-cd-half anchor gains the file's caveat (the three halves pairwise distinct is
    NOT claimed) and states "eliminates P2′" conditionally on ρ-equivariance as a premise.
M4  the Hessian anchor cites `hessQuad_flatDir` (its description used it) — ledger + manifest.
Gemini: drop "(w ⟂ u)" from the family anchor's name — its theorem takes ANY w.
Usage: python3 scripts/encode_definition_conversation_anchors_r3.py [--dry-run]
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
MANIFEST = ROOT / "docs/cth/anchor-worthy-manifest.json"
CH = "QBP.Foundations.CrystalHosting."
HS = "QBP.Foundations.HolographicSubalgebra."
OLD_FAM = "PROOF-encoding-family-constant-along-complex-lines"
NEW_FAM = "PROOF-encoding-family-u-mul-invariant"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        # M1 + Gemini: re-identify the family anchor
        fam = ed.remove("anchors", OLD_FAM)
        fam["id"] = NEW_FAM
        fam["name"] = (
            "Around a non-pole crystal, every quatDouble u w contains the hosted algebra and is "
            "ρ-invariant; the family is invariant under w ↦ u·w, and L_u² = −Id on u^⊥ ∩ Im𝕆"
        )
        fam["description"] = (
            "Foundations/HolographicSubalgebra.lean: `leftMul_sq_eq_neg` (u·(u·z) = −z for unit imaginary u) "
            "and `perp_stable_under_leftMul` make u^⊥ ∩ Im𝕆 a complex vector space under L_u; "
            "`quatSpan_subset_quatDouble` and `encoding_family_member` (w ARBITRARY — degenerate w including "
            "w = 0 are members; the physical case is unit w ⟂ u); `quatDouble_eq_of_mul_u`: "
            "quatDouble u (u·w) = quatDouble u w — ONE step of the L_u-action. This is the definition "
            "conversation's replacement for the refuted claim that a generic crystal's algebra lies in no "
            "ρ-invariant octonion. NOT claimed: constancy along a whole L_u-complex line (invariance under "
            "w ↦ (a + b·u)·w for all (a,b) ≠ 0, including real rescaling, is not proved); a bijection onto "
            "ℂP²; the real dimension of the family; transitivity of the crystal's stabiliser on it."
        )
        ed.append("anchors", fam)
        tr = ed.record("anchors", "PROOF-encoding-family-transitive-of-aut")
        tr["prediction_chain"] = [
            NEW_FAM if c == OLD_FAM else c for c in tr["prediction_chain"]
        ]
        # M2
        qd = ed.record("anchors", "PROOF-quatdouble-rho-invariant-mul-closed")
        qd["name"] = (
            "Every Cayley–Dickson double ℍ ⊕ ℍ·ℓ of a quaternion span in 𝕆 is a ρ-invariant, "
            "multiplication-closed subset of 𝕊 — for every pair (p, q), not only the seven Fano doubles"
        )
        qd["description"] = qd["description"].replace(
            "Refutes the definition-conversation dyad's 'exactly 7 ρ-invariant octonion subalgebras' (the seven "
            "Fano doubles are members, not the whole).",
            "Bears on the definition-conversation dyad's 'exactly 7 ρ-invariant octonion subalgebras': the seven "
            "Fano doubles are members of a family defined for every (p, q); whether distinct pairs give distinct "
            "doubles, and how many there are, is NOT proved here (`quatDouble_eq_of_mul_u` exhibits collisions).",
        )
        # M3
        rm = ed.record("anchors", "PROOF-rho-moves-cd-half-as-set")
        rm["description"] = rm["description"].replace(
            "Consequence for Decision 1 (INTERP-holographic-boundary, open): the P2′ reading's encoding half is "
            "NOT ρ-invariant, while every quatDouble is (PROOF-quatdouble-rho-invariant-mul-closed) — "
            "ρ-equivariance eliminates P2′ and constrains P2 not at all. Recorded as a RESULT; nothing ruled.",
            "Consequence for Decision 1 (INTERP-holographic-boundary, open): UNDER THE PREMISE that the encoding "
            "must be ρ-equivariant, the P2′ reading's encoding half is excluded (it is not ρ-invariant), while "
            "every quatDouble is (PROOF-quatdouble-rho-invariant-mul-closed) — so that premise constrains P2 not "
            "at all. The premise itself is not a theorem. Recorded as a RESULT; nothing ruled. NOT claimed: that "
            "the three halves 𝕆_low, ρ𝕆_low, ρ²𝕆_low are pairwise distinct (the ℤ/3-torsor gloss is numerical, "
            "`p2_cell_torsor_check.py`).",
        )
        # M4
        hs = ed.record("anchors", "PROOF-vacuum-hessian-transverse-eigenvalue")
        w = CH + "hessQuad_flatDir"
        if w not in hs["lean_companion_theorems"]:
            hs["lean_companion_theorems"].append(w)
            hs["verification"]["witnesses"].append(w)
        for a in L["anchors"]:
            if a["id"] in (
                NEW_FAM,
                "PROOF-encoding-family-transitive-of-aut",
                "PROOF-quatdouble-rho-invariant-mul-closed",
                "PROOF-rho-moves-cd-half-as-set",
                "PROOF-vacuum-hessian-transverse-eigenvalue",
            ):
                assert (
                    "constant along" not in a["name"] and "continuum" not in a["name"]
                )
        L["changelog"][-1]["note"] += (
            " Round-3 review (Red Team M1–M4, Gemini): the family anchor re-identified as "
            f"{NEW_FAM} (only w ↦ u·w invariance is proved; line-constancy NOT claimed); 'continuum' removed "
            "from a name; the P2′ exclusion stated as conditional on ρ-equivariance; three-halves-distinct "
            "caveat added; hessQuad_flatDir cited."
        )
        ed.touch("changelog")
    m = json.loads(MANIFEST.read_text())
    for e in m["entries"]:
        if e["anchor_id"] == OLD_FAM:
            e["anchor_id"] = NEW_FAM
        if (
            e["anchor_id"] == "PROOF-vacuum-hessian-transverse-eigenvalue"
            and CH + "hessQuad_flatDir" not in e["witnesses"]
        ):
            e["witnesses"].append(CH + "hessQuad_flatDir")
    if not args.dry_run:
        MANIFEST.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n")
    print(f"{'DRY ' if args.dry_run else ''}applied round-3 fixes")


if __name__ == "__main__":
    main()
