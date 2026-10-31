#!/usr/bin/env python3
"""QBP#755 AC4 — promote INSIGHT-octonion-quaternion-branching's CORE theory→PROOF.

The γ(a,b) ∈ Aut(𝕆) family is now kernel-proven in
`proofs/QBP/Foundations/OctonionAutBranching.lean` (PR #787, the Sonnet-arm proof).
This encoder flips the existing node `INSIGHT-octonion-quaternion-branching` from
provenance_kind `theory` to `proof` and attaches the five γ witnesses, WITHOUT
claiming the parts the proof does NOT establish.

PROVED (kernel, #755; the 5 witnesses): for unit quaternions a,b (N a = N b = 1),
γ(a,b) is a multiplicative automorphism of 𝕆 = CDAlg ℝ 3 (`gamma_mul`) proved via the
four-term Cayley–Dickson expansion using associativity of ℍ = CDAlg ℝ 2 ONLY (never
of 𝕆); it fixes the hosted quaternion subalgebra setwise (`gamma_fixes_hosted`); γ = id
iff trivial (`gamma_id_iff`); γ is bijective (`gamma_bijective`); packaged as
`gammaAut : CDAut 3` (a def). Classical mathematics (the standard Spin(4) → SO(4) ⊂ G₂
= Aut(𝕆) construction) — novel ONLY as a kernel-checked CDAlg formalization, per #755
honest-framing; do NOT present as a new result.

NOT claimed (AC4 exclusions, kept explicit — these stay theory/computational):
  (1) the 7 = (3,1) ⊕ (2,2) irrep branching (VERIFIED computationally, #559
      verify_g2_so4_branching.py — NOT kernel-proven here);
  (2) "SO(4) is the FULL stabiliser of ℍ in G₂" (needs Aut(𝕆) ≅ G₂, #622).

Attribution (AC5): the γ proof was authored by `claude-sonnet-5` as the Sonnet arm of
deming's 2026-09-30 cost-calibration harness, and deming independently kernel-verified
it (Nidavellir-bench-staging/results/VERIFICATION-RECORD-octonion-node.md). Provenance
metadata only — it does not touch the PA grade.

Schema: #697 shape (cth QBP#464 seq3942 — confirmed for theory→PROOF upgrades too): flip
provenance_kind/status, add verification/theorems/proof fields, pa 0/0; NO inline
source_sha / proof_assistants (those are the notary layer, derived from evidence_ref
post-notarisation). The composite import-closure manifest + PA grade arrive via the
notary path later (Seam: PA stays 0/0 until Notary evidence lands).

prediction_chain: kept as-is (`[]`). The module USES octonion_artin (Artin.lean),
cdAlg_mul_add_swap (ArtinTrace), quatSpan_assoc (InFlightAlgebra), CDAut
(CrystalHosting), instRingTwo (CDBridge), cdAlg2_norm_composition — candidate
derived_from edges, but adding them is a criticality/theory call left to
@qbp-oppenheimer's §I4 (not invented by the encoder).

FQ witness names + axiom closures are READ from the run-bounded capture JSON
(analysis/755-gamma-axioms.json: {short: {fq, axioms}}); the encoder asserts every
closure ⊆ {propext, Classical.choice, Quot.sound} (C3-FULL) before it will mint.

Usage: python3 scripts/encode_755_ac4_gamma_anchor.py --axioms-file analysis/755-gamma-axioms.json [--dry-run]
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()

ANCHOR_ID = "INSIGHT-octonion-quaternion-branching"
PROOF_FILE = "proofs/QBP/Foundations/OctonionAutBranching.lean"
DATE = "2026-10-29T00:00:00Z"
BATCH = "#755-ac4-gamma"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Revised name — @qbp-oppenheimer's PHYSICS-SIGNED wording (PR #787, resolving cth's
# seq3953 over-claim concern + arch F3): headline = the proven γ-core; the (3,1)⊕(2,2)
# branching demoted to computationally-verified-only (#559), explicitly NOT claimed — so
# the id+name+kind consumption point no longer reads "branching proven" atop
# provenance_kind:proof. cth confirms exact wording at the final-head co-sign; --name overrides.
NEW_NAME = (
    "γ(a,b) ∈ Aut(𝕆) for pairs fixing the hosted ℍ — kernel-proven (OctonionAutBranching: "
    "gamma_mul, gamma_fixes_hosted, gamma_id_iff, gamma_bijective, gammaAut). The "
    "7 = (3,1)⊕(2,2) branching under that action is computationally verified only (#559) "
    "and is NOT claimed by this anchor."
)

# derived_from edges from the proof-term closure of gammaAut (220 decls) ∩ ledger witnesses,
# re-derived by @qbp-oppenheimer (seq3955) and CONFIRMED by arch (seq3956) + cth (seq3957).
# The calibration header's "free to use" list was the WRONG source (availability ≠
# dependency): octonion_artin / quatSpan_assoc / cdAlg2_norm_composition / cdAlg_mul_add_swap
# are NOT in the closure — oppenheimer's seq3950 edges (and my seq3949 candidates) withdrawn.
# mul_coord_matrix is in the closure but homed under PROOF-sedenion-dirac-sum-kill — a
# witness-home-collision, NOT a dependency; excluded + re-home filed as a hygiene issue.
# --derived-from overrides; default is these three (each guarded to exist in the ledger).
DERIVED_FROM = [
    "PROOF-cd-product-formula",  # cdAlg_sq_eq / basis_expansion / e_mul_e / mulCoeff_props
    "PROOF-cd-associativity-level2",  # cdAlg_two_assoc + unit laws
    "PROOF-cd-associator-formula",  # assoc_e
]


def next_minor(ver):
    """6.X.Y -> 6.(X+1).0 (ledger convention: minor bump per content edit)."""
    parts = ver.split(".")
    return f"{parts[0]}.{int(parts[1]) + 1}.0"


# short name -> (kind, source line) for the witness-resolution guard
WITNESS_DECLS = {
    "gamma_mul": ("theorem", 469),
    "gamma_fixes_hosted": ("theorem", 481),
    "gamma_id_iff": ("theorem", 500),
    "gamma_bijective": ("theorem", 680),
    "gammaAut": ("def", 687),
}
HEADLINE = "gamma_mul"
COMPANIONS = ["gamma_fixes_hosted", "gamma_id_iff", "gamma_bijective", "gammaAut"]

LIBS = {
    "mathlib": {
        "ref": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "sha": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
    },
    "batteries": {"ref": "main", "sha": "32dc18cde3684679f3c003de608743b57498c56f"},
}

NEW_DESCRIPTION = (
    "γ(a,b) ∈ Aut(𝕆) — the SO(4) ⊂ G₂ octonion-automorphism family, CORE kernel-PROVED "
    "(QBP#755, proofs/QBP/Foundations/OctonionAutBranching.lean, namespace "
    "QBP.Foundations.OctonionAutBranching). For unit quaternions a,b : CDAlg ℝ 2 (N a = "
    "N b = 1) the coordinate-packaged map γ(a,b)(x₁,x₂) = (a·x₁·ā, b·x₂·ā) on 𝕆 = CDAlg "
    "ℝ 3 is: multiplicative on ALL of 𝕆 (`gamma_mul`) — the hard, non-vacuous fact, proved "
    "through the four-term Cayley–Dickson expansion using associativity of ℍ = CDAlg ℝ 2 "
    "ONLY, never associativity of 𝕆 (which fails, cf. Artin.lean); fixes the hosted "
    "quaternion subalgebra {x | oHi x = 0} setwise (`gamma_fixes_hosted`); equals the "
    "identity iff trivial (`gamma_id_iff`); is bijective (`gamma_bijective`); packaged as "
    "`gammaAut : CDAut 3` (def). Each kernel-checked, 0 sorry, 0 native_decide, #print "
    "axioms ⊆ {propext, Classical.choice, Quot.sound}. "
    "HONEST FRAMING (#755): the mathematics is CLASSICAL — the standard Spin(4) → SO(4) ⊂ "
    "G₂ = Aut(𝕆) construction (Conway–Smith / Baez). What is new is ONLY the kernel-checked "
    "formalization in QBP's CDAlg framework proving multiplicativity via ℍ-associativity "
    "alone; NOT a novel mathematical result. "
    "NOT CLAIMED (AC4 exclusions — these remain theory/computational, NOT upgraded by this "
    "proof): (1) the 7 = (3,1) ⊕ (2,2) imaginary-octonion irrep branching (retained Im(ℍ) "
    "= (3,1), lost (2,2) bi-doublet) — VERIFIED only computationally (#559 "
    "analysis/559-generator-dof-map/verify_g2_so4_branching.py, 2000-trial), NOT kernel-"
    "proven; (2) 'SO(4) is the FULL stabiliser of ℍ in G₂' — needs Aut(𝕆) ≅ G₂ (#622), "
    "unproven here (γ gives the ⊆ direction: an SO(4) worth of automorphisms fixing ℍ, not "
    "maximality). "
    "ATTRIBUTION (AC5): the Lean proof was authored by claude-sonnet-5 as the Sonnet arm of "
    "deming's 2026-09-30 cost-calibration harness (~10 iterations; Gemini-pro failed, Opus "
    "skipped) and independently kernel-verified by deming (Nidavellir-bench-staging/results/"
    "VERIFICATION-RECORD-octonion-node.md). Provenance metadata only — does not affect the "
    "PA grade. "
    "PA (pa_local/pa_effective) 0/0, ungraded — no Notary proof-assistant evidence recorded "
    "yet (Seam: PA stays 0/0 until Notary evidence lands; research-tier). Prior computational "
    "branching result retained as the node's theory context (#559/#539/#560); this upgrade "
    "promotes ONLY the γ-family core."
)


def resolves(short):
    kind, _ = WITNESS_DECLS[short]
    src = (ROOT / PROOF_FILE).read_text(encoding="utf-8")
    heads = (
        ("theorem ", "lemma ")
        if kind == "theorem"
        else ("def ", "noncomputable def ", "theorem ", "lemma ")
    )
    for line in src.splitlines():
        s = line.lstrip()
        if any(s.startswith(h + short) for h in heads):
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--axioms-file", required=True)
    ap.add_argument(
        "--derived-from",
        nargs="*",
        default=None,
        help="prediction_chain ids (closure-derived); default = DERIVED_FROM",
    )
    ap.add_argument(
        "--name", default=None, help="anchor name override; default = NEW_NAME"
    )
    ap.add_argument(
        "--version", default=None, help="ledger version to set; default = next-minor"
    )
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if not (ROOT / PROOF_FILE).exists():
        raise SystemExit(
            f"module missing on this head (checkout PR #787): {PROOF_FILE}"
        )
    for short in WITNESS_DECLS:
        if not resolves(short):
            raise SystemExit(f"witness does not resolve in {PROOF_FILE}: {short}")

    cap = json.loads(Path(args.axioms_file).read_text())
    # {short: {"fq": ..., "axioms": [...]}}
    for short in WITNESS_DECLS:
        if short not in cap:
            raise SystemExit(f"capture JSON missing witness: {short}")
        extra = set(cap[short]["axioms"]) - ALLOWED_AXIOMS
        if extra:
            raise SystemExit(
                f"C3-FULL: {short} closure has disallowed axioms {sorted(extra)}"
            )
    print(f"C3-FULL OK: all 5 γ witnesses ⊆ {{propext, Classical.choice, Quot.sound}}")

    fq = {s: cap[s]["fq"] for s in WITNESS_DECLS}
    witnesses = [fq[HEADLINE]] + [fq[c] for c in COMPANIONS]
    edges = (
        list(args.derived_from) if args.derived_from is not None else list(DERIVED_FROM)
    )
    name = args.name or NEW_NAME

    verifier = (
        f"QBP#755 AC4 (qbp-implementor writer lane), PR #787 branch "
        f"foundations/755-gamma-aut-proof. #print axioms on the 5 γ witnesses captured under "
        f"run-bounded 6G at head 43ae30a (analysis/755-gamma-axioms.json); every closure = "
        f"{{propext, Classical.choice, Quot.sound}} (C3-FULL PASS, 0 sorry / 0 native_decide). "
        f"Proof authored by claude-sonnet-5 (Sonnet arm, deming 2026-09-30 harness), deming-"
        f"verified (VERIFICATION-RECORD-octonion-node.md). Theory→PROOF upgrade; theory-axis "
        f"co-sign @qbp-oppenheimer, schema-axis co-sign @cth-implementor."
    )

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {x["id"] for x in L["anchors"]}
        for d in edges:
            if d not in have:
                raise SystemExit(
                    f"derived_from target missing from ledger (dangling edge): {d}. "
                    f"If this is PROOF-cd-* at #787's pre-#788 base, run on the merged head."
                )
        version = args.version or next_minor(L["version"])

        # Idempotent: set proof fields + name + edges regardless of current state (a
        # re-run where a field is already final is a no-op on that field). The confined
        # writer rejects a wholly-unchanged record, which correctly signals "already final".
        a = ed.record("anchors", ANCHOR_ID)
        a["provenance_kind"] = "proof"
        a["proof_file"] = PROOF_FILE
        a["proof_language"] = "lean4"
        a["proof_state"] = "verified"
        a["sorry_count"] = 0
        a["name"] = name
        a["lean_theorem"] = fq[HEADLINE]
        a["lean_companion_theorems"] = [fq[c] for c in COMPANIONS]
        a["theorems"] = [{"name": s, "status": "verified"} for s in WITNESS_DECLS]
        a["description"] = NEW_DESCRIPTION
        a["prediction_chain"] = edges
        a["verification"] = {
            "toolchain": TOOLCHAIN,
            "libraries": LIBS,
            "verified_at": DATE,
            "verifier": verifier,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": witnesses,
        }
        a.setdefault("pa_local", 0)
        a.setdefault("pa_effective", 0)
        L["version"] = version
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(
            {
                "version": version,
                "date": DATE,
                "note": (
                    f"QBP#755 AC4: {ANCHOR_ID} CORE promoted theory→PROOF — γ(a,b) ∈ Aut(𝕆) "
                    f"(OctonionAutBranching.lean, PR #787). Witnesses gamma_mul / "
                    f"gamma_fixes_hosted / gamma_id_iff / gamma_bijective / gammaAut, all "
                    f"#print axioms ⊆ {{propext, Classical.choice, Quot.sound}} (run-bounded "
                    f"capture @ 43ae30a). Name leads with the proven γ-core; the (3,1)⊕(2,2) "
                    f"branching marked computationally-verified-only (#559), NOT claimed "
                    f"(cth seq3953 + arch F3). derived_from {edges} — from gammaAut's "
                    f"proof-term closure ∩ ledger witnesses (arch/cth confirmed seq3956/3957), "
                    f"NOT the header 'free to use' list. Also NOT claimed: 'SO(4) = full "
                    f"stabiliser of ℍ in G₂' (needs #622). Classical math; novel only as a "
                    f"CDAlg kernel formalization. AC5: claude-sonnet-5 Sonnet arm of deming's "
                    f"2026-09-30 harness, deming-verified. #697-shaped, pa 0/0. Schema co-sign "
                    f"@cth-implementor; theory co-sign @qbp-oppenheimer."
                ),
            }
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}upgraded {ANCHOR_ID} theory→proof: "
        f"headline {fq[HEADLINE]}, {len(witnesses)} witnesses, "
        f"prediction_chain {edges}; ledger {version}"
    )


if __name__ == "__main__":
    main()
