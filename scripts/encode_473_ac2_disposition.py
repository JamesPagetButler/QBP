#!/usr/bin/env python3
"""#473 AC2 disposition (beekeeper rulings 2026-09-05) + Prop 16 proof anchor — ledger encoder.

Adds to the CTH ledger (idempotent on foundation_batch == "#473-ac2"):
  * KILLED-locale-forcing-route        — status `killed`: the condensed/locale route cannot force a vacuum
                                          measure or a dynamical rule (Prop 12 ratified 2026-09-05).
  * REF-adams-hopf-invariant-one        — Adams (1960): S^{n-1} is an H-space only for n = 1, 2, 4, 8 — the
                                          non-existence direction neither the Lean tower-termination theorem
                                          nor the Agda S³ H-space witnesses.
  * PROOF-no-autonomous-algebraic-dynamics — Lean anchor for proofs/QBP/Foundations/NoAutonomousDynamics.lean
                                          (Prop 16 (i) and the invariant-subspace half of (ii)).
and appends a dated note to INSIGHT-locale-condensed-chain (spatial claim stays coherent; forcing extension
killed). Manifest entries for the proof anchor. Nothing else in the ledger is modified.
Usage: python3 scripts/encode_473_ac2_disposition.py   (repo root)
"""

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)
MANIFEST = os.path.join(ROOT, "docs/cth/anchor-worthy-manifest.json")
BATCH = "#473-ac2"
STAMP = "2026-09-05T00:00:00Z"
CLEAN = ["propext", "Classical.choice", "Quot.sound"]
PROOF_FILE = "proofs/QBP/Foundations/NoAutonomousDynamics.lean"
NS = "QBP.Foundations.NoAutonomousDynamics."
WITS = [
    "genBy_mem_span",
    "genBy_unit_imag_eq",
    "genByPair_ell_mem_quatSpan",
    "quatSpan_mul_closed",
    "quatSpan_conj_closed",
    "quatSpan_proper",
    "assoc_self_ell",
    "ell_sq",
    "p_ell_anticomm",
    "p_sq",
    "p_mul_ell_p",
    "ell_p_mul_p",
    "ell_p_sq",
    "cdLo_ell_commutator",
    "cdHi_ell_commutator",
    "cdHi_ell_commutator_imaginary",
]

KILLED = {
    "id": "KILLED-locale-forcing-route",
    "name": "The condensed/locale route cannot force a vacuum measure or a dynamical rule (#473 AC2, Prop 12 ratified 2026-09-05)",
    "tier": 3,
    "provenance": "T",
    "status": "killed",
    "description": (
        "#473 AC2 first pass (PR #631 v0.4 Prop 12; beekeeper ratification 2026-09-05). The specific path "
        "'locales/condensed sets ⇒ a forced measure on S¹⁴ and a forced dynamical rule' is dead: (1) an "
        "algebra-native locale built from ℝ + Cayley–Dickson data relocates the mystery (Prop 8); (2) a "
        "non-native tower transports a measure only through a chosen chart, and the sole algebra-native cover "
        "of the vacuum S² — the S₃-orbifold S²(2,2,3) — pushes down no measure (Props 10′, 15); (3) the algebra "
        "supplies the metric N and the potential δ² but no autonomous dynamics toward the vacuum (Prop 16, "
        "three layers: one element trivial; the forced pair (s, ℓ) a quaternion subalgebra reaching only ±ℓ; "
        "an unforced pair a norm-failure transient onto the zero-divisor ridge, then a symmetry — layer (ii)'s "
        "'only ±ℓ reachable' and layer (iii) are NUMERICAL, not Lean; Prop 15's vacuum S² is elementary/numerical, "
        "#634 AC3), and nothing "
        "in a frame, locale or condensed set selects among quench / anneal / ℓ-axis, which give different "
        "numbers from the same measure (Prop 9). With the horn-1 ruling (initial ensemble = MaxEnt relative "
        "to the algebra's constraints = N's surface measure, PERMITTED) the measure half is closed by a "
        "postulate, so the kill rests on the rule. Reversal (Prop 13, clause (b) only): a mechanism that "
        "supplies the rule from topological or measure-theoretic data. SCOPE: this kills the FORCING "
        "extension of the chain, not its mathematics — the spatial first link is PROVED "
        "(PROOF-spatial-first-link-condensed-locale); CONJ-condensed-math-for-transition-state and "
        "INSIGHT-condensed-math-deferred stay marginal (their machinery is the candidate framework for AC1-hosting "
        "clause (c), #639). Substrate FORCED/PERMITTED status unchanged (PERMITTED, 2026-06-01)."
    ),
    "prediction_chain": [],
    "provenance_kind": "internal-compute",
    "foundation_batch": BATCH,
    "last_tested_at": STAMP,
}
ADAMS = {
    "id": "REF-adams-hopf-invariant-one",
    "name": "Adams (1960): On the non-existence of elements of Hopf invariant one — S^{n−1} is an H-space only for n = 1, 2, 4, 8",
    "tier": 2,
    "provenance": "T",
    "status": "coherent",
    "description": (
        "J. F. Adams, 'On the non-existence of elements of Hopf invariant one', Ann. of Math. 72 (1960) 20–104. "
        "The sphere S^{n−1} admits an H-space structure only for n = 1, 2, 4, 8 — the topological twin of Hurwitz's "
        "uniqueness theorem for normed division algebras. Role in the ledger (#473 rounds 13–15, PR #634): the "
        "NON-EXISTENCE direction that neither PROOF-normed-division-tower-existence (existence + termination of "
        "composition algebras, Lean) nor the Agda S³ H-space (existence, Buchholtz–Rijke port) witnesses. "
        "Prop 7′'s 'what breaks at dimension 16' (norm no longer multiplicative) is the fact both non-existence "
        "results — Hurwitz and Adams — witness; S¹⁵ is not an H-space. Cited, not re-proved."
    ),
    "prediction_chain": [],
    "provenance_kind": "theory-external",
    "foundation_batch": BATCH,
    "last_tested_at": STAMP,
}
PROOF16 = {
    "id": "PROOF-no-autonomous-algebraic-dynamics",
    "name": "No autonomous algebraic dynamics: words in one imaginary s lie in span{1,s}; {1,ℓ,p,ℓp} is a quaternion subalgebra",
    "tier": 1,
    "provenance": "T",
    "status": "coherent",
    "description": (
        "#473 AC1 v0.4/v0.5 Prop 16, PR #634, research-thread evidence. (i) For every imaginary s ∈ CDAlg ℝ n, "
        "every element obtained from s by the algebra's operations (products in any bracketing, conjugation, "
        "real scalars) lies in span{1, s} (genBy_mem_span, induction on an inductive closure GenBy from "
        "imaginary_sq; no power-associativity needed); an imaginary unit in that span is ±s (genBy_unit_imag_eq). "
        "(ii) In the sedenions, for ℓ = e₈ and p = s − s₈·ℓ: span{1, ℓ, p, ℓp} is a *-subalgebra closed under "
        "multiplication (quatSpan_mul_closed, quatSpan_conj_closed) and every word in {1, s, ℓ} lies in it "
        "(genByPair_ell_mem_quatSpan); the non-associative products are derived, not assumed, from assoc_self_ell "
        "([x, x, ℓ] = 0 for EVERY sedenion — a genuine fact about ℓ, 64-case kernel decide — the sedenion alternator "
        "is nonzero in general) with p·(ℓp) = N(p)·ℓ, (ℓp)·p = −N(p)·ℓ, (ℓp)² = −N(p)·1; non-vacuity witness "
        "quatSpan_proper. Commutator in CD coordinates: [s, ℓ] = −2c + 2aℓ (cdLo/cdHi_ell_commutator). SCOPE "
        "(docstring): the shape-invariant half of (ii) — σ = V/(1−b₀²)² constant, hence only ±ℓ reachable — is "
        "NOT formalised (numerical, lmaps_check.py); normalisation is not an algebra operation, so the "
        "(s+ℓ)/‖s+ℓ‖ map is outside the closure; layer (iii) — with an unforced t the maps x·t, t·x, [x,t] are "
        "power iteration of linear skew maps onto the zero-divisor ridge, Σσ²(R_t) = 16·N(t) — is numerical "
        "(generic_maps_check.py). Not a substrate claim; no Substrate/ file."
    ),
    "prediction_chain": [],
    "provenance_kind": "proof",
    "proof_system": "lean4",
    "proof_language": "lean4",
    "proof_file": PROOF_FILE,
    "sorry_count": 0,
    "proof_state": "verified",
    "lean_theorem": NS + WITS[0],
    "lean_companion_theorems": [NS + w for w in WITS[1:]],
    "theorems": [{"name": w, "status": "verified"} for w in WITS],
    "foundation_batch": BATCH,
    "last_tested_at": STAMP,
    "verification": {
        "toolchain": "leanprover/lean4:v4.30.0",
        "libraries": {
            "mathlib": {
                "ref": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
                "sha": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            },
            "batteries": {
                "ref": "main",
                "sha": "32dc18cde3684679f3c003de608743b57498c56f",
            },
        },
        "verified_at": STAMP,
        "verifier": "lake build QBP.Foundations.NoAutonomousDynamics + #print axioms (51 declarations), leanprover/lean4:v4.30.0 (qbp-oppenheimer + lean-prover agent, #634); Red Team round-4 confirmer rebuilt; pending cth §I4",
        "result": "verified",
        "axiom_closure": CLEAN,
    },
}
NOTE = (
    " UPDATE 2026-09-05 (#473, PR #631/#634, beekeeper rulings): the spatial first link is now PROVED in Lean "
    "(PROOF-spatial-first-link-condensed-locale) — this entry's spatial claim stays coherent and the Cantor "
    "calculation was never load-bearing. The FORCING extension ('the pointless case gates the physics path' as a "
    "route to a forced measure/rule) is KILLED (KILLED-locale-forcing-route; Prop 12 ratified). The pointless / "
    "in-flight regime itself is re-scoped as a HOSTING question — AC1 (hosting) clause (c), #639 — where "
    "circularity with the algebra is permitted."
)


def main():
    src = open(os.path.join(ROOT, PROOF_FILE), encoding="utf-8").read()
    missing = [
        w
        for w in WITS
        if f"theorem {w} " not in src
        and f"theorem {w}\n" not in src
        and f"theorem {w} :" not in src
    ]
    if missing:
        sys.exit(f"witnesses not found in {PROOF_FILE}: {missing}")
    ledger = json.load(open(LEDGER, encoding="utf-8"))
    anchors = ledger["anchors"]
    anchors[:] = [a for a in anchors if a.get("foundation_batch") != BATCH]
    for a in anchors:
        if a["id"] == "INSIGHT-locale-condensed-chain":
            a["description"] = a["description"].split(" UPDATE 2026-09-05")[0] + NOTE
            a["last_tested_at"] = STAMP
            n = (a.get("notes") or "").split(" [2026-09-05:")[0]
            a["notes"] = (
                n
                + " [2026-09-05: superseded on the forcing reading — see KILLED-locale-forcing-route; the pointless / "
                "in-flight regime is now AC1-hosting clause (c), #639.]"
            )
    anchors += [KILLED, ADAMS, PROOF16]
    json.dump(ledger, open(LEDGER, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    open(LEDGER, "a", encoding="utf-8").write("\n")
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    entries = [e for e in manifest["entries"] if e.get("declared_by") != BATCH]
    entries.append(
        {
            "anchor_id": PROOF16["id"],
            "proof_system": "lean4",
            "declared_by": BATCH,
            "witnesses": [NS + w for w in WITS],
        }
    )
    manifest["entries"] = entries
    json.dump(
        manifest, open(MANIFEST, "w", encoding="utf-8"), ensure_ascii=False, indent=2
    )
    open(MANIFEST, "a", encoding="utf-8").write("\n")
    print(
        f"ledger: +3 anchors (batch {BATCH}), 1 note; anchors now {len(anchors)}; manifest entries {len(entries)}"
    )


if __name__ == "__main__":
    main()
