#!/usr/bin/env python3
"""Issue #464 Phase C — the last QBP-side #464 leg: the 5 ANCHOR rows from
`analysis/464-anchor-cohort-plan.md` (PR #766 `f5ae480`), landed as ONE Tier-3 encoder
PR with three confined commits in the order C -> B -> A so every prediction_chain edge
resolves when it is written.

Theory axis: @qbp-oppenheimer signs the five statements on the PR; AC4 (inverse-anchor
audit re-run, expected orphans=37) is his after merge. Schema axis: @cth-implementor
co-signs the ONE new anchor id (Cohort B fallback) under R6.

COHORT DECISION (live-test seq 3928, qbp-oppenheimer): Cohort B takes the **fallback** —
mint the new anchor `PROOF-cd-trace-swap-identity` rather than extend
`PROOF-cd-product-formula`. Rationale: one-statement-per-anchor; the swap lemmas are a
derived trace identity, not the doubling-product statement. Knock-on (cth seq 3933,
concur): the swap identity now lives in the new anchor, so

  * Cohort A derives the swap identity from `PROOF-cd-trace-swap-identity` (NOT from
    `PROOF-cd-product-formula`, which it still derives `cdAlg_sq_eq` from); and
  * the two swap-lemma consumers (order-three-automorphism, leaf-foliation) edge to the
    new anchor, not to `PROOF-cd-product-formula`;
  * `PROOF-cd-product-formula` is NOT extended at all in the fallback world.

A/C **extend** existing anchors -> their composite import-closure manifests MOVE @ the
source_sha, marking prior PA/notarisation stale (notary#3 AC3 re-notarise path, A+C only).
B **fresh-mints** -> its own fresh manifest, no prior PA to stale. EffectivePA of B =
min(B, {cd-product-formula, norm-form-bilinear}); a parent is never re-graded by gaining
a dependent (floor is over dependencies, never dependents).

Schema: templated exactly on the cth-§I4-accepted `encode_697_leaf_foliation_anchor.py`
shape (verification{toolchain,libraries,verified_at,verifier,result,axiom_closure,
witnesses}; theorems[]; pa 0/0 ungraded). The #619-era A/C anchors carry no inline
source_sha/proof_assistants and the blessed #697 shape adds neither — those live in the
Notary PA layer (derived from evidence_ref, never typed), so this encoder does not
introduce them inline.

CAPTURE GATE (CLAUDE.md pre-run-resource-estimate + oppenheimer seq 3928 "one Lean
process on this box"): the `#print axioms` closures for the five theorems are captured by
ONE `run-bounded 6G` `lake env lean` elaboration AFTER oppenheimer's "#755 build done"
line here, or in the post-reboot window — NOT concurrently with his #755 lean-prover
build. The capture writes a JSON {theorem: [axioms...]} to --axioms-file; this encoder
asserts every new theorem's closure is a subset of {propext, Classical.choice,
Quot.sound} (C3-FULL) before it will mint. Until the capture lands, CAPTURE_PROVENANCE is
the "CAPTURE-PENDING" sentinel and a non-dry run refuses.

Usage:
  # staging / confinement validation (no capture needed):
  python3 scripts/encode_464_phasec_anchors.py --cohort C --dry-run
  python3 scripts/encode_464_phasec_anchors.py --cohort B --dry-run
  python3 scripts/encode_464_phasec_anchors.py --cohort A --dry-run
  # real mint, one commit per cohort, in order C then B then A:
  python3 scripts/encode_464_phasec_anchors.py --cohort C --axioms-file <capture.json>
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

PREV_VERSION = "6.19.0"
NEW_VERSION = (
    "6.20.0"  # bumped on the first cohort run (C); B/A do not re-touch version
)
DATE = "2026-10-29T00:00:00Z"  # capture date; updated to the real run date at mint time
BATCH = "#464-phase-c"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

LIBS = {
    "mathlib": {
        "ref": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "sha": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
    },
    "batteries": {"ref": "main", "sha": "32dc18cde3684679f3c003de608743b57498c56f"},
}

# --- capture provenance -----------------------------------------------------------
# Filled with the real run-bounded command + results AFTER the #print axioms capture.
# While it equals the sentinel, a non-dry mint is refused (guards against minting with
# placeholder provenance). FILLED 2026-10-29 from the lean-prover capture (PASS).
CAPTURE_PENDING = "CAPTURE-PENDING"
CAPTURE_PROVENANCE = (
    "capture 2026-10-29 @ head 539f7456 (branch qbp/464-phase-c-anchors off master "
    "539f745): run-bounded 6G 1200 taskset -c 2-6 lake build QBP.Foundations."
    "{ArtinTrace,ArtinSpan,ArtinCore} (peak RSS 4.86 GiB, wall 3:34, exit 0, 2952 jobs) "
    "+ run-bounded 6G 1200 lake env lean <scratch> (peak 3.31 GiB, wall 4.3s, exit 0); "
    "#print axioms on all five theorems captured to analysis/464-phasec-axioms.json, "
    "every closure = {propext, Classical.choice, Quot.sound} (C3-FULL PASS, no sorryAx / "
    "ofReduceBool / native_decide)"
)

NS = "QBP.Foundations.CDAlg."

# theorem -> source file it is declared in (witness-resolution guard greps this file)
THM_FILE = {
    "span4_mul_closed": "proofs/QBP/Foundations/ArtinSpan.lean",
    "assoc_vanishes_on_span4": "proofs/QBP/Foundations/ArtinCore.lean",
    "cdAlg_mul_add_swap": "proofs/QBP/Foundations/ArtinTrace.lean",
    "cdAlg_mul_add_swap_pure": "proofs/QBP/Foundations/ArtinTrace.lean",
    "N_add": "proofs/QBP/Foundations/ArtinTrace.lean",
}

# ======================================================================================
# COHORT SPECS
# ======================================================================================
# Each cohort: either an "extend" (mutate an existing anchor) or a "mint" (new anchor),
# plus "consumer_edges": {consumer_id: edge_id_to_append_to_its_prediction_chain}.

COHORTS = {
    # --- Cohort C: extend PROOF-norm-form-bilinear (+N_add) --------------------------
    "C": {
        "kind": "extend",
        "anchor": "PROOF-norm-form-bilinear",
        "add_theorems": ["N_add"],
        "add_companions": [NS + "N_add"],
        "add_derived_from": [],  # none (polarization of N = bil is already its content)
        "scope_sentence": (
            " Also witnesses the additive polarization N(x+y) = N x + N y + 2⟨x,y⟩ over ℝ "
            "(CDAlg.N_add; a general-CommRing copy lives at CrossProduct.N_add)."
        ),
        "consumer_edges": {
            "PROOF-octonion-zd-hypersurface-empty": "PROOF-norm-form-bilinear",
            "PROOF-rule-field-in-kernel-algebra-leaf-foliation": "PROOF-norm-form-bilinear",
            # 3rd consumer (the new cd-trace-swap anchor) is realized by its own mint in B.
        },
        "changelog_note": (
            f"#464 Phase C / cohort C: PROOF-norm-form-bilinear extended with CDAlg.N_add "
            "(ArtinTrace.lean:57), the additive polarization of the CD norm; the qualified "
            "name is required (bare N_add also names CrossProduct.N_add). Consumers "
            "octonion-zd-hypersurface-empty and rule-field-in-kernel-algebra-leaf-foliation "
            "gain a derived_from edge to it. #print axioms on the added theorem captured "
            "under run-bounded, closure ⊆ {propext, Classical.choice, Quot.sound}. No "
            "provenance_kind / proof_file / status change. Composite import-closure manifest "
            "for this anchor MOVES @ this source_sha (prior PA stale; notary#3 AC3 re-"
            "notarise). Theory-axis co-sign @qbp-oppenheimer."
        ),
    },
    # --- Cohort B: MINT PROOF-cd-trace-swap-identity (fallback) ----------------------
    "B": {
        "kind": "mint",
        "anchor": "PROOF-cd-trace-swap-identity",
        "name": (
            "Cayley-Dickson trace/swap polarization identity. For x, y ∈ CDAlg ℝ n: "
            "x·y + y·x = (2 Re x)·y + (2 Re y)·x − 2⟨x,y⟩·1 (cdAlg_mul_add_swap); and for "
            "Re x = Re y = 0, x·y + y·x = −2⟨x,y⟩·1 (cdAlg_mul_add_swap_pure). Over ℝ only."
        ),
        "proof_file": "proofs/QBP/Foundations/ArtinTrace.lean",
        "headline": "cdAlg_mul_add_swap",
        "companions_bare": ["cdAlg_mul_add_swap_pure"],
        "prediction_chain": ["PROOF-cd-product-formula", "PROOF-norm-form-bilinear"],
        "description": (
            "proofs/QBP/Foundations/ArtinTrace.lean (Foundations layer, namespace "
            "QBP.Foundations.CDAlg). The polarization of the square law at every level n: "
            "x·y + y·x = (2 Re x)·y + (2 Re y)·x − 2⟨x,y⟩·1 (cdAlg_mul_add_swap, "
            "ArtinTrace.lean:86), and its pure-imaginary specialization x·y + y·x = "
            "−2⟨x,y⟩·1 for Re x = Re y = 0 (cdAlg_mul_add_swap_pure, ArtinTrace.lean:120). "
            "Both stated for CDAlg ℝ n (over ℝ only). derived_from: PROOF-cd-product-formula "
            "(the doubling product / square law cdAlg_sq_eq the identity polarizes) and "
            "PROOF-norm-form-bilinear (the bilinear form ⟨x,y⟩ = bil x y it is stated in; "
            "N_add, Cohort C). FALLBACK MINT (oppenheimer seq 3928): split out of "
            "PROOF-cd-product-formula to keep one statement per anchor — the swap identity "
            "is a derived trace identity, not the doubling-product statement. Side effect "
            "(U5, cohort-plan): the inverse-anchor audit's file-level match for "
            "ArtinTrace.lean now also covers reCoord_add and mul_self_add; that is the "
            "coarse file-granularity semantics the report already labels a lower bound. "
            "NOT claimed: any statement about 𝕊-specific behaviour beyond the general-n form; "
            "the Artin assembly (PROOF-artin-theorem, which consumes this). PA 0/0, ungraded "
            "— no Notary proof-assistant evidence recorded yet (QBP#710 'ungraded' state)."
        ),
        "consumer_edges": {
            "PROOF-order-three-automorphism-fixes-ell": "PROOF-cd-trace-swap-identity",
            "PROOF-rule-field-in-kernel-algebra-leaf-foliation": "PROOF-cd-trace-swap-identity",
            # 3rd consumer (PROOF-artin-theorem) edges to it via A's own derived_from in A.
        },
        "changelog_note": (
            f"#464 Phase C / cohort B (FALLBACK, oppenheimer seq 3928): minted "
            "PROOF-cd-trace-swap-identity (Foundations) for the two trace/swap polarization "
            "lemmas cdAlg_mul_add_swap (ArtinTrace.lean:86) and cdAlg_mul_add_swap_pure "
            "(:120), split out of PROOF-cd-product-formula to keep one statement per anchor. "
            "prediction_chain [PROOF-cd-product-formula, PROOF-norm-form-bilinear]. Consumers "
            "order-three-automorphism-fixes-ell and rule-field-in-kernel-algebra-leaf-"
            "foliation edge to it. #print axioms on both theorems captured under run-bounded, "
            "closure ⊆ {propext, Classical.choice, Quot.sound}. Schema-axis co-sign "
            "@cth-implementor (R6, new id); theory-axis co-sign @qbp-oppenheimer. Fresh mint "
            "— no prior PA; EffectivePA = min(self, parents). Audit side effect: "
            "ArtinTrace.lean file match now also covers reCoord_add/mul_self_add (U5)."
        ),
    },
    # --- Cohort A: extend PROOF-artin-theorem (+2) -----------------------------------
    "A": {
        "kind": "extend",
        "anchor": "PROOF-artin-theorem",
        "add_theorems": ["span4_mul_closed", "assoc_vanishes_on_span4"],
        "add_companions": [NS + "span4_mul_closed", NS + "assoc_vanishes_on_span4"],
        # swap-identity edge re-targeted to the new anchor per the fallback (seq 3928/3933)
        "add_derived_from": [
            "PROOF-ops-alternativity-ladder",
            "PROOF-ops-flexibility-ladder",
            "PROOF-cd-product-formula",
            "PROOF-cd-trace-swap-identity",
        ],
        "scope_sentence": (
            " Also witnesses the two halves the proof assembles, for every pair x, y ∈ 𝕆: "
            "span ℝ {1,x,y,x·y} is closed under the product (span4_mul_closed) and the "
            "associator vanishes on it (assoc_vanishes_on_span4). NOT claimed: dim span = 4 "
            "(no independence hypothesis), or any statement about 𝕊."
        ),
        "consumer_edges": {
            "PROOF-quaternion-frame-maximal": "PROOF-artin-theorem",
            "PROOF-quatdouble-rho-invariant-mul-closed": "PROOF-artin-theorem",
            "PROOF-octonion-perp-module-span4-maximal": "PROOF-artin-theorem",
            "PROOF-associative-composition-iff": "PROOF-artin-theorem",
            "PROOF-gradient-lies-in-host-kernel-algebra": "PROOF-artin-theorem",
        },
        "changelog_note": (
            f"#464 Phase C / cohort A: PROOF-artin-theorem extended with span4_mul_closed "
            "(ArtinSpan.lean:312) and assoc_vanishes_on_span4 (ArtinCore.lean:349) — the two "
            "halves (product closure + associator vanishing on span ℝ {1,x,y,x·y}) the Artin "
            "proof assembles. derived_from set to [PROOF-ops-alternativity-ladder, "
            "PROOF-ops-flexibility-ladder, PROOF-cd-product-formula (cdAlg_sq_eq), "
            "PROOF-cd-trace-swap-identity (the swap identity, re-targeted to the Cohort-B "
            "fallback anchor)]; NOT PROOF-octonion-moufang (never invoked — cohort-plan "
            "flexibility-edge resolution). Five consumers "
            "(quaternion-frame-maximal, quatdouble-rho-invariant-mul-closed, "
            "octonion-perp-module-span4-maximal, associative-composition-iff, "
            "gradient-lies-in-host-kernel-algebra) gain a derived_from edge to it. #print "
            "axioms on both added theorems captured under run-bounded, closure ⊆ {propext, "
            "Classical.choice, Quot.sound}. Composite import-closure manifest MOVES @ this "
            "source_sha (prior PA stale; notary#3 AC3 re-notarise). Theory-axis co-sign "
            "@qbp-oppenheimer."
        ),
    },
}


def git_grep_resolves(thm, rel):
    """True iff `theorem <thm>` or `lemma <thm>` is declared in the working-tree file."""
    p = ROOT / rel
    if not p.exists():
        return False
    for line in p.read_text(encoding="utf-8").splitlines():
        s = line.lstrip()
        if s.startswith(f"theorem {thm}") or s.startswith(f"lemma {thm}"):
            return True
    return False


def build_verifier(cohort_key, thms):
    """Capture-provenance string. CAPTURE_PROVENANCE holds the real run-bounded command +
    peak RSS + head sha + the C3-FULL result; main() refuses a non-dry mint while it is
    still the CAPTURE-PENDING sentinel."""
    thm_list = ", ".join(thms)
    return (
        f"#464 Phase C cohort {cohort_key} (qbp-implementor writer lane). {CAPTURE_PROVENANCE}. "
        f"Theorems added this cohort: {{{thm_list}}}. Theory-axis co-sign qbp-oppenheimer"
        + (
            "; schema-axis co-sign cth-implementor (R6, new id)."
            if cohort_key == "B"
            else "."
        )
    )


def load_axiom_closures(axioms_file):
    if axioms_file is None:
        return None
    data = json.loads(Path(axioms_file).read_text())
    return {k: set(v) for k, v in data.items()}


def assert_c3_full(thms, closures, dry_run):
    """C3-FULL: each new theorem's #print axioms closure ⊆ ALLOWED_AXIOMS."""
    if closures is None:
        if not dry_run:
            raise SystemExit(
                "C3-FULL: --axioms-file required for a real mint (the captured "
                "#print axioms closures). Run the run-bounded capture first."
            )
        print(f"  [dry-run] C3-FULL skipped (no --axioms-file) for: {thms}")
        return
    for t in thms:
        if t not in closures:
            raise SystemExit(f"C3-FULL: {t} missing from captured axioms file")
        extra = closures[t] - ALLOWED_AXIOMS
        if extra:
            raise SystemExit(
                f"C3-FULL: {t} closure has disallowed axioms {sorted(extra)}"
            )
    print(f"  C3-FULL OK: {thms} all ⊆ {{propext, Classical.choice, Quot.sound}}")


def apply_consumer_edges(ed, edges):
    for consumer, edge in edges.items():
        rec = ed.record("anchors", consumer)
        chain = rec.setdefault("prediction_chain", [])
        if edge in chain:
            raise SystemExit(
                f"consumer {consumer} already has edge {edge} — the cohort plan expected a "
                f"fresh append; investigate before minting (silent no-op would abort anyway)"
            )
        chain.append(edge)


def do_extend(ed, spec, closures, dry_run):
    bare = spec["add_theorems"]
    assert_c3_full(bare, closures, dry_run)
    a = ed.record("anchors", spec["anchor"])
    # theorems[]
    have = {t["name"] for t in a["theorems"]}
    for t in bare:
        if t not in have:
            a["theorems"].append({"name": t, "status": "verified"})
    # lean_companion_theorems
    comp = a.setdefault("lean_companion_theorems", [])
    for c in spec["add_companions"]:
        if c not in comp:
            comp.append(c)
    # description scope sentence (append once)
    if spec["scope_sentence"].strip() not in a["description"]:
        a["description"] = a["description"].rstrip() + spec["scope_sentence"]
    # prediction_chain
    chain = a.setdefault("prediction_chain", [])
    for d in spec["add_derived_from"]:
        if d not in chain:
            chain.append(d)
    # verification: update capture provenance + add witnesses for the new theorems
    v = a["verification"]
    v["verified_at"] = DATE
    v["verifier"] = build_verifier(
        [k for k, s in COHORTS.items() if s is spec][0], bare
    )
    v["libraries"] = LIBS
    w = v.setdefault("witnesses", [])
    for c in spec["add_companions"]:
        if c not in w:
            w.append(c)
    apply_consumer_edges(ed, spec["consumer_edges"])


def do_mint(ed, spec, closures, dry_run):
    bare = [spec["headline"]] + [c.split(".")[-1] for c in spec["companions_bare"]]
    assert_c3_full(bare, closures, dry_run)
    have = {a["id"] for a in ed.ledger["anchors"]}
    if spec["anchor"] in have:
        raise SystemExit(f"already applied: {spec['anchor']} present")
    for d in spec["prediction_chain"]:
        if d not in have:
            raise SystemExit(f"derived_from target missing from ledger: {d}")
    companions = [NS + c for c in spec["companions_bare"]]
    witnesses = [NS + spec["headline"]] + companions
    rec = {
        "id": spec["anchor"],
        "name": spec["name"],
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": spec["description"],
        "proof_file": spec["proof_file"],
        "proof_language": "lean4",
        "proof_state": "verified",
        "lean_theorem": NS + spec["headline"],
        "lean_companion_theorems": companions,
        "sorry_count": 0,
        "provenance": "T",
        "prediction_chain": list(spec["prediction_chain"]),
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": LIBS,
            "verified_at": DATE,
            "verifier": build_verifier("B", bare),
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": witnesses,
        },
        "theorems": [{"name": t, "status": "verified"} for t in bare],
        "pa_local": 0,
        "pa_effective": 0,
    }
    ed.append("anchors", rec)
    apply_consumer_edges(ed, spec["consumer_edges"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cohort", required=True, choices=["C", "B", "A"])
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument(
        "--axioms-file",
        help="JSON {theorem: [axioms...]} from the run-bounded #print axioms capture",
    )
    args = ap.parse_args()
    spec = COHORTS[args.cohort]

    if not args.dry_run and CAPTURE_PROVENANCE == CAPTURE_PENDING:
        raise SystemExit(
            "CAPTURE_PROVENANCE is still the CAPTURE-PENDING sentinel — fill it with the "
            "real run-bounded command/results after the #print axioms capture before a real "
            "mint. (Dry-run is allowed for confinement validation.)"
        )

    # Witness-resolution guard: every cited new theorem resolves in its named file.
    new_thms = (
        spec["add_theorems"]
        if spec["kind"] == "extend"
        else [spec["headline"]] + spec["companions_bare"]
    )
    for t in new_thms:
        rel = THM_FILE[t]
        if not git_grep_resolves(t, rel):
            raise SystemExit(f"witness does not resolve in {rel}: {t}")

    closures = load_axiom_closures(args.axioms_file)

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        if args.cohort == "C":
            if L.get("version") != NEW_VERSION:
                L["version"] = NEW_VERSION
                ed.touch("version")
            if L.get("last_updated") != DATE:
                L["last_updated"] = DATE
                ed.touch("last_updated")
        if spec["kind"] == "extend":
            do_extend(ed, spec, closures, args.dry_run)
        else:
            do_mint(ed, spec, closures, args.dry_run)
        L["changelog"].append(
            {"version": NEW_VERSION, "date": DATE, "note": spec["changelog_note"]}
        )
        ed.touch("changelog")

    print(
        f"{'DRY ' if args.dry_run else ''}cohort {args.cohort} "
        f"({spec['kind']} {spec['anchor']}): new theorems {new_thms}, "
        f"consumer edges {list(spec['consumer_edges'])}; ledger {NEW_VERSION}"
    )


if __name__ == "__main__":
    main()
