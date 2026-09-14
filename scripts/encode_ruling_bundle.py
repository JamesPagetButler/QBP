#!/usr/bin/env python3
"""Encode the ruling bundle (PR #652) into the CTH ledger — ONE constitutional PR, shape A.

RUNS ONLY AFTER THE BEEKEEPER RULES Decisions 0–5 on PR #652. Parameters below carry the rulings;
the script refuses to run while MERGED_652 is False (the #652 merge is a process acceptance of the v0.4 sort, not a ruling). Idempotent (guards on DERIV-encoding-level's presence).

What it applies (package v0.6 §3 + ruling page v0.2 §2–§5), all previously drafted texts:
  D5  META-2 level saturation → new top-level list `meta_principles` (the schema pins `meta_axiom` to a single
      object, so META-2 cannot be appended there; `additionalProperties: true` at top level admits the new key);
      POST-hosting (final form) → `axioms` (it is the second physical axiom, package §2a);
      DERIV-encoding-level replaces AXIOM-2 (moved to `retired_axioms` with the demotion note);
      DERIV-substrate-level (with the level-generic crystal definition);
      DERIV-sedenion `derived_from` inverted → [DERIV-substrate-level, DERIV-encoding-level] (clause already option B, #651).
  D2  DERIV-holographic → POST-observer-associativity + POST-observation (→ `axioms`), DERIV-holographic-theorem and
      INTERP-holographic-boundary (→ new top-level list `interpretations`; the schema pins derived_principles ids to ^DERIV-);
      the 5 dependents + 3 chained anchors + CHAIN-born-to-revival + the flag-3 anchor descriptions re-pointed.
  D1  READING selects the INTERP text and the DERIV-sedenion first clause.
  D3  the three names are used in every new text.
  re-pointing of the 14 AXIOM-2-citing anchors and the 7 "Axioms ->" chains' source_ids.
Usage: python3 scripts/encode_ruling_bundle.py    (edit RULED / READING / RULING_URLS first)
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cth_ledger_edit import ledger_edit  # noqa: E402  (#654 D7: confined write)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)

# ----------------------------------------------------------------------------- rulings (fill in)
DRY_RUN = False  # True: verify confinement and print the summary, write nothing
MERGED_652 = False  # set True only when PR #652 (ruling bundle v0.4) has MERGED — a process acceptance of the sort, not a ruling; nothing here is ruled
READING = "open"  # "open" (v0.3: not decidable from the axioms — both hypotheses encoded, status open) | "P2prime" | "P2line" | "P2bundle"
ENCODE_DATE = "<date PR #652 merged>"
PAGE_URL = (
    "<URL of docs/foundations/ruling-bundle-2026-09-10.md at the #652 merge commit>"
)
# ----------------------------------------------------------------------------- texts (drafted, PR #652 v0.2)

META2 = {
    "id": "META-2",
    "name": "Level saturation",
    "statement": (
        "A structural level sits exactly at the bound its constraint sets; no slack. Domain: Cayley–Dickson levels only. "
        "It does not select states (the ensemble is MaxEnt, horn 1), copies (the ℤ/3 of encoding halves, or the ℂP² of "
        "encodings under P2), orientations, or signs."
    ),
    "kind": "epistemic principle",
    "derivable": False,
    "decision_state": "open",
    "kill_condition": [
        "A Cayley–Dickson level shown to sit strictly inside its constraint's bound — a "
        "crystal-hosting division or alternative structure above O (dim 8), or a non-crystal at "
        "a level below S (dim 16) — would break saturation and, with it, DERIV-encoding-level and "
        "DERIV-substrate-level. Discharge: none available (a positive principle about levels is "
        "not discharged by more examples); recorded OPEN. Root introduced by the AXIOM-2 "
        "demotion package (PR #648 v0.6) and the ruling bundle v0.4 §5 (PR #652)."
    ],
}
POST_HOSTING = {
    "id": "POST-hosting",
    "name": "Non-crystal states are physically realised",
    "statement": (
        "The state sphere at the substrate level carries an in-flight region V > 0 of positive measure, and almost every "
        "history starts in it. Kill (theory-internal only): a substrate level at which V ≡ 0 — the level bound failing; "
        "no observable (observers live in crystals; FLAG-seam-dynamics-open) — recorded as such, not as a pass. "
        "Convergence to a crystal is the rule's claim (#635), separate."
    ),
    "kind": "physical postulate",
    "kill_condition": [
        "A substrate level at which V ≡ 0 — the level bound failing. Theory-internal: this kill "
        "is the negation of the postulate and no observable reaches it (observers live in "
        "crystals; FLAG-seam-dynamics-open is incoherent) — it CANNOT FIRE today, recorded as "
        "such, not as a pass (package §9c; ruling bundle v0.4 §5)."
    ],
    "decision_state": "open",
    "derivable": False,
    "anchors": ["PROOF-substrate-hosting-definition", "PROOF-delta-landscape-descent"],
}
POST_ASSOC = {
    "id": "POST-observer-associativity",
    "name": "Observers require associativity",
    "statement": (
        "An observer is a subset of 𝕊 on which its actions compose; by the composition theorem such a subset is "
        "associative, and — if it lies inside an octonion — inside one ℍ by frame-maximality (in 𝕊 at large this is open). "
        "Under the hosting definition the observer's ℍ is the crystal's ℍ_s (definition D; premise P1′: observers are "
        "entities of clause (a)). Exclusivity — no observer lives outside the hosted algebra — is the postulate's content."
    ),
    "kind": "physical postulate",
    "kill_condition": [
        "An observer exhibited outside any associative subalgebra of S (exclusivity failing), "
        "or a non-associative subset of S on which actions compose (contradicting "
        "PROOF-associative-composition-iff's premise set). Discharge: none — a postulate about "
        "all observers; recorded OPEN (ruling bundle v0.4 §2)."
    ],
    "decision_state": "open",
    "derivable": False,
    "anchors": [
        "PROOF-associative-composition-iff",
        "PROOF-quaternion-frame-maximal",
        "PROOF-crystal-hosts-quaternion",
    ],
}
POST_OBS = {
    "id": "POST-observation",
    "name": "Observation is bounded by the encoding",
    "statement": (
        "(O⊆) What an observer can access is contained in what is encoded in its encoding octonion. "
        "(E) The electromagnetic ℂ of DERIV-observation is the ℂ selected by that encoding."
        + (
            " Under P2′ (E) has content: the selected ℂ is ℂ_u = ℍ_s ∩ (the encoding half); under P2 no ℂ is selected geometrically and DERIV-observation's ℂ is EM's own; the reading is open (INTERP-holographic-boundary)."
            if READING == "open"
            else (
                " Under the ruled reading (P2′) (E) has content: the selected ℂ is ℂ_u = ℍ_s ∩ (the encoding half)."
                if READING == "P2prime"
                else " Under the ruled reading (P2) no ℂ is selected geometrically and DERIV-observation's ℂ is EM's own."
            )
        )
    ),
    "kind": "physical postulate",
    "kill_condition": [
        "(O⊆) An observable that requires access to information not encoded in the observer's "
        "encoding octonion. Recorded OPEN.",
        "(E) An electromagnetic C shown distinct from the encoding-selected C. Has content only "
        "under P2' (where a C is selected); empty under P2 — so this entry is OPEN exactly as "
        "INTERP-holographic-boundary's P2/P2' pair is, and cannot fire before that pair is "
        "decided (ruling bundle v0.4 §2).",
    ],
    "decision_state": "open",
    "derivable": False,
    "anchors": ["PROOF-hosted-algebra-meets-cell-in-complex-line"],
}
DERIV_ENC = {
    "id": "DERIV-encoding-level",
    "name": "The encoding is the last information-preserving level",
    "statement": (
        "The encoding octonion of a universe sits at the Cayley–Dickson level below the first failure of AXIOM-1's "
        "selection: 𝕆 (dim 8) — division, norm composition and alternativity all hold through 𝕆 and all fail at 𝕊. "
        "Tower-relative ('largest in the Cayley–Dickson sequence'); the classification 'only four normed division "
        "algebras exist' (PROOF-hurwitz) is not used."
    ),
    "derived_from": ["AXIOM-1", "META-2"],
    "layer": 1,
    "anchors": [
        "PROOF-ops-division-ladder",
        "PROOF-ops-norm-composition-ladder",
        "PROOF-ops-alternativity-ladder",
        "PROOF-normed-division-tower-existence",
    ],
    "supersedes": "AXIOM-2",
}
DERIV_SUB = {
    "id": "DERIV-substrate-level",
    "name": "The substrate is the first level that hosts crystallisation",
    "statement": (
        "Definition (level-generic): a state s is a crystal iff its left alternator vanishes, assoc s s x = 0 for all x "
        "(equivalently L_s² is scalar). At 𝕊 this is equivalent to the Cayley–Dickson components of s commuting, "
        "V = ‖[a, b]‖² = 0 — an equivalence that holds at 𝕊 only; the commutator form is the 𝕊-specific computation. "
        "Statement: the substrate is the first Cayley–Dickson level at which a non-crystal exists: 𝕊 (dim 16). In every "
        "alternative algebra every state is a crystal (dimensions ≤ 8: CDLifting.assoc_diag_left at 𝕆, associativity "
        "below); at 𝕊 a non-crystal exists (sedWitX_alternator_ne_zero, inFlight_nonempty)."
    ),
    "derived_from": ["POST-hosting", "META-2"],
    "layer": 1,
    "anchors": [
        "PROOF-ops-alternativity-ladder",
        "PROOF-alternator-vanishes-iff-commute",
        "PROOF-substrate-hosting-definition",
    ],
}
DERIV_HOLO_THM = {
    "id": "DERIV-holographic-theorem",
    "name": "Quaternion frames are the maximal associative subalgebras of 𝕆 (frame-relative); codimension 4",
    "statement": (
        "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra of 𝕆 properly "
        "contains one (frame-relative; the global bound is deferred); the codimension of ℍ in 𝕆 is 4."
    ),
    "derived_from": ["DERIV-encoding-level"],
    "layer": 1,
    "anchors": [
        "PROOF-associative-composition-iff",
        "PROOF-quaternion-frame-maximal",
        "PROOF-quaternion-frame-codim-four",
    ],
    "supersedes": "DERIV-holographic (theorem part)",
}
INTERP_COMMON = (
    "There is a boundary encoding: each universe has an encoding octonion (the algebra AXIOM-2 referred to, now "
    "DERIV-encoding-level), and the holographic gap is the complement of the observer's algebra inside it; the seam "
    "boundary between universes is the zero-divisor locus (DERIV-sedenion). "
)
INTERP_VARIANT = {
    "open": "Which octonion encodes a universe is NOT decided by the axioms: the algebra does not pick a copy (the "
    "ℓ-fixing order-3 automorphism permutes the three Cayley–Dickson halves, PROOF-order-three-automorphism-fixes-ell; "
    "nothing selects a point of the ℂP² of octonions around ℍ_s). Two hypotheses, status open: P2′ — the encoding "
    "is a Cayley–Dickson half (one of three; ℍ_s meets it in ℂ_u, PROOF-hosted-algebra-meets-cell-in-complex-line; "
    "the gap is 6-dim; a discrete datum); P2 — the encoding is an octonion containing ℍ_s (a ℂP² of them, completeness "
    "a conjecture; the gap is 4-dim; or the datum-free bundle form ℍ_s^⊥ ≅ ℍ_s³). Decides it: a defining property for "
    "AXIOM-2's encoding stated as an object; the encoding map; or an observable — none on record.",
    "P2prime": "The encoding octonion is a Cayley–Dickson half, one of three (the ℓ-fixing order-3 automorphism permutes them, "
    "PROOF-order-three-automorphism-fixes-ell), a discrete datum of the universe; ℍ_s meets it in ℂ_u "
    "(PROOF-hosted-algebra-meets-cell-in-complex-line); DERIV-holographic-theorem describes the frame inside the "
    "half, not the observer's algebra, which straddles the halves; the holographic gap is 6-dimensional.",
    "P2line": "The encoding octonion is an octonion 𝕆'_v ⊃ ℍ_s chosen from a ℂP² (completeness of the family is a conjecture); "
    "the holographic gap is the 4-dimensional ℍ_s^⊥ ∩ 𝕆'_v.",
    "P2bundle": "The boundary is the canonical module ℍ_s^⊥ ≅ ℍ_s³ with its cone of admissible ℍ_s-lines; no encoding is chosen.",
}
INTERP = {
    "id": "INTERP-holographic-boundary",
    "name": "The holographic gap and the seam (interpretation)",
    "statement": INTERP_COMMON + INTERP_VARIANT[READING],
    "derived_from": [
        "DERIV-encoding-level",
        "POST-observer-associativity",
        "POST-observation",
    ],
    "layer": 1,
    "kind": "interpretation",  # cth-implementor (seq 1297): INTERP = provenance_kind philosophy + decision_state; no new kind
    "supersedes": "DERIV-holographic (interpretation part)",
    "provenance_kind": "philosophy",
    "decision_state": "open" if READING == "open" else "ruled",
    "kill_condition": [
        "Which copy of O encodes a universe (P2 vs P2'): fired or discharged by a defining "
        "property of the encoding stated as an object (a Cayley–Dickson half → P2' is a theorem; "
        "contains the observer's algebra → P2 is), by the encoding MAP (a map forces its domain), "
        "or by an observable distinguishing the readings — none on record. The first two are "
        "stipulations someone would write, not discoveries. This kill CANNOT FIRE today — "
        "recorded as such, not as a pass (ruling bundle v0.4 §1; hosting §4's form)."
    ],
}
SEDENION_FIRST_CLAUSE = {
    "open": "𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of an octonion (which copy encodes a universe is open — INTERP-holographic-boundary).",
    "P2prime": "𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of the encoding half (one of three such decompositions, permuted by the order-3 automorphism).",
    "P2line": "𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of an octonion; each universe's encoding octonion is chosen around its crystal.",
    "P2bundle": "𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of an octonion.",
}
REPOINT_DERIVED = {  # derived_from replacements after the split
    "DERIV-3plus1": ["POST-observer-associativity", "DERIV-holographic-theorem"],
    "DERIV-observation": ["POST-observation", "DERIV-holographic-theorem"],
    "DERIV-pati-salam": [
        "AXIOM-1",
        "DERIV-encoding-level",
        "DERIV-holographic-theorem",
    ],
    "DERIV-arrow": [
        "AXIOM-1",
        "POST-observer-associativity",
        "INTERP-holographic-boundary",
    ],
    "DERIV-constants": ["POST-observer-associativity", "INTERP-holographic-boundary"],
    "DERIV-crystallisation-asymptotic": [
        "AXIOM-1",
        "DERIV-encoding-level",
        "DERIV-constants",
    ],
}
ANCHOR_HOLO_MAP = {  # anchors whose list fields cite DERIV-holographic
    "PROOF-3gen": ["DERIV-holographic-theorem"],
    "PRED-gw-em": ["POST-observer-associativity", "INTERP-holographic-boundary"],
    "PRED-revival-exact": [
        "POST-observer-associativity",
        "INTERP-holographic-boundary",
    ],
    "CONJ-condensed-math-for-transition-state": ["INTERP-holographic-boundary"],
    "INSIGHT-condensed-math-deferred": ["INTERP-holographic-boundary"],
    "PROOF-associative-composition-iff": ["DERIV-holographic-theorem"],
    "PROOF-quaternion-frame-maximal": ["DERIV-holographic-theorem"],
    "PROOF-quaternion-frame-codim-four": ["DERIV-holographic-theorem"],
    "PROOF-crystal-hosts-quaternion": ["DERIV-holographic-theorem"],
}
LIST_FIELDS = ("prediction_chain", "converges_with", "source_ids", "derived_from")


def replace_in_lists(obj, old, new_list):
    changed = False
    for f in LIST_FIELDS:
        if isinstance(obj.get(f), list) and old in obj[f]:
            seq = []
            for x in obj[f]:
                if x == old:
                    seq.extend(n for n in new_list if n not in seq)
                elif x not in seq:
                    seq.append(x)
            obj[f] = seq
            changed = True
    return changed


def main():
    if not MERGED_652:
        print(
            "REFUSING: MERGED_652 is False — PR #652 (v0.4) has not merged. Nothing here is ruled; the merge is the process acceptance of the sort. Edit the parameters and re-run."
        )
        sys.exit(2)
    with open(LEDGER, encoding="utf-8") as f:
        if any(
            e["id"] == "DERIV-encoding-level"
            for e in json.load(f)["derived_principles"]
        ):
            print("already applied — no change")
            return
    with ledger_edit(LEDGER, dry_run=DRY_RUN) as ed:
        _apply(ed.ledger, ed)


def _apply(L, ed):
    # D5: AXIOM-2 → retired; DERIV-encoding-level in
    ax2 = next(a for a in L["axioms"] if a["id"] == "AXIOM-2")
    L["axioms"] = [a for a in L["axioms"] if a["id"] != "AXIOM-2"]
    L.setdefault("retired_axioms", []).append(
        {
            **ax2,
            "retired": f"{ENCODE_DATE}: content restated as DERIV-encoding-level (a derivation from AXIOM-1 + META-2 + the proved ladders — not a change of axiom: nothing AXIOM-2 asserted is denied; its 'largest' clause is now META-2's, an OPEN root with a kill). Ruling bundle v0.4 §5 (PR #652, {PAGE_URL}); package docs/foundations/axiom2-demotion-proposal-2026-09-09.md v0.6.",
        }
    )
    L["axioms"].extend([POST_HOSTING, POST_ASSOC, POST_OBS])
    L["meta_principles"] = [META2]
    ed.touch("axioms", "AXIOM-2")
    ed.touch("retired_axioms", "AXIOM-2")
    for p in (POST_HOSTING, POST_ASSOC, POST_OBS):
        ed.touch("axioms", p["id"])
    ed.touch("meta_principles", META2["id"])
    # D2: DERIV-holographic → retired; four entries in
    holo = next(e for e in L["derived_principles"] if e["id"] == "DERIV-holographic")
    L["derived_principles"] = [
        e for e in L["derived_principles"] if e["id"] != "DERIV-holographic"
    ]
    L.setdefault("retired_principles", []).append(
        {
            **holo,
            "retired": f"{ENCODE_DATE}: split into POST-observer-associativity, POST-observation, DERIV-holographic-theorem, INTERP-holographic-boundary — an editorial split (one kind of statement per entry, ruling bundle v0.4 §2, PR #652, {PAGE_URL}); the theorem part is proved, the postulate and interpretation parts are OPEN roots with kill conditions.",
        }
    )
    L["derived_principles"].extend([DERIV_ENC, DERIV_SUB, DERIV_HOLO_THM])
    L["interpretations"] = [
        INTERP
    ]  # schema pins derived_principles ids to ^DERIV-; interpretations get their own list
    ed.touch("derived_principles", "DERIV-holographic")
    ed.touch("retired_principles", "DERIV-holographic")
    for d in (DERIV_ENC, DERIV_SUB, DERIV_HOLO_THM):
        ed.touch("derived_principles", d["id"])
    ed.touch("interpretations", INTERP["id"])
    # DERIV-sedenion inverted + first clause per reading
    sed = next(e for e in L["derived_principles"] if e["id"] == "DERIV-sedenion")
    ed.touch("derived_principles", "DERIV-sedenion")
    sed["derived_from"] = ["DERIV-substrate-level", "DERIV-encoding-level"]
    sed["statement"] = (
        SEDENION_FIRST_CLAUSE[READING] + " " + sed["statement"].split(". ", 1)[1]
    )
    sed["ruling"] = (
        sed.get("ruling", "")
        + f" | {ENCODE_DATE}: derived_from inverted to [DERIV-substrate-level, DERIV-encoding-level] with the AXIOM-2 retirement (ruling bundle v0.4 §5); first clause neutral ({READING}: which copy encodes a universe is OPEN, INTERP-holographic-boundary)."
    ).strip(" |")
    # re-point derived principles
    for e in L["derived_principles"]:
        if e["id"] in REPOINT_DERIVED:
            if e["derived_from"] != REPOINT_DERIVED[e["id"]]:
                e["derived_from"] = REPOINT_DERIVED[e["id"]]
                ed.touch("derived_principles", e["id"])
        elif replace_in_lists(e, "AXIOM-2", ["DERIV-encoding-level"]):
            ed.touch("derived_principles", e["id"])
    # re-point anchors (list fields) and the flag-3 anchor descriptions
    n_ax2 = n_holo = 0
    for a in L["anchors"]:
        if replace_in_lists(a, "AXIOM-2", ["DERIV-encoding-level"]):
            n_ax2 += 1
            ed.touch("anchors", a["id"])
        if a["id"] in ANCHOR_HOLO_MAP and replace_in_lists(
            a, "DERIV-holographic", ANCHOR_HOLO_MAP[a["id"]]
        ):
            n_holo += 1
            ed.touch("anchors", a["id"])
        if (
            isinstance(a.get("description"), str)
            and "DERIV-holographic, theorem part" in a["description"]
        ):
            a["description"] = a["description"].replace(
                "DERIV-holographic, theorem part",
                "DERIV-holographic-theorem (was DERIV-holographic), part",
            )
            ed.touch("anchors", a["id"])
    # chains
    n_ch = 0
    for c in L["chains"]:
        if replace_in_lists(c, "AXIOM-2", ["META-2", "DERIV-encoding-level"]):
            n_ch += 1
            ed.touch("chains", c["id"])
        if replace_in_lists(
            c,
            "DERIV-holographic",
            ["POST-observer-associativity", "DERIV-holographic-theorem"],
        ):
            n_ch += 1
            ed.touch("chains", c["id"])
    L["changelog"].append(
        {
            "version": "6.0.0",
            "date": f"{ENCODE_DATE}T00:00:00Z",
            "note": (
                f"qbp-oppenheimer: ruling bundle v0.4 sort encoded (PR #652 merged {ENCODE_DATE}; {PAGE_URL}) — nothing ruled, "
                f"nothing forced by fiat. PROVED: T1–T3 (DERIV-holographic-theorem), the level ladders. OPEN roots with kill "
                f"lists (decision_state open): META-2 (meta_principles), POST-hosting (kill cannot fire — recorded as such), "
                f"POST-observer-associativity, POST-observation ((O⊆),(E) beside P2/P2'), INTERP-holographic-boundary (P2 vs P2' "
                f"open, kill cannot fire). DERIV-encoding-level and DERIV-substrate-level are derivations conditional on the open "
                f"roots. AXIOM-2 → retired_axioms (a derivation, not a change of axiom); DERIV-holographic → retired_principles "
                f"(editorial split). DERIV-sedenion derived_from inverted, first clause neutral ({READING}). Re-pointed {n_ax2} "
                f"anchors (AXIOM-2), {n_holo} anchors (DERIV-holographic), {n_ch} chain fields. Root list after: AXIOM-1 (open, "
                f"#659), META-1 (registered #655), META-2, POST-hosting, POST-observer-associativity, POST-observation (all open); "
                f"the rule (#635), the crystal definition and the state-space identification live inside records under non-root "
                f"prefixes — outside the root gate's reach until encoded as roots (scripts/root_audit.py, #658)."
            ),
        }
    )
    L["update_provenance"] = (
        f"qbp-oppenheimer {ENCODE_DATE}: ruling bundle v0.4 sort encoded (PR #652; nothing ruled)"
    )
    L["last_updated"] = f"{ENCODE_DATE}T00:00:00Z"
    ed.touch("changelog")
    ed.touch("update_provenance")
    ed.touch("last_updated")
    print(
        f"applied: reading={READING}; anchors re-pointed AXIOM-2={n_ax2}, DERIV-holographic={n_holo}; chain fields={n_ch}"
    )


if __name__ == "__main__":
    main()
