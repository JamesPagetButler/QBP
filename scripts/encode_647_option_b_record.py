#!/usr/bin/env python3
"""#647 / #654: re-record "AXIOM-1 option B" as derived-and-open, not ruled.

Four-bucket audit of option B (the beekeeper's standard, 2026-09-11 — the beekeeper rules
scope, priority and process, never a physical truth; anything the axioms under-determine
is encoded open with a kill condition):

  PROVED   DERIV-sedenion's algebraic clause: on the zero-divisor locus left multiplication
           L_a has a non-trivial kernel — PROOF-42zd (verified, sorry-free).
  FORCED   "flag 1 is not a contradiction today": AXIOM-1's first sentence is about
           processes; the ledger asserts no process at the seams
           (PROOF-no-autonomous-algebraic-dynamics; KILLED-locale-forcing-route;
           FLAG-seam-dynamics-open is incoherent). A kernel is a map, not a process.
           Retiring "seams where information CAN be destroyed" is forced: it asserted a
           loss with no process to carry it.
  OPEN     whether crystallisation is a physical process AXIOM-1 governs — undecidable
           until the rule (#635) exists as a flow through the ridge. Kill condition on
           AXIOM-1; trigger #647; DERIVED at trigger time, never ruled.
  WRONG    the record: "option B — ruled by the beekeeper" put a forced+open item to him
           as a choice and filed his answer as the physical reason. Option A (rescope
           AXIOM-1) was the unforced axiom edit; option B was the non-choice.

This script rewrites the record accordingly through the confined-write helper: only
AXIOM-1, DERIV-sedenion, changelog, version, update_provenance and last_updated change.
Idempotent (guards on AXIOM-1.decision_state). --dry-run verifies confinement only.
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cth_ledger_edit import ledger_edit  # noqa: E402

LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DATE = "2026-09-13"
BEEKEEPER_LINE = (
    "https://github.com/JamesPagetButler/QBP/issues/647#issuecomment-5639808463"
)

AXIOM1_KILL = (
    "Fires when the ledger holds the rule (#635) written as a flow on StateSphere whose "
    "trajectories pass through or terminate on the zero-divisor ridge (V = 1) AND that flow "
    "is shown to lose information along a trajectory (non-injective on states). Then 'no "
    "physical process destroys information' is contradicted by an asserted process and "
    "AXIOM-1 must change (option A: rescope to the encoding, blast radius package §4a) — an "
    "axiom changes only because it has been proven that it must. Today no process is asserted "
    "at the seams (PROOF-no-autonomous-algebraic-dynamics; KILLED-locale-forcing-route; "
    "FLAG-seam-dynamics-open incoherent), so this kill cannot fire — recorded as such, not as "
    "a pass. Trigger issue #647; the answer is DERIVED there at trigger time, never ruled."
)
AXIOM1_SCOPE = (
    "The selection clause ('selects division algebras') is exercised on the encoding "
    "(octonions, DERIV-encoding-level pending #652). The substrate S (DERIV-sedenion) has zero "
    "divisors by construction; whether AXIOM-1 governs processes there is the open question "
    "in kill_condition — not a contradiction today, because no such process is asserted."
)
SEDENION_RECORD = (
    f"Record ({DATE}, re-audited under the four-bucket standard, #654/#647): the algebraic "
    "wording is PROVED (PROOF-42zd — L_a has a non-trivial kernel on the zero-divisor locus). "
    "'No process is asserted at the seams' is a fact of the ledger "
    "(PROOF-no-autonomous-algebraic-dynamics; KILLED-locale-forcing-route; "
    "FLAG-seam-dynamics-open, status incoherent), so flag 1 (vs AXIOM-1) is not a "
    "contradiction today — FORCED, not chosen; retiring the superseded 'information CAN be "
    "destroyed' clause is forced (a loss asserted with no process to carry it). Whether "
    "crystallisation is a physical process AXIOM-1 governs is OPEN — AXIOM-1.kill_condition, "
    "trigger #647, derived at trigger time. 'Option B' (PR #648 §3; applied PR #651) was the "
    "non-choice; option A was an unforced axiom edit. The beekeeper's line 'I choose option B.' "
    f"({BEEKEEPER_LINE}, 2026-09-11) is retained as the PROCESS authorisation to apply the "
    "rewording, not as the physical reason for it."
)


def main():
    dry = "--dry-run" in sys.argv
    with open(LEDGER, encoding="utf-8") as f:
        ax1_now = next(a for a in json.load(f)["axioms"] if a["id"] == "AXIOM-1")
    if ax1_now.get("decision_state") == "open" and "kill_condition" in ax1_now:
        print("already applied — no change")
        return
    with ledger_edit(LEDGER, dry_run=dry) as ed:
        L = ed.ledger
        ax1 = ed.record("axioms", "AXIOM-1")
        ax1["kill_condition"] = AXIOM1_KILL
        ax1["decision_state"] = "open"
        ax1["scope_note"] = AXIOM1_SCOPE
        sed = ed.record("derived_principles", "DERIV-sedenion")
        sed["superseded_ruling"] = sed["ruling"]
        sed["ruling"] = SEDENION_RECORD
        L["changelog"].append(
            {
                "version": "5.4.1",
                "date": f"{DATE}T00:00:00Z",
                "note": (
                    "qbp-oppenheimer: AXIOM-1 'option B' re-recorded under the four-bucket standard "
                    "(#654, beekeeper direction 2026-09-11): the content is PROVED (PROOF-42zd) + "
                    "FORCED (no process asserted at the seams); the scope question is OPEN with a "
                    "kill_condition on AXIOM-1 (trigger #647, derived not ruled); the beekeeper's "
                    "own-hand line is kept as process authorisation, not physical reason. "
                    "AXIOM-1 now sorts into bucket-3 OPEN under scripts/root_audit.py (#658)."
                ),
            }
        )
        ed.touch("changelog")
        L["version"] = "5.4.1"
        ed.touch("version")
        L["update_provenance"] = (
            f"qbp-oppenheimer {DATE}: #647 option-B record re-audited (#654)"
        )
        ed.touch("update_provenance")
        L["last_updated"] = f"{DATE}T00:00:00Z"
        ed.touch("last_updated")


if __name__ == "__main__":
    main()
