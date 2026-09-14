#!/usr/bin/env python3
"""#647 / #654 / #659: re-record "AXIOM-1 option B" — proved + open, not ruled (v2).

Four-bucket audit of option B (the beekeeper's standard, 2026-09-11 — the beekeeper rules
scope, priority and process, never a physical truth; anything the axioms under-determine
is encoded open with a kill condition). v2 applies the PR #659 Red Team + Gemini findings:
"flag 1 is not a contradiction today" was mis-filed as FORCED on an absence; it is OPEN.

  PROVED   DERIV-sedenion's algebraic clause: left multiplication by a zero divisor has a
           non-trivial kernel — PROOF-42zd (bridge prodIsZero_iff_cdAlg_mul_eq_zero,
           Breakdown.lean; count zero_divisor_count_42, Sedenion.lean).
  OPEN     (a) whether crystallisation is a physical process AXIOM-1 governs, and
           (b) whether AXIOM-1's selection clause ranges over the substrate S (zero
           divisors by construction) or the encoding only — undecidable until the rule
           (#635) exists as a proven flow. No contradiction is DERIVABLE today (a kernel
           is a map; no proven process through the zero-divisor locus exists), but
           candidate processes are on record (Prop 16 layer 3 transient, numerical;
           FLAG-seam-dynamics-open placeholder; DERIV-arrow's lossy projection), so this
           is OPEN with a kill condition on AXIOM-1 — not FORCED, not a pass.
  WRONG    the record "option B — ruled by the beekeeper": a forced+open item put to him
           as a choice and his answer filed as the physical reason. Option A (rescope
           AXIOM-1) was the unforced axiom edit; option B the non-choice.

Ledger edit through the confined-write helper: only AXIOM-1 (kill_condition,
decision_state — the two D3 fields, nothing else), DERIV-sedenion (ruling), changelog,
version, update_provenance, last_updated change. Version 5.7.1 (changelog head was
5.7.0; 5.4.1 was already used 2026-06-12). Idempotent. --dry-run verifies only.
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
    "OPEN — two questions the axioms under-determine: (a) whether 'physical process' ranges "
    "over the substrate (crystallisation) or only over processes in a crystal; (b) whether the "
    "selection clause 'selects division algebras' ranges over the substrate S (zero divisors "
    "by construction, DERIV-sedenion) or over the encoding only. KILL: a proven flow on "
    "StateSphere (the rule, #635) whose omega-limit meets the zero-divisor locus and whose "
    "omega-limit map is non-injective on a positive-measure set of states (strict phase-volume "
    "contraction), OR an encoded PROOF-/DERIV- anchor asserting such a loss from a stated "
    "process — then 'no physical process destroys information' is contradicted by an asserted "
    "process and AXIOM-1 must change (option A: rescope to the encoding, package §4a price: 22 "
    "citers + 5 principles), because it has been proven that it must. DISCHARGE: the flow proven "
    "information-preserving (omega-limit map injective a.e.) — the kill is then removed as "
    "discharged. First-order semiflows are injective at finite time, so the criterion is on the "
    "omega-limit, not on finite-time states. TODAY: no proven flow exists; the ledger holds "
    "candidate processes touching the locus — Prop 16 layer 3 (power-iteration transient onto "
    "the dominant subspace; numerical, not pressure-tested, 473-ac1-v0.5 addendum), "
    "FLAG-seam-dynamics-open (incoherent placeholder asserting a seam scattering process), and "
    "two AXIOM-1 citers asserting a lossy process (DERIV-arrow 'lossy projection', "
    "DERIV-crystallisation-asymptotic 'time IS the crystallisation') — none proven, so the kill "
    "cannot fire and no contradiction is derivable: recorded as OPEN, not as a pass. Trigger "
    "issue #647; the answer is DERIVED there at trigger time, never ruled."
)
SEDENION_RECORD = (
    f"Record ({DATE}, four-bucket re-audit, #654/#647/#659 v2). PROVED — the algebraic clause: "
    "left multiplication by a zero divisor has a non-trivial kernel (PROOF-42zd; bridge "
    "prodIsZero_iff_cdAlg_mul_eq_zero, Breakdown.lean; count zero_divisor_count_42, "
    "Sedenion.lean). OPEN — whether this clause conflicts with AXIOM-1: a kernel is a map, and "
    "no proven process through the zero-divisor locus exists (Prop 16 layers 1-2 prove the "
    "algebra generates symmetries, never dynamics toward the vacuum; layer 3's transient onto "
    "the locus is numerical; FLAG-seam-dynamics-open is an incoherent placeholder), so no "
    "contradiction is derivable today — but candidate processes are on record, so this is OPEN "
    "under AXIOM-1.kill_condition, trigger #647, derived at trigger time, never ruled. WRONG "
    "(superseded record): 'AXIOM-1 option B — ruled by the beekeeper 2026-09-09 (PR #648 "
    "package v0.5 §3), applied on direction 2026-09-10 (PR #651)' — a forced-plus-open item "
    "was put to the beekeeper as a choice; option A (rescope AXIOM-1) was an unforced axiom "
    "edit, option B the non-choice. The beekeeper's line 'I choose option B.' "
    f"({BEEKEEPER_LINE}, 2026-09-11) post-dates the applied rewording (PR #651, 2026-09-10) and "
    "is retained as ratification of process only, not as the physical reason. Retiring 'seams "
    "where information CAN be destroyed' stands: it asserted a loss with no proven process to "
    "carry it."
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
        sed = ed.record("derived_principles", "DERIV-sedenion")
        sed["ruling"] = SEDENION_RECORD
        L["changelog"].append(
            {
                "version": "5.7.1",
                "date": f"{DATE}T00:00:00Z",
                "note": (
                    "qbp-oppenheimer: AXIOM-1 'option B' re-recorded under the four-bucket standard "
                    "(#654, beekeeper direction 2026-09-11; PR #659 v2 after Red Team + Gemini): the algebraic "
                    "clause is PROVED (PROOF-42zd); whether it conflicts with AXIOM-1 is OPEN — no "
                    "contradiction derivable today, candidate processes on record — with a kill_condition "
                    "on AXIOM-1 (omega-limit information loss of a proven flow through the zero-divisor "
                    "locus; trigger #647, derived not ruled). The old record 'ruled by the beekeeper' is "
                    "superseded; his line is ratification of process, not physical reason. AXIOM-1 sorts "
                    "into bucket-3 OPEN under scripts/root_audit.py (#658); its open_roots register entry "
                    "is removed by whichever of #658 / #659 merges second."
                ),
            }
        )
        ed.touch("changelog")
        L["version"] = "5.7.1"
        ed.touch("version")
        L["update_provenance"] = (
            f"qbp-oppenheimer {DATE}: #647 option-B record re-audited, v2 (#654/#659)"
        )
        ed.touch("update_provenance")
        L["last_updated"] = f"{DATE}T00:00:00Z"
        ed.touch("last_updated")


if __name__ == "__main__":
    main()
