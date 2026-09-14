#!/usr/bin/env python3
"""#647 / #654 / #659: re-record "AXIOM-1 option B" — proved + open, not ruled.

Four-bucket audit of option B (the beekeeper's standard, 2026-09-11 — the beekeeper rules
scope, priority and process, never a physical truth; anything the axioms under-determine
is encoded open with a kill condition). Three Red Team rounds moved two items out of
FORCED: "flag 1 is not a contradiction today" (cited an absence) and "the selection clause
is exercised on the encoding" (AXIOM-2 applies the selection there but does not fix the
clause's range). Both are OPEN with their own kill and discharge arms on AXIOM-1.

  PROVED   DERIV-sedenion's algebraic clause: left multiplication by a zero divisor has a
           non-trivial kernel — PROOF-42zd (bridge prodIsZero_iff_cdAlg_mul_eq_zero,
           Breakdown.lean; count zero_divisor_count_42, Sedenion.lean).
  OPEN 1   whether crystallisation is a physical process AXIOM-1's first sentence governs
           — undecidable until the rule (#635) exists as a proven flow; no contradiction
           is DERIVABLE today (a kernel is a map; no proven process through the locus),
           but candidate assertions are on record (Prop 16 layer (iii) numerical
           transient; FLAG-seam-dynamics-open; DERIV-crystallisation-asymptotic;
           DERIV-arrow's lossy projection), none proven. Kill: omega-limit information
           loss of a proven flow, or a verified anchor asserting it. Trigger #647.
  OPEN 2   the range of AXIOM-1's selection clause — AXIOM-2 applies the selection at the
           encoding but does not state the range; both readings are admitted today.
           Discharge route: #652's DERIV-encoding-level states where the selection is
           exercised. Kill: a rule anchor asserting the selection over the substrate.
  WRONG    the record "option B — ruled by the beekeeper": a proved-plus-open item put
           to him as a choice and his answer filed as the physical reason. Option A
           (rescope AXIOM-1) was the unforced axiom edit; option B the non-choice.

Ledger edit through the confined-write helper: only AXIOM-1 (kill_condition,
decision_state — the two D3 fields, nothing else), DERIV-sedenion (ruling), changelog,
version, update_provenance, last_updated change. Version 5.7.1 (changelog head was
5.7.0; 5.4.1 was already used 2026-06-12). Fields documented in
docs/cth/qbp-local-extensions.md; upstream tracking confluent-trust #102. Idempotent.
--dry-run verifies only.
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
    "OPEN — two questions the axioms under-determine, each with its own kill and discharge; "
    "discharging one does not discharge the other. QUESTION 1 (process): whether 'physical "
    "process' ranges over the substrate (crystallisation, the descent through the zero-divisor "
    "locus) or only over processes in a crystal. KILL — a proven flow on StateSphere (the rule, "
    "#635) whose omega-limit set meets the zero-divisor locus and whose omega-limit map is "
    "non-injective on a positive-measure set of states, OR an anchor with proof_state verified "
    "(PROOF-* or DERIV-*) asserting such a loss from a stated process — then 'no physical process "
    "destroys information' is contradicted by a proven process and AXIOM-1 must change (option "
    "A: rescope to the encoding; package §4a price, 22 citers + 5 principles), because it has "
    "been proven that it must. DISCHARGE — the same flow proven information-preserving "
    "(omega-limit map injective almost everywhere). First-order semiflows are injective at "
    "finite time, so the criterion is on the omega-limit, not on finite-time states. TODAY — no "
    "proven flow exists; the ledger holds candidate assertions touching the locus, none proven: "
    "Prop 16 layer (iii) (power-iteration transient onto the dominant subspace; numerical, "
    "generic_maps_check.py; not pressure-tested per the 473-ac1-v0.5 addendum), "
    "FLAG-seam-dynamics-open (incoherent placeholder asserting a seam scattering process), "
    "DERIV-crystallisation-asymptotic (names a process and a step counter Gamma but no map on "
    "states), DERIV-arrow (takes information preservation as its premise and asserts a lossy "
    "projection — a map; listed as the ledger's nearest assertion of loss). The kill cannot fire "
    "and no contradiction is derivable: recorded as OPEN, not as a pass. Trigger issue #647; "
    "derived there at trigger time, never ruled. QUESTION 2 (scope of the selection clause "
    "'selects division algebras'): AXIOM-2's statement applies the selection at the boundary "
    "encoding; it does not state that the clause ranges over the encoding only, and AXIOM-1's "
    "own wording leaves the range unstated. The ledger admits both readings: encoding-only "
    "(DERIV-sedenion's substrate sedenions are the ledger's own content, no conflict) or "
    "unrestricted (PROOF-42zd's 42 zero divisors contradict the clause and AXIOM-1 must be "
    "rescoped, option A). KILL — an encoded rule anchor asserting the selection over the "
    "substrate S, against PROOF-42zd, then option A is due. DISCHARGE — a rule anchor stating "
    "the range: #652's DERIV-encoding-level (selection exercised at the encoding level) is the "
    "named route. Recorded OPEN until encoded; not forced."
)
SEDENION_RECORD = (
    f"Record ({DATE}, four-bucket re-audit, #654/#647/#659). PROVED — the algebraic clause: left "
    "multiplication by a zero divisor has a non-trivial kernel (PROOF-42zd; bridge "
    "prodIsZero_iff_cdAlg_mul_eq_zero, Breakdown.lean; count zero_divisor_count_42, "
    "Sedenion.lean). OPEN (scope) — the range of AXIOM-1's selection clause: AXIOM-2's statement "
    "applies the selection at the boundary encoding but does not state that the clause ranges "
    "over the encoding only; the ledger admits both readings (encoding-only: this entry's "
    "substrate sedenions are the ledger's own content; unrestricted: PROOF-42zd contradicts the "
    "clause and option A is due); resolved when a rule anchor states the range — #652's "
    "DERIV-encoding-level is the named route; recorded OPEN until encoded, not forced "
    "(AXIOM-1.kill_condition question 2). OPEN (process) — whether the kernel clause conflicts "
    "with AXIOM-1's process sentence: a kernel is a map, and no proven process through the "
    "zero-divisor locus exists (Prop 16 layer (i) and the invariant-subspace half of layer (ii) "
    "are in Lean, NoAutonomousDynamics.lean; the shape-invariant half of (ii) and layer (iii) are "
    "numerical; FLAG-seam-dynamics-open is an incoherent placeholder), so no contradiction is "
    "derivable today — candidate assertions are on record, none proven — OPEN under "
    "AXIOM-1.kill_condition question 1, trigger #647, derived at trigger time, never ruled. "
    "WRONG (superseded record): 'AXIOM-1 option B — ruled by the beekeeper 2026-09-09 (PR #648 "
    "package v0.5 §3), applied on direction 2026-09-10 (PR #651)' — an item that was proved plus "
    "open was put to the beekeeper as a choice; option A (rescope AXIOM-1's process sentence) was "
    "an unforced axiom edit, option B the non-choice. The beekeeper's line 'I choose option B.' "
    f"({BEEKEEPER_LINE}, 2026-09-11) post-dates the applied rewording (PR #651, 2026-09-10) and is "
    "retained as ratification of process only, not as the physical reason. Retiring 'seams where "
    "information CAN be destroyed' stands: it asserted a loss with no proven process to carry it."
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
                    "(#654, beekeeper direction 2026-09-11; PR #659 after three Red Team rounds + Gemini): "
                    "the algebraic clause is PROVED (PROOF-42zd); two questions are OPEN on AXIOM-1 — the "
                    "process question (omega-limit information loss of a proven flow through the "
                    "zero-divisor locus; trigger #647) and the scope of the selection clause (#652's "
                    "DERIV-encoding-level is the discharge route) — each with its own kill_condition arm; "
                    "no contradiction derivable today, candidate assertions on record, none proven. The "
                    "old record 'ruled by the beekeeper' is superseded; his line is ratification of "
                    "process, not physical reason. AXIOM-1 sorts into bucket-3 OPEN under "
                    "scripts/root_audit.py (#658); its open_roots register entry is removed by whichever "
                    "of #658 / #659 merges second. Fields documented in docs/cth/qbp-local-extensions.md; "
                    "upstream confluent-trust #102."
                ),
            }
        )
        ed.touch("changelog")
        L["version"] = "5.7.1"
        ed.touch("version")
        L["update_provenance"] = (
            f"qbp-oppenheimer {DATE}: #647 option-B record re-audited (#654/#659, confluent-trust #102)"
        )
        ed.touch("update_provenance")
        L["last_updated"] = f"{DATE}T00:00:00Z"
        ed.touch("last_updated")


if __name__ == "__main__":
    main()
