#!/usr/bin/env python3
"""#668 G2 + AC3 (2026-09-25): rewrite AXIOM-1.kill_condition[0] in positive-measure form.

Ledger record edit on a ROOT (AXIOM-1), not a governance/ file. The previous text (encoded at
#659, 6.1.0 → 6.2.0) was defective in both directions (#668; confirmer verdict 2026-09-20 §3):
  1. unearnable DISCHARGE — "ω-limit map injective a.e." is satisfiable only by the zero flow
     (ω is constant along flow lines; flow-box + Fubini);
  2. asymmetric measure qualifier — the KILL's first conjunct carried none, so with the locus
     made of rest points (ruleField_eq_zero_of_potential_eq_one) it fires on any locus rest
     point the instant local existence is proved — a triviality;
  3. wrong observable — ω-non-injectivity is dissipation, not information destruction; the
     criterion would kill AXIOM-1 on every damped system.
Replacement (positive-measure passage of ω(s) into the zero-divisor locus; discharge = full-measure
avoidance): text proposed on #668 (issuecomment-5828899695), ratified qbp-architecture §I4 seq 1694
(APPROVE-as-drafted) + cth-implementor schema seq 1695 (CONFORMS) on live-test 2026-09-25
(issuecomment-5828957463); beekeeper process go 2026-09-25 ("G2 Go ahead and push"). Tracking #684.

Constraints carried into the encode: `discharge` stays FLAG-rule-flow-open (the live tracker; NOT a
PROOF-/DERIV- id while existence and the {V = 1}-null step are unproved); the "{V = 1} null —
elementary, NOT in Lean" qualifier stays explicit; kill_condition[1] untouched; closure and
decision_state untouched; the previous kill_condition[0] text is preserved verbatim in the changelog.
AC3 (#668): in the same transaction, appends a note to FLAG-rule-flow-open (the discharge target)
recording that AXIOM-1's discharge route now rides on it; the anchor's status, testable_when and
every other field are untouched — notes only.
Written through the confined writer; only AXIOM-1, FLAG-rule-flow-open (+ version/last_updated/
changelog) declared.
Usage: [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DATE = "2026-09-25T00:00:00Z"
OLD_VERSION = "6.10.0"
NEW_VERSION = "6.11.0"
ISSUE_G2 = "https://github.com/JamesPagetButler/QBP/issues/668#issuecomment-5828899695"
ISSUE_RATIFIED = (
    "https://github.com/JamesPagetButler/QBP/issues/668#issuecomment-5828957463"
)

# The ratified wording (G2 comment on #668, both review axes APPROVE/CONFORMS). Plain text; the
# markdown emphasis of the proposal is rendered as capitals where it was load-bearing.
NEW_KILL = (
    "QUESTION 1 (process) — OPEN: whether 'physical process' ranges over the substrate "
    "(crystallisation under the rule, #635) or only over processes in a crystal. "
    "KILL — under the postulated rule (POST-…, #635) and the working initial ensemble (horn 1: N's normalised "
    "surface measure on StateSphere — explored first, with Q_μ and the thermal family retained as live "
    "alternatives; #473 issuecomment-5555310567 and the 2026-09-25 horn audit), the set of initial states s whose "
    "ω-limit set ω(s) meets the zero-divisor locus has POSITIVE MEASURE with respect to that ensemble — proven, with existence of the "
    "flow on that set; OR an anchor with proof_state verified asserting information loss from a stated "
    "process. Then AXIOM-1 is contradicted by a proven process and must change (option A, package §4a "
    "price), because it has been proven that it must. "
    "DISCHARGE — proven: for a set of initial states of FULL MEASURE, ω(s) ∩ zero-divisor-locus = ∅. "
    "Route on record: omega_avoids_zeroDivisors [PROOF-rule-descent-avoids-zero-divisors; conditional "
    "on a given curve] + local existence + {V = 1} of measure zero [elementary: proper real-algebraic "
    "subset of S¹⁴ — NOT in Lean]. Earnable by the non-trivial flow as postulated. "
    "TODAY — existence not proved (FLAG-rule-flow-open); the kill cannot fire and the discharge is not "
    "earned. OPEN, not a pass. What passage through the locus would destroy remains the seam question "
    "(FLAG-seam-dynamics-open), not decided here."
)

NOTES = (
    "kill_condition[0] rewritten 2026-09-25 per #668 (defects: unearnable discharge; asymmetric "
    "measure qualifier; wrong observable); text ratified qbp-architecture seq 1694 + cth-implementor "
    "seq 1695 on live-test; beekeeper go given in the qbp-oppenheimer session 2026-09-25 ('G2 Go ahead and push'); direct on-PR confirmation of the go and of the working-ensemble deviation pending (#687 merge-gate box) — the record is not to be read as pre-confirmed; the previous text is preserved in the changelog "
    "entry "
    + NEW_VERSION
    + ". Trigger issue #647; derived there at trigger time, never ruled."
    " Encode-time constraints honoured: discharge stays FLAG-rule-flow-open "
    "(a tracker, not a PROOF-/DERIV- id) while flow existence and the {V = 1}-null step are unproved; "
    "the 'NOT in Lean' qualifier is kept explicit so the discharge reads earnable-modulo-one-"
    "unformalised-step. kill_condition[1] untouched. G2 proposal: "
    + ISSUE_G2
    + "; reviews: "
    + ISSUE_RATIFIED
    + "; tracking #684."
)

# AC3 (#668): appended verbatim to FLAG-rule-flow-open's existing notes string (plain-text append,
# the record's own convention — see the 2026-09-25 #473-attack-1 CORRECTION already on this note).
FLAG_NOTES_APPEND = (
    " 2026-09-25 (#668, PR #687): AXIOM-1 kill_condition[0] now rides on this tracker — its "
    "DISCHARGE is 'for a full-measure set of initial states, ω(s) ∩ zero-divisor-locus = ∅', "
    "earnable via omega_avoids_zeroDivisors (PROOF-rule-descent-avoids-zero-divisors; conditional "
    "on a given curve) + local existence + {V = 1} of measure zero (elementary, not in Lean); its "
    "KILL is positive-measure passage of ω(s) into the locus under the postulated rule and the "
    "working ensemble (horn 1, alternatives retained). Neither fires until existence lands; "
    "AXIOM-1's discharge field points here. The old kill's 'ω-injective a.e.' discharge is retired "
    "(unearnable by any non-trivial flow, #668)."
)


def changelog_note(old_kill):
    return (
        "qbp-oppenheimer: #668 G2 — AXIOM-1.kill_condition[0] rewritten in positive-measure form "
        "(ROOT record edit; text ratified §I4 qbp-architecture seq 1694 APPROVE-as-drafted + cth-implementor "
        "schema seq 1695 CONFORMS on live-test 2026-09-25; beekeeper process go 2026-09-25). Three defects "
        "fixed: (1) unearnable DISCHARGE ('ω-limit map injective a.e.' ⟺ the zero flow) → discharge is "
        "now full-measure avoidance of the zero-divisor locus, earnable by a non-trivial flow; (2) asymmetric "
        "measure qualifier (KILL conjunct 1 fired on any locus rest point once local existence is proved) → "
        "the kill is positive-measure passage of ω(s) into the locus, proven WITH existence of the flow on "
        "that set; (3) wrong observable (ω-non-injectivity is dissipation) → the observable is passage into "
        "the only proven kernel (PROOF-42zd). QUESTION 1 (substrate vs crystal scope) stays OPEN; TODAY: "
        "existence not proved (FLAG-rule-flow-open) — the kill cannot fire and the discharge is not earned; "
        "OPEN, not a pass; what passage would destroy remains FLAG-seam-dynamics-open. closure "
        "'derivation', discharge FLAG-rule-flow-open and decision_state 'open' unchanged (root_audit bucket 3 "
        "preserved); kill_condition[1] untouched; notes added. AC3 (#668): FLAG-rule-flow-open's notes "
        "extended (append only — status, testable_when and every other field untouched) to record that "
        "AXIOM-1's discharge route now rides on this tracker. Nothing else touched. PREVIOUS "
        "kill_condition[0] text, verbatim (6.2.0 → 6.10.0): “" + old_kill + "”"
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        if L["version"] != OLD_VERSION:
            raise SystemExit(
                f"ledger version is {L['version']}, expected {OLD_VERSION}; "
                f"re-check NEW_VERSION before applying"
            )
        if any(c.get("version") == NEW_VERSION for c in L["changelog"]):
            raise SystemExit("already applied")
        a = ed.record("axioms", "AXIOM-1")
        kc = a["kill_condition"]
        assert (
            isinstance(kc, list) and len(kc) == 2
        ), "AXIOM-1 kill_condition shape changed"
        e0 = kc[0]
        assert e0["closure"] == "derivation", e0["closure"]
        assert e0["discharge"] == "FLAG-rule-flow-open", e0["discharge"]
        assert a["decision_state"] == "open", a["decision_state"]
        old_kill = e0["kill"]
        assert old_kill.startswith(
            "QUESTION 1 (process)"
        ), "unexpected kill_condition[0]"
        assert (
            "omega-limit map is non-injective" in old_kill
        ), "unexpected kill_condition[0]"
        e0["kill"] = NEW_KILL
        # closure / discharge / kill_condition[1] deliberately untouched
        assert (
            "notes" not in a
        ), "AXIOM-1 already carries notes; extend rather than overwrite"
        a["notes"] = NOTES
        L["version"] = NEW_VERSION
        ed.touch("version")
        if L.get("last_updated", "") < DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(
            {"version": NEW_VERSION, "date": DATE, "note": changelog_note(old_kill)}
        )
        ed.touch("changelog")
        # AC3 (#668): same transaction, FLAG-rule-flow-open notes extended (append only).
        f = ed.record("anchors", "FLAG-rule-flow-open")
        assert isinstance(f["notes"], str), "FLAG-rule-flow-open notes shape changed"
        assert FLAG_NOTES_APPEND.strip() not in f["notes"], "AC3 note already applied"
        f["notes"] = f["notes"] + FLAG_NOTES_APPEND
    print(
        f"{'DRY ' if args.dry_run else ''}applied: AXIOM-1.kill_condition[0] rewritten "
        f"({OLD_VERSION} → {NEW_VERSION}); FLAG-rule-flow-open notes extended (AC3)"
    )


if __name__ == "__main__":
    main()
