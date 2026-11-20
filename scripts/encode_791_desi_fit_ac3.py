#!/usr/bin/env python3
"""QBP#791 AC3 — write the qbp-desi-fit round-1 E move onto `PRED-w-not-minus-1`.

Issue #791 (inter#246 AC4 write-back): the pre-registered round-1 fit of the
recorded reading-I accretion density (QBP#775/#782; frozen pre-registration
`spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md`, results
`spikes/qbp-desi-fit/qbp-desi-fit-r1-results.md`) found model A (z_t fixed at
0.70, the record's own value) disfavoured relative to ΛCDM: ΔAIC(A - ΛCDM) =
+109.734 against the frozen rule "disfavoured iff ΔAIC >= +2". Physics sign
(AC1) by qbp-oppenheimer, 2026-10-29, two amendments (issue comment); paper
write-back (AC2) merged as QBP PR #792 (`c0597b6`). This script is the AC3
writer-lane leg: the E move itself, encoded onto the ledger's e_axis field
(schema 0.3.6) rather than hand-typed, so the notary's AC3 verify reads a
reproducible run against the frozen pre-reg and the raw sha, not prose.

Two facts land on the SAME anchor, kept UNFOLDED (qbp-architecture, QBP#791 AC1
confirmation comment, 2026-10-29): this script never combines them into one
sentence or one field.
  1. `e_axis`: value "falsified", post_hoc true. "falsified" is a terminal
     e_axis outcome (schema 0.3.6 EAxis doc), so it is reachable even though
     the round's own contamination guard caps its best POSITIVE outcome at
     "consistent (post-hoc)" (z_t and Omega_DE were set from data families
     this fit uses) -- the ceiling bounds confirmation, not falsification.
     Scoped to model A (the recorded reading-I density as fitted) only: it
     says nothing about reading II, the free-transition variant B (not as
     good as CPL, QBP#774, record only), or the
     COMP-cmb-power-spectrum-accretion CAMB re-run (QBP#772 AC3, separate).
  2. `review_flag` (QBP#772 AC1, still open on that issue; this script also
     discharges it): the anchor's OWN description prose ("w > -1 at z < z_t,
     w < -1 at z > z_t") is wrong-signed relative to the sign-corrected
     reading-I density (QBP PR #774 v0.2, `ec47285`), which instead gives
     w < -1 (phantom) below z_t and w > -1 (quintessence-like) above it --
     the opposite of the prose. The flag records the discrepancy; the
     description text itself is left exactly as written (a steward
     re-signs it separately -- QBP#772 AC1 note, not this issue's scope).

QBP#817 variant A: version/changelog/last_updated are frozen; a real change
writes exactly one fragment under archive/cth-inventory/changes.d/ instead
(`scripts/ledger_fragment.write_fragment`), never by hand.

Usage: python3 scripts/encode_791_desi_fit_ac3.py --pr <N> [--dry-run]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import canonical_dump, ledger_edit  # noqa: E402
from ledger_fragment import build_fragment, fragment_path, write_fragment  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"

ANCHOR_ID = "PRED-w-not-minus-1"
FRAGMENT_ISSUE = 791
FRAGMENT_SLUG = "ac3-desi-fit-r1-e-move"

PRE_REG_REF = (
    "spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md "
    "sha256 f6a186169d9dae577d61f626578bc0d166314b6d1f8041bcbd3f3c788337090a "
    "@ 0a59a59"
)
PRE_REG_TIMESTAMP = "2026-10-27T19:52:36-04:00"
DATASET_REF = (
    "spikes/qbp-desi-fit/raw/qbp-desi-fit-r1-raw-2026-10-27.json "
    "sha256 e143b83503a17f487f1ecebf23ad25388d62e3be6d907d94e2f0290f9834700a "
    "@ 421aa94"
)
THRESHOLD = (
    "disfavoured iff ΔAIC(A - ΛCDM) >= +2 (frozen §4 Q1, "
    "spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md)"
)
MEASUREMENT_CHAIN = (
    "DESI DR2 BAO (CobayaSampler/bao_data@b7b8a36) + Pantheon+SH0ES "
    "(PantheonPlusSH0ES/DataRelease@7fc6805, STAT+SYS covariance, M "
    "marginalised analytically) + Planck 2018 compressed distance priors "
    "(arXiv:1808.05724, Chen/Huang/Wang 2019 convention) -> joint "
    "L-BFGS-B+Nelder-Mead fit, z_t fixed at 0.70 (the recorded reading-I "
    "density; cosmo.py/likelihoods.py/fit.py@425761f) -> AIC relative to "
    "LCDM (spikes/qbp-desi-fit/qbp-desi-fit-r1-results.md §Q1)"
)
SYSTEMATICS = (
    "Pantheon+ STAT+SYS covariance and the Planck 2018 compressed-prior "
    "covariance used verbatim; no additional systematics budget beyond the "
    "published covariances (qbp-desi-fit-r1-results.md, deviations 2-7)"
)

EVIDENCE_REF = [
    {
        "kind": "internal",
        "value": 109.734,
        "systematics": SYSTEMATICS,
        "threshold": THRESHOLD,
        "measurement_chain": MEASUREMENT_CHAIN,
        "pre_registered": True,
        "pre_reg_ref": PRE_REG_REF,
        "pre_reg_timestamp": PRE_REG_TIMESTAMP,
        "dataset_ref": DATASET_REF,
    }
]

E_AXIS = {"value": "falsified", "post_hoc": True}

REVIEW_FLAG = (
    "Sign review (QBP#772 AC1): this anchor's own description prose "
    '("w > -1 at z < z_t ... w < -1 at z > z_t") is wrong-signed relative '
    "to the sign-corrected reading-I density (QBP PR #774 v0.2, `ec47285`): "
    "w_eff(z) = -1 + (2/3)[(1+z)^2 - (1+z_t)^2]/[(1+z)^2 + (1+z_t)^2] gives "
    "w < -1 (phantom) below z_t and w > -1 (quintessence-like) above it -- "
    "the opposite sense. The description text is left as originally "
    "written; a steward re-signs it separately (not this issue's scope). "
    "Kept unfolded from the e_axis falsification below (QBP#791 AC1, "
    "qbp-architecture confirmation, 2026-10-29): one is a labelling defect "
    "in this anchor's own prose, the other is an empirical result against "
    "the (correctly-signed) recorded density -- two different facts."
)

NOTES_ADDITION = (
    "\n\nE-axis update (QBP#791 AC3, writer lane, 2026-11-20): e_axis set to "
    'falsified -- a FALSIFIED CANDIDATE (frozen pre-reg §5, row "A '
    'disfavoured": "propose a falsified candidate ... with kill-condition '
    "review\"; the paper, PR #792 l.175, and qbp-oppenheimer's AC1 sign both "
    "say the same, oppenheimer theory re-confirm on PR #821, "
    "issuecomment-7047925804 item 4: the ledger must not be stronger than "
    "the paper) -- for the recorded reading-I density as fitted (model A, "
    "z_t fixed at 0.70), via the pre-registered qbp-desi-fit round-1 fit "
    "(QBP#775/#782). ΔAIC(A - ΛCDM) = +109.734 against the frozen rule "
    '"disfavoured iff ΔAIC >= +2" (see evidence_ref for the pre-reg and '
    "raw-output pointers). post_hoc: true -- z_t and (A+B)^2 = Omega_DE were "
    "set from the same data families this fit uses (frozen contamination "
    "guard, answered YES), so this round's best possible NON-falsifying "
    'outcome was "consistent (post-hoc)"; falsified is a terminal e_axis '
    "outcome and is not bounded by that ceiling. Scoped to this candidate "
    "formulation only: says nothing about reading II of the records, the "
    "free-transition variant B (QBP#774, record only -- not as good as CPL, "
    "Δχ² = +92.354), or the COMP-cmb-power-spectrum-accretion CAMB re-run "
    "(QBP#772 AC3, separate). Paper write-back: QBP#792 (merged `c0597b6`). "
    "Physics sign: qbp-oppenheimer, QBP#791 AC1, 2026-10-29. Kill-condition "
    "review: qbp-oppenheimer, QBP#772 issuecomment-7048003226, 2026-11-20 "
    "(passes) -- the code reproduces the known ΛCDM/CPL answers, SNe and BAO "
    "each disfavour A on their own, the arm-B z_t profile fails at every "
    "z_t from 0.1 to 2.0 so the verdict does not rest on the contaminated "
    "z_t, k matches, no best fit sits on a bound. See the `review_flag` "
    "field for the separate, unfolded sign-labelling fact (QBP#772 AC1)."
)


# The PR #821 real-run text (head 05ff9ea), superseded by the oppenheimer
# theory re-confirm fix round (issuecomment-7047925804 items 4/5): missing
# "candidate" (frozen pre-reg §5 / the paper both require it), and wrongly
# credited the AC1 paper-wording sign as the kill-condition review.
OLD_NOTES_ADDITION_V1 = (
    "\n\nE-axis update (QBP#791 AC3, writer lane, 2026-11-20): e_axis set to "
    "falsified for the recorded reading-I density as fitted (model A, z_t "
    "fixed at 0.70), via the pre-registered qbp-desi-fit round-1 fit "
    "(QBP#775/#782). ΔAIC(A - ΛCDM) = +109.734 against the frozen rule "
    '"disfavoured iff ΔAIC >= +2" (see evidence_ref for the pre-reg and '
    "raw-output pointers). post_hoc: true -- z_t and (A+B)^2 = Omega_DE were "
    "set from the same data families this fit uses (frozen contamination "
    "guard, answered YES), so this round's best possible NON-falsifying "
    'outcome was "consistent (post-hoc)"; falsified is a terminal e_axis '
    "outcome and is not bounded by that ceiling. Scoped to this candidate "
    "formulation only: says nothing about reading II of the records, the "
    "free-transition variant B (QBP#774, record only -- not as good as CPL, "
    "Δχ² = +92.354), or the COMP-cmb-power-spectrum-accretion CAMB re-run "
    "(QBP#772 AC3, separate). Paper write-back: QBP#792 (merged `c0597b6`). "
    "Kill-condition review / physics sign: qbp-oppenheimer, QBP#791 AC1, "
    "2026-10-29 (two amendments, on the issue). See the `review_flag` field "
    "for the separate, unfolded sign-labelling fact (QBP#772 AC1)."
)

# head 5bdccbf, superseded by oppenheimer's kill-condition review landing on
# QBP#772 (seq5625, issuecomment-7048003226, "passes") -- that review was
# PENDING when this text was written; it has since completed.
OLD_NOTES_ADDITION_V2 = (
    "\n\nE-axis update (QBP#791 AC3, writer lane, 2026-11-20): e_axis set to "
    'falsified -- a FALSIFIED CANDIDATE (frozen pre-reg §5, row "A '
    'disfavoured": "propose a falsified candidate ... with kill-condition '
    "review\"; the paper, PR #792 l.175, and qbp-oppenheimer's AC1 sign both "
    "say the same, oppenheimer theory re-confirm on PR #821, "
    "issuecomment-7047925804 item 4: the ledger must not be stronger than "
    "the paper) -- for the recorded reading-I density as fitted (model A, "
    "z_t fixed at 0.70), via the pre-registered qbp-desi-fit round-1 fit "
    "(QBP#775/#782). ΔAIC(A - ΛCDM) = +109.734 against the frozen rule "
    '"disfavoured iff ΔAIC >= +2" (see evidence_ref for the pre-reg and '
    "raw-output pointers). post_hoc: true -- z_t and (A+B)^2 = Omega_DE were "
    "set from the same data families this fit uses (frozen contamination "
    "guard, answered YES), so this round's best possible NON-falsifying "
    'outcome was "consistent (post-hoc)"; falsified is a terminal e_axis '
    "outcome and is not bounded by that ceiling. Scoped to this candidate "
    "formulation only: says nothing about reading II of the records, the "
    "free-transition variant B (QBP#774, record only -- not as good as CPL, "
    "Δχ² = +92.354), or the COMP-cmb-power-spectrum-accretion CAMB re-run "
    "(QBP#772 AC3, separate). Paper write-back: QBP#792 (merged `c0597b6`). "
    "Physics sign: qbp-oppenheimer, QBP#791 AC1, 2026-10-29 (two amendments, "
    "on the issue). Kill-condition review (frozen §5): PENDING, owner "
    "qbp-oppenheimer, on QBP#772 -- the AC1 sign above is the paper-wording "
    "sign-off, NOT the kill-condition review (oppenheimer theory re-confirm "
    'on PR #821, issuecomment-7047925804 item 5). This "candidate" '
    "qualifier is expected to drop in a later one-fragment PR once that "
    "review lands. See the `review_flag` field for the separate, unfolded "
    "sign-labelling fact (QBP#772 AC1)."
)

# Checked in this order: the most recent superseded text must be tried first,
# since OLD_NOTES_ADDITION_V1's text is not a substring of V2's.
SUPERSEDED_NOTES_ADDITIONS = (OLD_NOTES_ADDITION_V2, OLD_NOTES_ADDITION_V1)


def already_applied(anchor: dict) -> bool:
    return (
        anchor.get("e_axis") == E_AXIS
        and anchor.get("review_flag") == REVIEW_FLAG
        and anchor.get("evidence_ref") == EVIDENCE_REF
        and NOTES_ADDITION in (anchor.get("notes") or "")
    )


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--ledger", default=str(LEDGER))
    ap.add_argument(
        "--pr",
        type=int,
        help=(
            "The PR number this run's fragment belongs to (QBP#817 variant A: "
            "required whenever this run actually changes anything)."
        ),
    )
    args = ap.parse_args()

    with ledger_edit(args.ledger, dry_run=args.dry_run) as ed:
        L = ed.ledger
        by_id = {a["id"]: a for a in L["anchors"]}
        if ANCHOR_ID not in by_id:
            raise SystemExit(f"{ANCHOR_ID!r} not found in {args.ledger}")
        if already_applied(by_id[ANCHOR_ID]):
            raise SystemExit("already applied: no change needed")

        a = ed.record("anchors", ANCHOR_ID)
        a["review_flag"] = REVIEW_FLAG
        a["e_axis"] = E_AXIS
        a["evidence_ref"] = EVIDENCE_REF
        # Gemini real-API review, PR #821: `already_applied()` only guards a
        # FULL match (all four fields). A partial-drift re-run (e.g. a
        # steward hand-edits `review_flag` afterwards, so `already_applied`
        # is False) must not duplicate NOTES_ADDITION on top of an addition
        # that already landed in a prior run -- checked here, independent of
        # already_applied()'s all-or-nothing gate.
        current_notes = a.get("notes") or ""
        for superseded in SUPERSEDED_NOTES_ADDITIONS:
            # oppenheimer theory re-confirm rounds (issuecomment-7047925804
            # items 4/5; seq5625 kill-condition-review landing): REPLACE
            # whichever superseded text is present, never append alongside
            # it -- an old text is wrong in some specific way and must not
            # survive next to its own correction. At most one can match
            # (each run's own already_applied()/write step leaves exactly
            # the newest text behind), so trying both in turn is safe.
            if superseded in current_notes:
                current_notes = current_notes.replace(superseded, "")
                break
        if NOTES_ADDITION not in current_notes:
            a["notes"] = current_notes + NOTES_ADDITION
        else:
            a["notes"] = current_notes

        if not args.dry_run and not args.pr:
            raise SystemExit(
                "this run changes the anchor, so it needs --pr <number> to "
                "write its changes.d/ fragment (QBP#817 variant A)"
            )

    fragment_note = (
        f"QBP#791 AC3: {ANCHOR_ID} gains e_axis (value falsified, "
        f"post_hoc true) -- a FALSIFIED CANDIDATE (frozen pre-reg §5; the "
        f"paper, PR #792; qbp-oppenheimer's AC1 sign all say the same) -- "
        f"for the recorded reading-I density as fitted (model A) -- the "
        f"pre-registered qbp-desi-fit round-1 fit (QBP#775/#782) found it "
        f"disfavoured vs LCDM (ΔAIC +109.734 against the frozen "
        f"'disfavoured iff >= +2' threshold); evidence_ref records the "
        f"frozen pre-reg (sha256 f6a18616...090a @ 0a59a59) and the raw "
        f"output (sha256 e143b835...700a @ 421aa94). Scoped to this "
        f"candidate formulation only -- does not test reading II or the "
        f"COMP-cmb-power-spectrum-accretion CAMB re-run (QBP#772 AC3, "
        f"separate). Also lands QBP#772 AC1: a review_flag noting the "
        f"anchor's own description prose is wrong-signed relative to the "
        f"sign-corrected reading-I density (PR #774 v0.2, ec47285), kept "
        f"unfolded from the e_axis fact per qbp-architecture's QBP#791 AC1 "
        f"confirmation. Paper write-back QBP#792 (merged c0597b6). Physics "
        f"sign: qbp-oppenheimer, QBP#791 AC1, 2026-10-29. Kill-condition "
        f"review: qbp-oppenheimer, QBP#772 issuecomment-7048003226, "
        f"2026-11-20 (passes) -- code reproduces the known LCDM/CPL "
        f"answers, SNe and BAO each disfavour A on their own, the arm-B "
        f"z_t profile fails at every z_t from 0.1 to 2.0 so the verdict "
        f"does not rest on the contaminated z_t, k matches, no best fit "
        f"sits on a bound."
    )
    if not args.dry_run:
        changes_dir = Path(args.ledger).resolve().parent / "changes.d"
        path = fragment_path(FRAGMENT_ISSUE, FRAGMENT_SLUG, changes_dir)
        if path.exists():
            # Rule 3 of scripts/ledger_bookkeeping_lint.py protects a
            # fragment already on BASE (origin/master); this fragment was
            # added by THIS SAME open PR (#821) and has not merged yet, so
            # correcting its note in place -- never a second fragment file,
            # which rule 2 (exactly one fragment per PR) would forbid -- is
            # the only way to fix a wrong fragment note pre-merge.
            fixed = build_fragment(
                issue=FRAGMENT_ISSUE,
                slug=FRAGMENT_SLUG,
                pr=args.pr,
                encoder="scripts/encode_791_desi_fit_ac3.py",
                note=fragment_note,
                touched_ids=[ANCHOR_ID],
            )
            path.write_text(canonical_dump(fixed), encoding="utf-8")
        else:
            write_fragment(
                issue=FRAGMENT_ISSUE,
                slug=FRAGMENT_SLUG,
                pr=args.pr,
                encoder="scripts/encode_791_desi_fit_ac3.py",
                note=fragment_note,
                touched_ids=[ANCHOR_ID],
                changes_dir=changes_dir,
            )

    print(
        f"{'DRY-RUN ' if args.dry_run else ''}encoded {ANCHOR_ID}: "
        f"e_axis=falsified(post_hoc), review_flag set, evidence_ref[1]"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
