#!/usr/bin/env python3
"""Required status check: fail when a merge-blocking sign-off box is unticked (#507 §7).

Consumer 2 of the §2.2 box parser (`scripts/pr_merge_blocking_boxes.py`, the ONE
parser shared with the notifier's nudge — consumer 1).  Wired as the GitHub
check `Merge-blocking boxes` (`.github/workflows/merge-blocking-boxes.yml`); the
beekeeper adds that name to the master ruleset's required checks, after which
an unticked merge-blocking box disables the merge button — for everyone,
including the beekeeper (ruling on #507, 2026-10-27).  Auto-nudge, never
auto-tick: this script reads the body and exits; the hand that owns a box still
ticks it (or ⊘-nils it with a reason).

Exit codes (the contract the workflow relies on):
  0  no unticked merge-blocking box: all ticked and/or ⊘-nil'd, OR no §2.2
     region in the body (not assessable — `::warning::`, see below)
  1  `region=present` and `unticked > 0`  → red check, each box named
  1  `region=absent` and `--absent-blocks` → red check (the beekeeper's flip)
  2  usage error (unreadable body file)

No-region policy (PR B, beekeeper-confirmable): a body that uses neither §2.2
form is NOT blocked here — the notifier already withholds ✅ for it (🟡 "not
assessable", fail-closed R3) and the PR templates do not yet carry the region
everywhere.  The check passes with a `::warning::` that names the fix.  To make
absence blocking later, pass `--absent-blocks` in the workflow step (one line).

Beekeeper-box scope guard (#835; beekeeper ruling 2026-11-24, QBP#714
issuecomment-7147354671).  Active when the workflow passes `--labels` and
`--changed-file` (a changed rename contributes BOTH its old and new path):

  pure housekeeping = label `housekeeping` AND not theory-bearing AND touches
                      no merge-lane file.
  theory-bearing    = any changed path under THEORY_PATHS (the union of
                      PR Process Lints §1 and the tier-3 gate's THEORY_GLOBS),
                      or the `tier-3-review` label.  Paths decide; the label can
                      only ADD theory status, never remove it (a GITHUB_TOKEN
                      label does not re-trigger this job — F2 on PR #838).
  merge-lane file   = LANE_PATHS: the box/tier/label gates, their workflows, the
                      PR templates, CONTRIBUTING.md, review_tiers.md, CODEOWNERS.
                      Those PRs stay the beekeeper's (CLAUDE.md delegation rule).

  1. A ⊘-nil'd beekeeper box (HVR / merge authorized / beekeeper, matched after
     NFKC + zero-width removal) on a PR that is not pure housekeeping → exit 1.
  2. Positive requirement: on a PR with a §2.2 region that is neither pure
     housekeeping nor plain Tier 1 (`tier-1-review` label, no theory, no lane
     file), the region must hold a TICKED Human Visual Review box AND a TICKED
     Merge authorized box → else exit 1 (a deleted or renamed box cannot pass).
  Without the scope inputs, rule 1 fails closed and rule 2 is not evaluated.

Usage: merge_blocking_check.py [--body-file F | reads stdin] [--absent-blocks]
                               [--labels="a,b"] [--changed-file=F]
"""

from __future__ import annotations

import argparse
import os
import re
import sys
import unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pr_merge_blocking_boxes import parse  # noqa: E402

# Normalisation before any name match: NFKC, zero-width / soft-hyphen removal,
# markdown emphasis + strike markers dropped, case-folded.
_ZW_RE = re.compile("[\u00ad\u200b-\u200f\u2060\ufeff]")
_MD_RE = re.compile(r"[~*_`]")
# A NIL'd box naming the beekeeper's sign-off in any spelling (wide on purpose).
BEEKEEPER_NIL_RE = re.compile(
    r"visual\W*review|beekeeper|\bh\W?v\W?r|merge\W*authori[sz]|merge\W*approv"
)
# The two boxes a non-housekeeping Tier 2+ PR must carry TICKED (canonical names).
HVR_BOX_RE = re.compile(r"human\W*visual\W*review|\bhvr\b")
MA_BOX_RE = re.compile(r"merge\W*authori[sz]ed")
HOUSEKEEPING_LABEL = "housekeeping"
TIER1_LABEL = "tier-1-review"

# Theory-bearing paths: the UNION of PR Process Lints §1
# (`check_pr_prose_claims.THEORY_PATHS`) and the tier-3 gate
# (`check_tier3_label.THEORY_GLOBS` prefixes), as path prefixes (stricter than the
# globs: any file under them).  Kept as a local copy so the base-sha judge stays
# the two files the verdict selector requires; the test suite asserts this is a
# superset of both sources, so neither can widen without this following.
THEORY_PATHS = (
    "proofs/",
    "docs/theory/",
    "docs/foundations/",
    "paper/",
    "archive/cth-inventory/",
)
THEORY_LABEL = "tier-3-review"
# Merge-lane / governance machinery (F4 on PR #838): a PR touching any of these is
# never pure housekeeping — the beekeeper merges it (CLAUDE.md: "A PR that changes
# this delegation or any seat's merge lane is merged by the beekeeper").
LANE_PATHS = (
    "CONTRIBUTING.md",
    "docs/workflows/review_tiers.md",
    ".github/PULL_REQUEST_TEMPLATE/",
    ".github/CODEOWNERS",
    "CODEOWNERS",
    "docs/CODEOWNERS",
    ".github/workflows/merge-blocking-boxes.yml",
    ".github/workflows/tier-3-review-gate.yml",
    ".github/workflows/pr-check-status.yml",
    "scripts/merge_blocking_check.py",
    "scripts/pr_merge_blocking_boxes.py",
    "scripts/merge_blocking_verdict_source.py",
    "scripts/check_tier3_label.py",
    "scripts/pr_box_evidence.py",
)


def _norm(text: str) -> str:
    return _MD_RE.sub(
        "", _ZW_RE.sub("", unicodedata.normalize("NFKC", text))
    ).casefold()


def _labels(labels) -> set:
    return {x.strip().casefold() for x in labels}


def is_theory_bearing(labels, changed) -> bool:
    """Paths decide; the `tier-3-review` label (case-folded) can only add."""
    if THEORY_LABEL in _labels(labels):
        return True
    return any(p.startswith(THEORY_PATHS) for p in changed)


def touches_lane(changed) -> bool:
    return any(
        p == lp or (lp.endswith("/") and p.startswith(lp))
        for p in changed
        for lp in LANE_PATHS
    )


def pure_housekeeping(labels, changed) -> bool:
    """True iff the PR is pure housekeeping per the 2026-11-24 ruling (#835).

    The `housekeeping` label match is exact (after strip): a near-miss fails closed.
    """
    return (
        HOUSEKEEPING_LABEL in {x.strip() for x in labels}
        and not is_theory_bearing(labels, changed)
        and not touches_lane(changed)
    )


def needs_beekeeper_boxes(labels, changed) -> bool:
    """Tier 2+ and not pure housekeeping → HVR + merge authorized must be ticked."""
    if pure_housekeeping(labels, changed):
        return False
    plain_tier1 = (
        TIER1_LABEL in _labels(labels)
        and not is_theory_bearing(labels, changed)
        and not touches_lane(changed)
    )
    return not plain_tier1


def _why_not_pure(labels, changed) -> str:
    if is_theory_bearing(labels, changed):
        return (
            "PR is theory-bearing (tier-3-review label or a path under "
            + ", ".join(THEORY_PATHS)
            + ")"
        )
    if touches_lane(changed):
        return "PR touches merge-lane / governance files (beekeeper-merged)"
    return "no `housekeeping` label"


DOC_URL = (
    "https://github.com/JamesPagetButler/inter/blob/main/github-best-practices.md"
    "#22-body"
)
LOCAL_DOC = "docs/workflows/review_tiers.md (Evidence-first discipline, item 8)"
FIX_HINT = (
    "tick the box, or ⊘-nil it with a reason (`- [ ] ~~option~~ ⊘ reason`) — "
    "the hand that owns the box ticks it; nothing auto-ticks"
)
ABSENT_FIX = (
    "add a `Sign-off required (merge-blocking):` list (or the "
    "`<!-- merge-blocking -->` sentinel) to the PR body per github-best-practices "
    "§2.2 so the sign-off state is assessable; the notifier shows 🟡 not-assessable "
    "until then"
)


def _annot(level: str, msg: str) -> None:
    """Emit a GitHub workflow command on one line.

    The message part is percent-escaped per the Actions toolkit (`%`→`%25`,
    `\r`→`%0D`, `\n`→`%0A`): a box text containing `%` or a line break must
    neither truncate the annotation nor start a second command.
    """
    esc = msg.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(f"::{level}::{esc}")


def check(body: str, absent_blocks: bool = False, labels=None, changed=None) -> int:
    """Return the exit code for `body` and print the actionable report.

    `labels`/`changed` are the PR's label names and changed paths; `None`
    means "not supplied", which fails closed for a nil'd beekeeper box.
    """
    res = parse(body)
    n_un, n_t, n_nil = len(res["unticked"]), len(res["ticked"]), len(res["nil"])
    n_ev = len(res.get("evidence", []))
    # `evidence=` (the notifier-owned CI-green box, #815) is appended AFTER
    # `region=` so the stable `unticked=<n> …` prefix is unchanged.
    print(
        f"unticked={n_un} ticked={n_t} nil={n_nil} region={res['region']} "
        f"evidence={n_ev}"
    )
    if res["region"] == "absent":
        msg = f"Merge-blocking boxes: no §2.2 region in the PR body — {ABSENT_FIX}."
        if absent_blocks:
            _annot("error", msg + f" (absence is BLOCKING here) See {DOC_URL}")
            return 1
        _annot("warning", msg + f" (not blocking in this configuration) See {DOC_URL}")
        return 0
    bk_nil = [t for t in res["nil"] if BEEKEEPER_NIL_RE.search(_norm(t))]
    scoped = labels is not None and changed is not None
    if bk_nil:
        if not scoped:
            ok, why = False, "PR labels/changed files not supplied (fail closed)"
        else:
            ok = pure_housekeeping(labels, changed)
            why = "" if ok else _why_not_pure(labels, changed)
        if not ok:
            print(
                f"\nFAIL — {len(bk_nil)} beekeeper box(es) ⊘-nil'd on a PR that is "
                f"not pure housekeeping ({why}):"
            )
            for t in bk_nil:
                print(f"  - [ ] {t}")
                _annot(
                    "error",
                    f"⊘-nil'd beekeeper box on a non-housekeeping PR: {t} — HVR and "
                    f"`merge authorized` may be nil'd only on pure housekeeping "
                    f"({why}); when in doubt, treat it as theory (#835)",
                )
            print(f"Contract: {LOCAL_DOC}")
            return 1
    if scoped and needs_beekeeper_boxes(labels, changed):
        ticked_n = [_norm(t) for t in res["ticked"]]
        missing = [
            name
            for name, rx in (
                ("Human Visual Review (beekeeper)", HVR_BOX_RE),
                ("Merge authorized (beekeeper; QBP lane)", MA_BOX_RE),
            )
            if not any(rx.search(t) for t in ticked_n)
            and not any(rx.search(_norm(t)) for t in res["unticked"])
        ]
        if missing:
            why = _why_not_pure(labels, changed)
            print(
                f"\nFAIL — required beekeeper box(es) missing from the §2.2 region "
                f"on a Tier 2+ PR that is not pure housekeeping ({why}):"
            )
            for name in missing:
                print(f"  - [ ] {name}")
                _annot(
                    "error",
                    f"required beekeeper box missing: {name} — Tier 2+ PRs keep HVR and "
                    f"`merge authorized` except pure housekeeping ({why}); add the box "
                    f"to the merge-blocking region (#835)",
                )
            print(f"Contract: {LOCAL_DOC}")
            return 1
    if n_un > 0:
        print(
            f"\nFAIL — {n_un} merge-blocking sign-off box(es) unticked "
            f"(github-best-practices §2.2 region present):"
        )
        for t in res["unticked"]:
            print(f"  - [ ] {t}")
            _annot("error", f"unticked merge-blocking box: {t} — {FIX_HINT}")
        print(f"\nFix: {FIX_HINT}.")
        print(f"Contract: {DOC_URL}  ·  {LOCAL_DOC}")
        print("Edit the PR body; this check re-runs on `pull_request: edited`.")
        return 1
    _annot(
        "notice",
        f"Merge-blocking boxes: all clear ({n_t} ticked, {n_nil} ⊘-nil'd, "
        f"{n_ev} notifier-owned CI-green evidence, 0 unticked in the §2.2 region).",
    )
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--body-file", help="PR body file (default: stdin)")
    ap.add_argument(
        "--absent-blocks",
        action="store_true",
        help="also fail when the body has no §2.2 region (beekeeper's flip)",
    )
    ap.add_argument(
        "--labels",
        default=None,
        help="comma-separated PR label names (enables the #835 beekeeper-box guard; pass as --labels=VALUE)",
    )
    ap.add_argument(
        "--changed-file",
        default=None,
        help="file listing the PR's changed paths, one per line (#835 guard)",
    )
    args = ap.parse_args(argv)
    labels = changed = None
    if args.labels is not None:
        labels = [x.strip() for x in args.labels.split(",") if x.strip()]
    if args.changed_file is not None:
        try:
            with open(args.changed_file, encoding="utf-8") as fh:
                changed = [ln.strip() for ln in fh if ln.strip()]
        except OSError as e:
            _annot("error", f"Merge-blocking boxes: cannot read changed files: {e}")
            return 2
    try:
        if args.body_file:
            with open(args.body_file, encoding="utf-8") as fh:
                body = fh.read()
        else:
            body = sys.stdin.read()
    except OSError as e:
        _annot("error", f"Merge-blocking boxes: cannot read PR body: {e}")
        return 2
    return check(body, absent_blocks=args.absent_blocks, labels=labels, changed=changed)


if __name__ == "__main__":
    sys.exit(main())
