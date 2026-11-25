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
issuecomment-7147354671): a ⊘-nil'd box whose text names Human Visual Review /
HVR or `merge authorized` is accepted ONLY on a pure housekeeping PR — label
`housekeeping` and not theory-bearing (the PR Process Lints §1 definition:
no `tier-3-review` label, no changed path under proofs/, docs/theory/,
docs/foundations/).  Otherwise exit 1.  "When in doubt, treat it as theory":
if the scope inputs are not supplied the guard fails closed on such a nil.

Usage: merge_blocking_check.py [--body-file F | reads stdin] [--absent-blocks]
                               [--labels "a,b"] [--changed-file F]
"""

from __future__ import annotations

import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pr_merge_blocking_boxes import parse  # noqa: E402

# A nil'd box naming one of the beekeeper's own boxes (HVR / merge authorized).
BEEKEEPER_BOX_RE = re.compile(
    r"human\s+visual\s+review|\bhvr\b|merge[\s-]+authori[sz]ed", re.I
)
HOUSEKEEPING_LABEL = "housekeeping"

# Theory-bearing = the PR Process Lints §1 definition.  Kept as a local copy (not
# an import) so the base-sha judge stays the two files it has always been; the
# test suite asserts it equals `check_pr_prose_claims.THEORY_PATHS/THEORY_LABEL`.
THEORY_PATHS = ("proofs/", "docs/theory/", "docs/foundations/")
THEORY_LABEL = "tier-3-review"


def is_theory_bearing(labels, changed) -> bool:
    if THEORY_LABEL in labels:
        return True
    return any(p.startswith(THEORY_PATHS) for p in changed)


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


def pure_housekeeping(labels, changed) -> bool:
    """True iff the PR is pure housekeeping per the 2026-11-24 ruling (#835)."""
    return HOUSEKEEPING_LABEL in labels and not is_theory_bearing(labels, changed)


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
    bk_nil = [t for t in res["nil"] if BEEKEEPER_BOX_RE.search(t)]
    if bk_nil:
        if labels is None or changed is None:
            ok, why = False, "PR labels/changed files not supplied (fail closed)"
        else:
            ok = pure_housekeeping(set(labels), list(changed))
            why = (
                "no `housekeeping` label"
                if HOUSEKEEPING_LABEL not in labels
                else "PR is theory-bearing (tier-3-review label or a path under "
                "proofs/, docs/theory/, docs/foundations/)"
            )
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
        help="comma-separated PR label names (enables the #835 beekeeper-box guard)",
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
