#!/usr/bin/env python3
"""Pick the checkout that judges a PR for the `Merge-blocking boxes` check (#507 §7).

The judge must not be part of the evidence (qbp-architecture §I4 on PR #780):
on `pull_request` the default checkout IS the PR head, so a PR that edits
`scripts/merge_blocking_check.py` or `scripts/pr_merge_blocking_boxes.py` would
otherwise be judged by its own copy.  The workflow therefore checks the PR's
**base sha** out into `base/` and runs the verdict from there.

Selection:
  base              both REQUIRED scripts exist in the base checkout → the base
                    copy judges (the PR's own edits to the scripts are inert)
  head(bootstrap)   the base lacks at least one script (first landing of the
                    check, or of a renamed script) → the head copy judges, with
                    a `::warning::` naming the missing file(s)
  exit 1            neither checkout has both scripts → fail closed

Output (stdout): `verdict-source=<base|head(bootstrap)>` and `verdict-dir=<dir>`;
the same two values go to `$GITHUB_OUTPUT` (`source=`, `dir=`) when that
variable is set, so later steps run `$dir/scripts/merge_blocking_check.py`.

Usage: merge_blocking_verdict_source.py --base DIR --head DIR
"""

from __future__ import annotations

import argparse
import os
import sys
from typing import List, Tuple

REQUIRED = ("scripts/merge_blocking_check.py", "scripts/pr_merge_blocking_boxes.py")


def _missing(root: str) -> List[str]:
    return [f for f in REQUIRED if not os.path.isfile(os.path.join(root, f))]


def select(base: str, head: str) -> Tuple[str, str, List[str]]:
    """Return (source, dir, base_missing); raise FileNotFoundError if neither qualifies."""
    base_missing = _missing(base)
    if not base_missing:
        return "base", base, []
    head_missing = _missing(head)
    if head_missing:
        raise FileNotFoundError(
            f"base lacks {base_missing} and head lacks {head_missing}: nothing can judge"
        )
    return "head(bootstrap)", head, base_missing


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", required=True, help="checkout of the PR base sha")
    ap.add_argument(
        "--head", required=True, help="checkout of the PR head (default cwd)"
    )
    args = ap.parse_args(argv)
    try:
        source, chosen, base_missing = select(args.base, args.head)
    except FileNotFoundError as e:
        print(f"::error::Merge-blocking boxes: {e}")
        return 1
    if base_missing:
        print(
            "::warning::Merge-blocking boxes: verdict runs from the PR HEAD copy "
            f"(bootstrap) — the base checkout `{args.base}` lacks "
            f"{', '.join(base_missing)}. Once the scripts are on the base branch the "
            "base copy judges and a head-side edit cannot flip the verdict."
        )
    print(f"verdict-source={source}")
    print(f"verdict-dir={chosen}")
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(f"source={source}\ndir={chosen}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
