#!/usr/bin/env python3
"""Tier-3 review-label gate — issue #481 Addition 1 (FAULT-S4-001 structural fix).

Theory-bearing PRs MUST carry the `tier-3-review` label, and the label must be backed by
posted Red Team / Gemini review artifacts (a bare label is itself a finding — anti-gaming).
This converts "the Tier-3 gate fired" from human discipline into a mechanical merge precondition,
so neither Oppenheimer nor the beekeeper is a single point of failure.

Theory-bearing trigger paths (review_tiers.md Tier-3: physics formalism, axioms, formal proofs,
architecture):
  - proofs/**/*.lean              (formal proofs)
  - archive/cth-inventory/*.json  (CTH epistemic-status changes — the #484 class)
  - paper/**                      (theory papers)
  - docs/foundations/**           (theory scope/docs)

Logic:
  1. No theory-bearing file changed            -> PASS (not a Tier-3 PR)
  2. Theory-bearing AND no `tier-3-review` label -> FAIL (label required)
  3. Labeled BUT no review-artifact comment     -> FAIL (bare label / rubber-stamp)
  4. else                                       -> PASS

Usage:
  check_tier3_label.py --changed-files changed.txt --labels-file labels.txt --comments-file comments.txt
"""

import argparse
import fnmatch
import re
import sys

THEORY_GLOBS = [
    "proofs/*.lean",
    "proofs/**/*.lean",
    "archive/cth-inventory/*.json",
    "paper/*",
    "paper/**",
    "docs/foundations/*",
    "docs/foundations/**",
]
TIER3_LABEL = "tier-3-review"
# review-artifact signatures — a real Red Team / Gemini §I4 review leaves one of these.
REVIEW_ARTIFACT = re.compile(
    r"Red Team|Gemini|§I4|APPROVE|REQUEST CHANGES|Sabine|Furey|Feynman", re.IGNORECASE
)


def is_theory(path):
    return any(fnmatch.fnmatch(path, g) for g in THEORY_GLOBS)


def read_lines(p):
    try:
        with open(p, encoding="utf-8") as f:
            return [ln.strip() for ln in f if ln.strip()]
    except FileNotFoundError:
        return []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--changed-files", required=True)
    ap.add_argument("--labels-file", required=True)
    ap.add_argument("--comments-file", required=True)
    args = ap.parse_args()

    changed = read_lines(args.changed_files)
    labels = set(read_lines(args.labels_file))
    comments_blob = ""
    try:
        with open(args.comments_file, encoding="utf-8") as f:
            comments_blob = f.read()
    except FileNotFoundError:
        pass

    theory_files = [f for f in changed if is_theory(f)]
    if not theory_files:
        print(
            "PASS: no theory-bearing paths in diff — Tier-3 label gate not applicable."
        )
        return 0

    print(f"Theory-bearing files in diff ({len(theory_files)}):")
    for f in theory_files[:20]:
        print(f"  - {f}")

    if TIER3_LABEL not in labels:
        print(
            f"::error::Tier-3 gate — this PR touches theory-bearing paths but lacks the "
            f"`{TIER3_LABEL}` label. The label is applied only AFTER Red Team → Gemini review "
            f"comments are posted. Theory PRs cannot merge without the review artifact "
            f"(FAULT-S4-001). Add `{TIER3_LABEL}` once the review has run."
        )
        return 1

    if not REVIEW_ARTIFACT.search(comments_blob):
        print(
            f"::error::Tier-3 gate — `{TIER3_LABEL}` is present but no Red Team / Gemini review "
            f"artifact was found in the PR comments. A bare label is a finding, not a pass "
            f"(anti-gaming). Post the Tier-3 review comments before labeling."
        )
        return 1

    print(f"PASS: `{TIER3_LABEL}` present + review artifact found in comments.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
