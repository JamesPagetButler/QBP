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
# A real review leaves TWO marks: a reviewer SIGNATURE (who) and a VERDICT (judgment).
# Requiring both defeats FAULT-S4-003: the notifier's TECH-GREEN "review checklist"
# comment and the PR template body both *name* the reviewers ("Red Team review
# (Sabine/...)", "Gemini review (Furey/Feynman)") — a SIGNATURE without a VERDICT.
# A bare label backed only by those names is a rubber-stamp, not a review.
REVIEW_SIGNATURE = re.compile(
    r"Red Team|Gemini|§I4|Sabine|Grothendieck|Knuth|Furey|Feynman", re.IGNORECASE
)
# A rendered verdict — the thing only an actual review produces. The notifier's
# own verdicts ("ALL GREEN", "Tech-green", "Checks FAILED") deliberately contain
# none of these, so the notifier's comments can never satisfy the gate.
REVIEW_VERDICT = re.compile(
    r"\bAPPROVE\b|APPROVE-WITH-CONCERN|REQUEST\s+CHANGES|\bBLOCKING\b|\bDEFER\b",
    re.IGNORECASE,
)
# Notifier-authored comments carry this marker; they are stripped before matching
# so the notifier's reviewer-naming checklist cannot stand in for a real review.
NOTIFIER_MARKER = "<!-- pr-check-status-notifier -->"
# The workflow joins individual comment bodies with this boundary so the gate can
# evaluate each comment separately (signature + verdict must co-occur in ONE).
COMMENT_BOUNDARY = "===TIER3-COMMENT-BOUNDARY==="


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

    # A real review = ONE comment carrying BOTH a reviewer signature AND a rendered
    # verdict. Splitting per-comment (boundary emitted by the workflow) prevents a
    # signature in one comment and a stray verdict in another from combining into a
    # false pass. Notifier-authored comments are skipped: their checklist names the
    # reviewers (signature) but never renders a verdict, so they cannot stand in.
    blocks = comments_blob.split(COMMENT_BOUNDARY)
    real_review = False
    for block in blocks:
        if NOTIFIER_MARKER in block:
            continue  # notifier checklist / verdict — not a review
        if REVIEW_SIGNATURE.search(block) and REVIEW_VERDICT.search(block):
            real_review = True
            break

    if not real_review:
        print(
            f"::error::Tier-3 gate — `{TIER3_LABEL}` is present but no real review was found. "
            f"A review must be a single comment carrying BOTH a reviewer signature "
            f"(Red Team / Gemini / Sabine / Furey / ...) AND a rendered verdict "
            f"(APPROVE / APPROVE-WITH-CONCERN / REQUEST CHANGES / BLOCKING / DEFER). "
            f"The notifier's reviewer-naming checklist and the PR template do NOT count "
            f"(FAULT-S4-003 — a named-but-unrendered review is a rubber-stamp). "
            f"Run the Red Team → Gemini review and post the verdicts before merge."
        )
        return 1

    print(f"PASS: `{TIER3_LABEL}` present + a real review (signature + verdict) found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
