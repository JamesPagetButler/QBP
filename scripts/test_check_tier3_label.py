#!/usr/bin/env python3
"""Tests for the Tier-3 review-label gate (scripts/check_tier3_label.py).

Covers the FAULT-S4-003 signature+verdict logic AND the FAULT-S4-006 regression:
the PR body must NOT be able to satisfy the gate (an author's prose containing a
signature-word next to a verdict-word passed the gate with zero real review on
PR #612/#614). Run: python3 scripts/test_check_tier3_label.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_tier3_label.py")
WORKFLOW = os.path.join(HERE, "..", ".github", "workflows", "tier-3-review-gate.yml")
BOUND = "\n===TIER3-COMMENT-BOUNDARY===\n"


def run(changed, labels, comments_blob):
    with tempfile.TemporaryDirectory() as d:
        cf = os.path.join(d, "changed.txt")
        open(cf, "w").write("\n".join(changed))
        lf = os.path.join(d, "labels.txt")
        open(lf, "w").write("\n".join(labels))
        mf = os.path.join(d, "comments.txt")
        open(mf, "w").write(comments_blob)
        r = subprocess.run(
            [
                sys.executable,
                SCRIPT,
                "--changed-files",
                cf,
                "--labels-file",
                lf,
                "--comments-file",
                mf,
            ],
            capture_output=True,
            text=True,
        )
        return r.returncode


def run_json(changed, labels, comments):
    """Like run() but feeds raw GitHub-API-shaped comment JSON via --comments-json (#552)."""
    with tempfile.TemporaryDirectory() as d:
        cf = os.path.join(d, "changed.txt")
        open(cf, "w").write("\n".join(changed))
        lf = os.path.join(d, "labels.txt")
        open(lf, "w").write("\n".join(labels))
        jf = os.path.join(d, "comments.json")
        open(jf, "w").write(json.dumps(comments))
        r = subprocess.run(
            [
                sys.executable,
                SCRIPT,
                "--changed-files",
                cf,
                "--labels-file",
                lf,
                "--comments-json",
                jf,
            ],
            capture_output=True,
            text=True,
        )
        return r.returncode


REVIEW = "# Red Team Review\nVerdict: APPROVE\n— Red Team (Sabine)"


def c(body, assoc, login="someone"):
    return {"body": body, "author_association": assoc, "user": {"login": login}}


# #552 security fix: only insider-authored comments may satisfy the review half.
JSON_CASES = [
    # (name, changed, labels, comments, expected_exit)
    (
        "#552: real review by COLLABORATOR → PASS",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [c(REVIEW, "COLLABORATOR", "qbp-architecture")],
        0,
    ),
    (
        "#552: real review by OWNER → PASS",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [c(REVIEW, "OWNER", "JamesPagetButler")],
        0,
    ),
    (
        "#552: identical review text by NONE (outsider) → FAIL",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [c(REVIEW, "NONE", "drive-by-account")],
        1,
    ),
    (
        "#552: CONTRIBUTOR / FIRST_TIMER are not trusted → FAIL",
        ["archive/cth-inventory/inv.json"],
        ["tier-3-review"],
        [c(REVIEW, "CONTRIBUTOR"), c(REVIEW, "FIRST_TIME_CONTRIBUTOR")],
        1,
    ),
    (
        "#552: outsider review + insider non-review chatter → FAIL (no combining)",
        ["archive/cth-inventory/inv.json"],
        ["tier-3-review"],
        [c(REVIEW, "NONE"), c("thanks, looking", "MEMBER")],
        1,
    ),
    (
        "#552: outsider noise + one real insider review → PASS",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [c(REVIEW, "NONE"), c(REVIEW, "MEMBER", "qbp-implementor")],
        0,
    ),
    (
        "#552: missing author_association field → treated as untrusted → FAIL",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [{"body": REVIEW, "user": {"login": "x"}}],
        1,
    ),
    (
        "#552: empty JSON array → FAIL",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        [],
        1,
    ),
]

CASES = [
    # (name, changed, labels, comments_blob, expected_exit)
    ("non-theory diff → PASS", ["README.md"], [], "", 0),
    ("theory diff, no label → FAIL", ["proofs/QBP/Foundations/X.lean"], [], "", 1),
    (
        "theory diff, label, notifier-only → FAIL",
        ["archive/cth-inventory/inv.json"],
        ["tier-3-review"],
        "<!-- pr-check-status-notifier -->\n## ALL GREEN — Red Team / Gemini checklist APPROVE",
        1,
    ),
    (
        "theory diff, label, real review comment (sig+verdict) → PASS",
        ["proofs/QBP/Foundations/X.lean"],
        ["tier-3-review"],
        "# Red Team Review\nVerdict: APPROVE\n— Red Team (Sabine)",
        0,
    ),
    (
        "sig in one block + verdict in another → FAIL",
        ["archive/cth-inventory/inv.json"],
        ["tier-3-review"],
        "Red Team is reviewing" + BOUND + "looks good, APPROVE from me",
        1,
    ),
    # FAULT-S4-006: author-body prose (sig-word + verdict-word) as a lone block must NOT pass.
    # (Belt-and-braces: even if the body were re-fed, the gate should still require a real
    #  reviewer comment. This asserts the block-matching alone doesn't rescue incidental prose
    #  — here the "review" is NOT a real one because the workflow no longer supplies the body,
    #  so with only this block present the gate must FAIL.)
    (
        "FAULT-S4-006: no comments at all, only would-be body prose absent → FAIL",
        ["archive/cth-inventory/inv.json"],
        ["tier-3-review"],
        "",
        1,
    ),
]


def main():
    failures = 0
    for name, changed, labels, blob, exp in CASES:
        got = run(changed, labels, blob)
        ok = got == exp
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        failures += not ok

    for name, changed, labels, comments, exp in JSON_CASES:
        got = run_json(changed, labels, comments)
        ok = got == exp
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        failures += not ok

    # #552 workflow guard: the gate must consume RAW comment JSON (author_association intact)
    # via --comments-json, never pre-joined bodies that have lost the trust field.
    wf = open(WORKFLOW, encoding="utf-8").read()
    trust_ok = (
        "--comments-json" in wf
        and "author_association" in wf
        and "--comments-file" not in wf
    )
    print(
        f"  [{'PASS' if trust_ok else 'FAIL'}] #552 guard: workflow feeds raw JSON with author_association"
    )
    failures += not trust_ok

    # FAULT-S4-006 regression guard: the workflow must NOT pipe the PR *body* into the
    # comments file. If this reappears, an author's prose can satisfy the gate again.
    body_fed = (
        "pulls/${PR}" in wf
        and "--jq '.body'" in wf
        and "comments.txt" in wf.split("--jq '.body'")[1][:80]
    )
    guard_ok = not body_fed
    print(
        f"  [{'PASS' if guard_ok else 'FAIL'}] FAULT-S4-006 guard: PR body NOT fed into the gate"
    )
    failures += not guard_ok

    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll Tier-3 gate tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
