#!/usr/bin/env python3
"""Guard: a PR may not auto-close an issue that still has unchecked AC boxes.

FAULT-S4-004 fix. GitHub auto-closes issue #N on merge when a PR body or commit
says `close[s|d] / fix[es|ed] / resolve[s|d] #N` (the trailing "AC2" in
"closes #474 AC2" is IGNORED by GitHub). So satisfying ONE acceptance criterion
of a parent tracking issue silently closes the whole parent. This check fails the
PR BEFORE the merge, so the author switches to `Refs #N (satisfies ACn)`.

Logic:
  1. Find every issue # referenced with a GitHub closing keyword in the PR text.
  2. For each, fetch the issue body; count unchecked `- [ ] **AC...` boxes.
  3. Any closing-ref to an issue with >=1 unchecked AC -> FAIL.

A `- [ ]` AC box is the practical signature of a *tracked* issue (parent/research
issue with acceptance criteria); closing one with open ACs is the violation.

Usage:
  check_closing_acs.py --text-file pr_text.txt
  # issue bodies are fetched via `gh`; for tests pass --issue-body-dir DIR
  # containing <N>.md files to use instead of calling gh.
"""

import argparse
import os
import re
import subprocess
import sys

# GitHub's documented closing keywords, followed by an optional space and #<num>.
CLOSING = re.compile(
    r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\b\s*:?\s+#(\d+)",
    re.IGNORECASE,
)
UNCHECKED_AC = re.compile(r"^\s*-\s*\[\s\]\s*\*\*AC", re.MULTILINE)


def closing_refs(text):
    """Return the set of issue numbers referenced with a closing keyword."""
    return {int(m) for m in CLOSING.findall(text)}


def count_unchecked_acs(body):
    return len(UNCHECKED_AC.findall(body or ""))


def fetch_issue_body(num, issue_body_dir=None):
    if issue_body_dir:
        path = os.path.join(issue_body_dir, f"{num}.md")
        try:
            with open(path, encoding="utf-8") as f:
                return f.read()
        except FileNotFoundError:
            return ""
    try:
        out = subprocess.run(
            ["gh", "issue", "view", str(num), "--json", "body", "--jq", ".body"],
            capture_output=True,
            text=True,
            timeout=60,
        )
        return out.stdout if out.returncode == 0 else ""
    except Exception:
        return ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--text-file", required=True)
    ap.add_argument("--issue-body-dir", default=None)
    args = ap.parse_args()

    try:
        with open(args.text_file, encoding="utf-8") as f:
            text = f.read()
    except FileNotFoundError:
        print("PASS: no PR text to scan.")
        return 0

    refs = closing_refs(text)
    if not refs:
        print("PASS: no closing keywords (close/fix/resolve #N) in PR text.")
        return 0

    print(f"Closing-keyword references found: {sorted(refs)}")
    violations = []
    for num in sorted(refs):
        body = fetch_issue_body(num, args.issue_body_dir)
        n_unmet = count_unchecked_acs(body)
        if n_unmet > 0:
            violations.append((num, n_unmet))
            print(
                f"  #{num}: {n_unmet} unchecked AC box(es) — closing it is a violation"
            )
        else:
            print(f"  #{num}: no unchecked AC boxes — ok to close")

    if violations:
        for num, n in violations:
            print(
                f"::error::PR would auto-close #{num} which still has {n} unchecked "
                f"acceptance criterion(a). A parent/tracked issue never closes with open "
                f"ACs (FAULT-S4-004). Use `Refs #{num} (satisfies ACn)` instead of a "
                f"closing keyword; the beekeeper closes #{num} manually when all ACs are met."
            )
        return 1

    print("PASS: no closing keyword targets an issue with unchecked ACs.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
