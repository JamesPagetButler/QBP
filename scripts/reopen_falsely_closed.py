#!/usr/bin/env python3
"""Post-merge backstop: auto-reopen any issue this push closed with unchecked ACs.

Layer 2 of the FAULT-S4-004 defence (layer 1 = check_closing_acs.py, a PR-time
guard that can be bypassed if it is not a required check or if a fresh closing
keyword is typed in the squash-merge box at merge time). This runs on push to the
default branch and is independent of branch protection: the worst case is an issue
is wrongly CLOSED for ~one CI run, then auto-reopened with a warning.

SAFETY — only ever undoes a SAME-PUSH auto-close, never fights a deliberate close:
  - acts only on issues referenced with a closing keyword in THIS push's commits,
  - only if the issue is now CLOSED with stateReason == COMPLETED,
  - only if it still has >=1 unchecked `- [ ] **AC` box.
A human closing an issue manually (no closing keyword in a pushed commit) is never
touched.

Usage:
  reopen_falsely_closed.py --commits-file pushed_commit_messages.txt [--dry-run]
"""

import argparse
import json
import subprocess
import sys

from check_closing_acs import closing_refs, count_unchecked_acs


def gh_json(args):
    out = subprocess.run(["gh", *args], capture_output=True, text=True, timeout=60)
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return out.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--commits-file", required=True)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    try:
        with open(args.commits_file, encoding="utf-8") as f:
            text = f.read()
    except FileNotFoundError:
        print("no commits file — nothing to do.")
        return 0

    refs = closing_refs(text)
    if not refs:
        print("no closing keywords in pushed commits — nothing to do.")
        return 0

    print(f"closing-keyword refs in this push: {sorted(refs)}")
    reopened = []
    for num in sorted(refs):
        info = gh_json(["issue", "view", str(num), "--json", "state,stateReason,body"])
        if not isinstance(info, dict):
            print(f"  #{num}: could not fetch — skipping")
            continue
        state = info.get("state")
        reason = info.get("stateReason")
        n_unmet = count_unchecked_acs(info.get("body", ""))
        if state == "CLOSED" and reason == "COMPLETED" and n_unmet > 0:
            print(
                f"  #{num}: CLOSED/COMPLETED with {n_unmet} unchecked AC(s) — REOPENING"
            )
            if args.dry_run:
                reopened.append(num)
                continue
            subprocess.run(["gh", "issue", "reopen", str(num)], timeout=60)
            warn = (
                f"## ⚠️ Auto-reopened (FAULT-S4-004 backstop)\n\n"
                f"This issue was closed by a `close/fix/resolve #{num}` keyword in a just-"
                f"merged commit, but it still has **{n_unmet} unchecked acceptance "
                f"criterion(a)**. A tracked issue never closes with open ACs. Reopened "
                f"automatically. Use `Refs #{num} (satisfies ACn)` instead of a closing "
                f"keyword; close manually once every AC is met and verified."
            )
            subprocess.run(
                ["gh", "issue", "comment", str(num), "--body", warn], timeout=60
            )
            reopened.append(num)
        else:
            print(
                f"  #{num}: state={state} reason={reason} unchecked_ACs={n_unmet} — no action"
            )

    if reopened:
        print(f"::warning::auto-reopened issues with unchecked ACs: {reopened}")
    return 0  # backstop never fails the build — it heals, it doesn't block


if __name__ == "__main__":
    sys.exit(main())
