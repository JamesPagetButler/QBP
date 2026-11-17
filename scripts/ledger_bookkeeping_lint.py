#!/usr/bin/env python3
"""CI lint — QBP#817 variant A: a ledger-touching PR authors content only.

`scripts/cth_ledger_edit.py` already makes it impossible for a NEW confined
edit to declare `version`/`changelog`/`last_updated`. This lint is the
defense-in-depth backstop for the two things that tool can't see: (1) a diff
that bypassed `ledger_edit()` entirely (a hand-edited JSON), and (2) the
changes.d/ fragment-count rule, which is a repo-wide git-diff property, not a
single-file-edit property `cth_ledger_edit` could ever check.

Checks, comparing `--base` to `--head`:
  1. The ledger's `version`/`changelog`/`last_updated` are byte-identical to base.
  2. If the ledger changed at all, exactly one fragment was added under
     archive/cth-inventory/changes.d/ (never zero, never more than one).
  3. No fragment already on base was modified or removed (changes.d/ is append-only).
  4. The new fragment's `touched_ids` is exactly the set of anchor/record ids that
     actually changed — not a subset (an under-claimed fragment hides what the
     reviewer actually needs to re-derive) and not a superset (an over-claimed
     fragment pads the changelog view with ids nothing happened to). This is the
     automatable half of "the rebase reproduces exactly" (qbp-architecture, QBP#817
     ref. 1): CI can verify the fragment's claim against the diff for any encoder,
     without knowing that encoder's own CLI. The other half — re-running a specific
     PR's encoder against a fresh master and diffing the result — has no shared
     CLI contract across encoders to automate generically; it stays a documented,
     one-command-per-encoder manual recipe (docs/cth/qbp-local-extensions.md).

Usage:
    python3 scripts/ledger_bookkeeping_lint.py --base origin/master --head HEAD
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import _records  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER_REL = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
CHANGES_DIR_REL = "archive/cth-inventory/changes.d"


class LintFailure(RuntimeError):
    pass


def _show(ref: str, rel_path: str) -> str | None:
    result = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    return result.stdout if result.returncode == 0 else None


def _diff_status(base: str, head: str, rel_path: str) -> list:
    """[(status, path), ...] for rel_path (a file or a directory) between base and head."""
    out = subprocess.run(
        ["git", "diff", "--name-status", f"{base}..{head}", "--", rel_path],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    rows = []
    for line in out.splitlines():
        status, path = line.split("\t", 1)
        rows.append((status, path))
    return rows


def check_frozen_fields(base: str, head: str) -> list:
    errors: list = []
    base_raw = _show(base, LEDGER_REL)
    head_raw = _show(head, LEDGER_REL)
    if base_raw is None or head_raw is None:
        return (
            errors  # ledger doesn't exist at one of the refs — nothing to freeze-check
        )
    base_ledger = json.loads(base_raw)
    head_ledger = json.loads(head_raw)
    for key in ("version", "changelog", "last_updated"):
        if base_ledger.get(key) != head_ledger.get(key):
            errors.append(
                f"{key!r} differs from {base}: frozen by QBP#817 (variant A) — "
                f"add a fragment under {CHANGES_DIR_REL}/ instead, never edit this field."
            )
    return errors


def check_fragment_count(base: str, head: str) -> list:
    errors = []
    base_raw = _show(base, LEDGER_REL)
    head_raw = _show(head, LEDGER_REL)
    ledger_changed = (
        base_raw is not None and head_raw is not None and base_raw != head_raw
    )

    rows = _diff_status(base, head, CHANGES_DIR_REL)
    added = [p for s, p in rows if s == "A"]
    modified_or_removed = [p for s, p in rows if s in ("M", "D", "R100")]

    if modified_or_removed:
        errors.append(
            f"{CHANGES_DIR_REL}/ is append-only: modified/removed fragment(s) "
            f"{modified_or_removed}"
        )
    if len(added) > 1:
        errors.append(
            f"more than one fragment added in one PR: {added} — one PR, one fragment"
        )
    if ledger_changed and len(added) != 1:
        errors.append(
            f"the ledger changed but {len(added)} fragment(s) were added under "
            f"{CHANGES_DIR_REL}/ — exactly one is required"
        )
    return errors


def check_fragment_claims_diff(base: str, head: str) -> list:
    errors: list = []
    base_raw = _show(base, LEDGER_REL)
    head_raw = _show(head, LEDGER_REL)
    if base_raw is None or head_raw is None or base_raw == head_raw:
        return errors  # no ledger change to claim anything about

    rows = _diff_status(base, head, CHANGES_DIR_REL)
    added = [p for s, p in rows if s == "A"]
    if len(added) != 1:
        return errors  # already flagged by check_fragment_count

    fragment = json.loads(
        subprocess.run(
            ["git", "show", f"{head}:{added[0]}"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    )
    claimed = set(fragment["touched_ids"])

    b_recs, _ = _records(json.loads(base_raw))
    a_recs, _ = _records(json.loads(head_raw))
    actually_changed = set()
    for key in set(b_recs) | set(a_recs):
        bi, ai = b_recs.get(key, {}), a_recs.get(key, {})
        for rid in set(bi) | set(ai):
            if json.dumps(bi.get(rid)) != json.dumps(ai.get(rid)):
                actually_changed.add(rid)

    under = claimed - actually_changed
    over = actually_changed - claimed
    if under:
        errors.append(
            f"fragment {added[0]} claims touched_ids {sorted(under)} that did not "
            f"actually change"
        )
    if over:
        errors.append(
            f"fragment {added[0]} is missing touched_ids for {sorted(over)}, which "
            f"did actually change"
        )
    return errors


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--base", default="origin/master")
    ap.add_argument("--head", default="HEAD")
    args = ap.parse_args()

    errors = (
        check_frozen_fields(args.base, args.head)
        + check_fragment_count(args.base, args.head)
        + check_fragment_claims_diff(args.base, args.head)
    )
    if errors:
        for e in errors:
            print(f"FAIL: {e}")
        sys.exit(1)
    print(
        f"OK: bookkeeping frozen, fragment convention respected ({args.base}..{args.head})."
    )


if __name__ == "__main__":
    main()
