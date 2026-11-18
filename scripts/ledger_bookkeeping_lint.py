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
  3. No fragment already on base was touched at all — added, modified, removed,
     renamed (any similarity score) or type-changed; changes.d/ is append-only,
     so anything other than a clean new addition fails (D4, qbp-oppenheimer,
     QBP#817 PR-1 review, 2026-11-17: a partial-similarity rename, e.g. git's
     "R087", slipped past the original "M/D/R100-only" check).
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
  5. analysis/cth-ledger-changelog.md never appears in the diff at all (D1,
     qbp-oppenheimer, QBP#817 PR-1 review, 2026-11-17): that view is CI-published
     post-merge, never committed (scripts/generate_ledger_changelog_view.py) — a
     hand-committed copy would have to be kept in sync by every later content PR,
     reintroducing the exact bookkeeping collision this design removes.

Usage:
    python3 scripts/ledger_bookkeeping_lint.py --base origin/master --head HEAD
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import _records  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER_REL = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
CHANGES_DIR_REL = "archive/cth-inventory/changes.d"
CHANGELOG_VIEW_REL = "analysis/cth-ledger-changelog.md"

# A fragment's real naming convention (ledger_fragment.fragment_path /
# _SLUG_RE): "<issue>-<slug>.json", lowercase-ascii-and-digits only, directly
# under CHANGES_DIR_REL — never a subdirectory. E3 (qbp-architecture, QBP#817
# PR-1 re-confirm, 2026-11-17) requires every added path to match this
# exactly, not merely end in ".json".
_FRAGMENT_FILENAME_RE = re.compile(r"^[0-9]+-[a-z0-9]+(?:-[a-z0-9]+)*\.json$")


class LintFailure(RuntimeError):
    pass


def _merge_base(base: str, head: str) -> str:
    """The commit `base` and `head` actually diverged from — F4' (qbp-
    architecture, QBP#817 PR-1 review, 2026-11-17): `_show(base, ...)` used to
    read `base`'s literal tip, same bug class as the two-dot/F4 diff fix, just
    not yet applied to the frozen-field and touched_ids content comparisons.
    `main()` resolves this once and passes it as the effective base to every
    check, so a `--base` that has moved further ahead than this branch's own
    divergence point (e.g. a stale local `origin/master`) can't make an
    unrelated master-side edit look like this branch's own change."""
    return subprocess.run(
        ["git", "merge-base", base, head],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _show(ref: str, rel_path: str) -> str | None:
    result = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    return result.stdout if result.returncode == 0 else None


def _diff_status(base: str, head: str, rel_path: str) -> list:
    """[(status, old_path, new_path), ...] for rel_path (a file or a directory)
    between base and head. Three-dot (merge-base) diff, not two-dot
    (qbp-oppenheimer, QBP#817 PR-1 re-confirm, 2026-11-17, nit): two-dot diffs
    base's literal tree against head's, so a local checkout whose `base` ref
    (e.g. `origin/master`) has moved further ahead than this branch's own
    merge-base would falsely report every fragment master gained in between
    as "modified" on this branch — the append-only check would then fail for
    a reason that isn't this branch's own change. Three-dot diffs against the
    merge-base instead, so only what THIS branch actually did since it
    diverged ever shows up, regardless of how far base has moved since.

    For a rename/copy row, `git diff --name-status` prints three fields
    (status, old path, new path); every other status prints two. Run with
    `-z` (NUL-delimited, no C-style quoting) rather than the default
    newline/tab-delimited form — E3 (qbp-architecture, QBP#817 PR-1
    re-confirm, 2026-11-17): git quotes-and-octal-escapes a non-ASCII path by
    default (wrapping it in literal double quotes), so a caller checking a
    plain `.endswith(".json")` suffix on the returned string silently missed
    a real `changes.d/2-é.json` row — invisible to every check in this file
    while still fully visible to `ledger_fragment.read_fragments()`'s real
    filesystem glob, which doesn't go through git at all. `-z` sidesteps the
    quoting entirely rather than trying to un-quote it. (E1, same file, same
    review round: a rename row's old/new paths are both returned explicitly
    too, so a rename away from the fragment naming convention is still
    caught, not just a rename into it.)"""
    out = subprocess.run(
        ["git", "diff", "--name-status", "-z", f"{base}...{head}", "--", rel_path],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    tokens = out.split("\0")
    if tokens and tokens[-1] == "":
        tokens.pop()
    rows = []
    i = 0
    while i < len(tokens):
        status = tokens[i]
        i += 1
        if status[:1] in ("R", "C"):
            old_path, new_path = tokens[i], tokens[i + 1]
            i += 2
        else:
            old_path = new_path = tokens[i]
            i += 1
        rows.append((status, old_path, new_path))
    return rows


def _is_fragment_path(path: str) -> bool:
    """True iff `path` is exactly `<issue>-<slug>.json` directly under
    CHANGES_DIR_REL — never a subdirectory (E2) and never anything a mere
    `.endswith(".json")` would have let through (E3)."""
    prefix = CHANGES_DIR_REL + "/"
    if not path.startswith(prefix):
        return False
    return bool(_FRAGMENT_FILENAME_RE.match(path[len(prefix) :]))


def _fragment_rows(base: str, head: str) -> list:
    """[(status, old_path, new_path), ...] under CHANGES_DIR_REL, minus
    changes.d/README.md itself (by exact path on both ends — it documents
    the convention and is never a fragment) — shared by every
    fragment-counting/claims check so the filter can't drift between them
    (E1). E3 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): this no
    longer filters by `.endswith(".json")` at all — every surviving row is
    "fragment-relevant" for append-only purposes, and `check_fragment_count`
    separately validates any ADDED row's path against `_is_fragment_path`,
    so a badly-named addition (wrong extension, wrong directory, non-ASCII)
    is rejected outright instead of silently excluded from `added` and never
    checked at all."""
    readme = f"{CHANGES_DIR_REL}/README.md"
    rows = []
    for status, old_path, new_path in _diff_status(base, head, CHANGES_DIR_REL):
        if old_path == readme and new_path == readme:
            continue
        rows.append((status, old_path, new_path))
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

    # changes.d/README.md documents the convention and is not a fragment
    # (found while verifying this PR's own diff against master: this PR's
    # own one-time README.md addition showed up as "A" here and crashed
    # check_fragment_claims_diff trying to json.loads() a markdown file).
    # README.md stays freely editable; `_fragment_rows` already exempts it
    # by exact path. Every other row under changes.d/ is fragment-relevant.
    rows = _fragment_rows(base, head)
    added = [new for s, old, new in rows if s == "A"]
    # D4: anything other than a clean "A" is a touch of an existing fragment —
    # M(odified), D(eleted), any R(ename) regardless of similarity score
    # (git reports "R100" only for a byte-identical rename; a partial-content
    # rename like "R087" slipped past an "s == 'R100'" check), C(opy), T(ype
    # change). Append-only means append-only.
    modified_or_removed = [new for s, old, new in rows if s != "A"]

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
    # E2/E3 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): every
    # added path must be exactly "<issue>-<slug>.json" directly under
    # CHANGES_DIR_REL. E2: a subdirectory path (changes.d/sub/x.json) passes
    # every check above — the diff pathspec is recursive — but
    # ledger_fragment.read_fragments() only globs changes.d/*.json directly,
    # so it never sees it there. E3: a non-ASCII or otherwise malformed name
    # must not be silently dropped out of `added` either (that was this
    # check's OWN earlier mistake, before E3's fix to `_fragment_rows`) — it
    # is rejected outright as an invalid name instead.
    invalid = [p for p in added if not _is_fragment_path(p)]
    if invalid:
        errors.append(
            f"fragment(s) not named '<issue>-<slug>.json' directly under "
            f"{CHANGES_DIR_REL}/: {invalid} — read_fragments() only recognizes "
            f"that exact pattern in that exact directory"
        )
    return errors


def check_fragment_claims_diff(base: str, head: str) -> list:
    """F2 (qbp-architecture, QBP#817 PR-1 review, 2026-11-17): this no longer
    early-returns just because the ledger is byte-identical at base/head. A
    fragment added with the ledger UNCHANGED is always an over-claim — a
    fragment's touched_ids can never legitimately be non-empty
    (ledger_fragment.py's build_fragment() refuses an empty list) if nothing
    in the ledger actually changed, so skipping the check there let a bogus
    fragment (claiming ids, with no matching edit) through CI, and it then
    earned a real derived version bump in the published view."""
    errors: list = []
    rows = _fragment_rows(base, head)
    added = [new for s, old, new in rows if s == "A"]
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

    base_raw = _show(base, LEDGER_REL)
    head_raw = _show(head, LEDGER_REL)
    if base_raw is None or head_raw is None:
        return errors  # ledger doesn't exist at one of the refs — nothing to compare

    b_recs, _ = _records(json.loads(base_raw))
    a_recs, _ = _records(json.loads(head_raw))
    actually_changed = set()
    for key in set(b_recs) | set(a_recs):
        bi, ai = b_recs.get(key, {}), a_recs.get(key, {})
        for rid in set(bi) | set(ai):
            if json.dumps(bi.get(rid)) != json.dumps(ai.get(rid)):
                actually_changed.add(rid)

    # F8 (qbp-architecture): names were inverted relative to their meaning —
    # `over_claimed` is what's claimed but didn't change (an OVER-claim);
    # `under_claimed` is what changed but wasn't claimed (an UNDER-claim).
    # The messages were already correct; only the variable names were swapped.
    over_claimed = claimed - actually_changed
    under_claimed = actually_changed - claimed
    if over_claimed:
        errors.append(
            f"fragment {added[0]} claims touched_ids {sorted(over_claimed)} that did "
            f"not actually change"
        )
    if under_claimed:
        errors.append(
            f"fragment {added[0]} is missing touched_ids for {sorted(under_claimed)}, "
            f"which did actually change"
        )
    return errors


def check_changelog_view_not_committed(base: str, head: str) -> list:
    rows = _diff_status(base, head, CHANGELOG_VIEW_REL)
    if rows:
        return [
            f"{CHANGELOG_VIEW_REL} must never be committed (D1): it is CI-published "
            f"post-merge, never a tracked file — remove it from this PR's diff "
            f"({[s for s, _, _ in rows]})"
        ]
    return []


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--base", default="origin/master")
    ap.add_argument("--head", default="HEAD")
    args = ap.parse_args()

    # F4' — resolve once, use everywhere: every check below compares against
    # the true divergence point, never against --base's literal (possibly
    # stale-locally-ahead) tip.
    merge_base = _merge_base(args.base, args.head)

    errors = (
        check_frozen_fields(merge_base, args.head)
        + check_fragment_count(merge_base, args.head)
        + check_fragment_claims_diff(merge_base, args.head)
        + check_changelog_view_not_committed(merge_base, args.head)
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
