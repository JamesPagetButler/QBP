#!/usr/bin/env python3
"""Ledger change fragments — QBP#817 variant A (beekeeper-ruled 2026-11-16).

A content PR no longer authors `version`/`changelog`/`last_updated` on the CTH
ledger (scripts/cth_ledger_edit.py's `LedgerEdit.touch()` hard-blocks it). Instead
it adds exactly one fragment file here, under
`archive/cth-inventory/changes.d/<issue>-<slug>.json`. The fragment mirrors the
ledger's own `ChangelogEntry` shape (cth-implementor, live-test seq5141/5144) so
regen is a pure copy, never a re-authoring: `note` is the exact text a reviewer
signed off on, and `version`/`date` stay `null` in the PR — they are filled in
only by the derived view (scripts/ledger_version.py,
scripts/generate_ledger_changelog_view.py), never by a content PR.

Two extra fields beyond the bare ChangelogEntry mirror, needed for the generated
changelog view's columns ("derived version · merge time · issue · PR · note ·
touched anchor ids", beekeeper requirement on QBP#817): `pr` (the PR number) and
`touched_ids` (the anchor ids this fragment's content edit declared via
`cth_ledger_edit`). `encoder` records which script made the edit, for audit.

A fragment's filename encodes merge order indirectly — not by name, but by its
position in `git log --reverse` on master once merged (scripts/ledger_version.py
reads that order; a fragment's own content never claims an ordinal).
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from cth_ledger_edit import canonical_dump

REPO_ROOT = Path(__file__).resolve().parent.parent
CHANGES_DIR = REPO_ROOT / "archive/cth-inventory/changes.d"

REQUIRED_KEYS = (
    "issue",
    "slug",
    "pr",
    "encoder",
    "note",
    "touched_ids",
    "version",
    "date",
)

_SLUG_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

# The fragment naming convention itself, as a single pattern both
# `read_fragments` (below) and `ledger_bookkeeping_lint.py` fullmatch
# against — qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17, after N1
# (a non-ASCII filename quoting gap) and N2 (a dangling symlink passing CI
# and then breaking read_fragments after merge): a single shared `is_fragment`
# below is the only place either caller decides "is this a real fragment".
_FRAGMENT_FILENAME_RE = re.compile(r"[0-9]+-[a-z0-9]+(?:-[a-z0-9]+)*\.json")
REGULAR_FILE_MODE = "100644"


class FragmentError(ValueError):
    pass


def is_fragment(path: str, mode: str) -> bool:
    """True iff `path` is a real ledger fragment. `path` must already be
    expressed RELATIVE TO changes.d/ itself (e.g. `"1-a.json"`) — never a
    full repo-relative path; a caller working with full paths (the lint)
    strips its own known `changes.d/` prefix before calling this. `mode`
    must be the exact git-style mode string `"100644"` (a plain regular
    file) — never a symlink (`"120000"`), an executable (`"100755"`), or
    anything else (N2: a dangling symlink passed CI and then broke
    `read_fragments()` after merge, since nothing checked the entry's mode
    at all).

    Three conditions, all required:
      1. `mode == REGULAR_FILE_MODE` — a plain regular file, nothing else.
      2. No `"/"` in `path` at all — directly in changes.d/, never a
         subdirectory (the fragment-count side of the old E2 gap).
      3. `path` fullmatches the naming convention `<issue>-<slug>.json`
         exactly, via `re.fullmatch` — NOT `.match()` plus a trailing `"$"`
         (N1: `$`, by default, matches just before a FINAL trailing
         newline too, so `.match(pattern + "$", "1-a.json\\n")` succeeds
         even though the real name has a stray newline appended; a
         `git diff` row can produce exactly this for a maliciously- or
         accidentally-named path. `fullmatch` requires the match to
         consume the entire string, which that trailing `\\n` can't
         satisfy, closing the gap outright rather than patching it
         filename-shape by filename-shape).

    This is the ONLY place either `read_fragments` (the real filesystem
    reader) or `ledger_bookkeeping_lint.py` (the CI backstop, reading git
    diff rows) decides what counts as a fragment — so there is exactly one
    definition for the two to agree on, instead of two independently
    maintained filters that can silently drift apart (E1/E3's actual root
    cause)."""
    if mode != REGULAR_FILE_MODE:
        return False
    if "/" in path:
        return False
    return bool(_FRAGMENT_FILENAME_RE.fullmatch(path))


def fragment_path(issue: int, slug: str, changes_dir: Path = CHANGES_DIR) -> Path:
    if not _SLUG_RE.match(slug):
        raise FragmentError(
            f"slug {slug!r} must be kebab-case (lowercase, digits, hyphens)"
        )
    return changes_dir / f"{issue}-{slug}.json"


def build_fragment(
    *, issue: int, slug: str, pr: int, encoder: str, note: str, touched_ids: list
) -> dict:
    """The fragment's content, as it reads inside an open PR: `version`/`date`
    stay null — the regen step (scripts/ledger_version.py's consumers) fills
    them in only once this fragment is on master, never before."""
    if not note.strip():
        raise FragmentError("note must be non-empty")
    if not touched_ids:
        raise FragmentError(
            "touched_ids must be non-empty — a fragment with no "
            "anchor edits has nothing for the changelog view to cite"
        )
    return {
        "issue": issue,
        "slug": slug,
        "pr": pr,
        "encoder": encoder,
        "note": note,
        "touched_ids": sorted(touched_ids),
        "version": None,
        "date": None,
    }


def write_fragment(
    *,
    issue: int,
    slug: str,
    pr: int,
    encoder: str,
    note: str,
    touched_ids: list,
    changes_dir: Path = CHANGES_DIR,
    dry_run: bool = False,
) -> Path:
    path = fragment_path(issue, slug, changes_dir)
    if path.exists():
        raise FragmentError(f"{path} already exists — one fragment per issue+slug")
    fragment = build_fragment(
        issue=issue,
        slug=slug,
        pr=pr,
        encoder=encoder,
        note=note,
        touched_ids=touched_ids,
    )
    out = canonical_dump(fragment)
    if not dry_run:
        changes_dir.mkdir(parents=True, exist_ok=True)
        path.write_text(out, encoding="utf-8")
    return path


def validate_fragment(data: dict, source: str = "<fragment>") -> None:
    missing = [k for k in REQUIRED_KEYS if k not in data]
    if missing:
        raise FragmentError(f"{source}: missing required key(s) {missing}")
    extra = [k for k in data if k not in REQUIRED_KEYS]
    if extra:
        raise FragmentError(f"{source}: unexpected key(s) {extra}")
    if not isinstance(data["touched_ids"], list) or not data["touched_ids"]:
        raise FragmentError(f"{source}: touched_ids must be a non-empty list")
    if not isinstance(data["note"], str) or not data["note"].strip():
        raise FragmentError(f"{source}: note must be a non-empty string")


def _fs_mode(path: Path) -> str:
    """The real filesystem entry's mode, expressed as the same git-style
    string `is_fragment` checks against — a symlink is `"120000"`
    regardless of what it points at (N2: never followed, never read), an
    executable regular file is `"100755"`, anything else that isn't a
    plain file (a directory, a fifo, ...) is `"040000"` (never a fragment
    either way), and a plain non-executable regular file is
    `REGULAR_FILE_MODE`."""
    if path.is_symlink():
        return "120000"
    if not path.is_file():
        return "040000"
    if path.stat().st_mode & 0o111:
        return "100755"
    return REGULAR_FILE_MODE


def read_fragments(changes_dir: Path = CHANGES_DIR) -> list:
    """All fragments on disk, each `(path, data)`, validated. Unordered — caller
    (scripts/ledger_version.py) derives merge order from git history, not from
    anything in this directory listing. Each entry must pass `is_fragment` —
    the same check `ledger_bookkeeping_lint.py` runs against the git diff —
    so a dangling symlink (N2) or anything else that isn't a plain,
    correctly-named regular file is skipped here rather than attempted
    and crashing."""
    if not changes_dir.exists():
        return []
    out = []
    for path in sorted(changes_dir.iterdir()):
        if not is_fragment(path.name, _fs_mode(path)):
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        validate_fragment(data, source=str(path))
        out.append((path, data))
    return out
