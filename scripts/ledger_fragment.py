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


class FragmentError(ValueError):
    pass


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


def read_fragments(changes_dir: Path = CHANGES_DIR) -> list:
    """All fragments on disk, each `(path, data)`, validated. Unordered — caller
    (scripts/ledger_version.py) derives merge order from git history, not from
    anything in this directory listing."""
    if not changes_dir.exists():
        return []
    out = []
    for path in sorted(changes_dir.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        validate_fragment(data, source=str(path))
        out.append((path, data))
    return out
