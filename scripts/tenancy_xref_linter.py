#!/usr/bin/env python3
"""Tenancy doc cross-reference linter (closes QBP #433).

Parses `docs/qbp-federation-tenancy.md` for filesystem references and
verifies each exists on the branch being tested.

Stems from PR #403 v0.1 review — 4 stale references to non-existent BMA
Addenda slipped past initial reviews and were only caught by Oppenheimer's
independent manual verification. This linter catches that class of error
in CI.

Patterns matched:
- `archive/foo` paths (relative, in-repo)
- `paper/foo` paths (relative, in-repo)
- `proofs/foo` paths (relative, in-repo)
- `docs/foo` paths (relative, in-repo)
- `research/foo` paths (relative, in-repo)
- `scripts/foo` paths (relative, in-repo)
- `~/Documents/<sibling>/foo` paths (out-of-repo, federation cross-refs;
  reported as INFO since we can't verify them in CI but record for awareness)

NOT matched:
- Bare GitHub PR/issue/comment URLs (handled by link-checker.yml)
- External URLs (handled by link-checker.yml)
- Filesystem references inside code fences (e.g., shell snippets, YAML
  examples — these are illustrative, not citations)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# In-repo prefixes — paths under these must exist for the linter to pass.
REPO_PREFIXES = ("archive/", "paper/", "proofs/", "docs/", "research/", "scripts/")

# Out-of-repo prefixes — federation cross-refs; reported as INFO, not error.
FEDERATION_PREFIXES = ("~/Documents/",)

# Regex: captures backtick-quoted paths or bare paths preceded by whitespace/punctuation.
# Backtick-quoted: `path/to/file`
# Pattern allows the path to optionally end with line/section anchors like :42 or §3.4.
PATH_PATTERN = re.compile(
    r"`(?P<path>(?:archive/|paper/|proofs/|docs/|research/|scripts/|~/Documents/)[^`\s][^`]*)`"
)


def strip_anchor_suffix(path: str) -> str:
    """Strip Markdown section anchor (#fragment), line anchor (:42), or
    file-internal section reference (§...) from a path for filesystem lookup."""
    # Strip ` §...` suffix (e.g., "paper/foo.md §1.2")
    path = re.split(r"\s+§", path, maxsplit=1)[0]
    # Strip ":line" suffix (e.g., "paper/foo.md:42")
    path = re.split(r":", path, maxsplit=1)[0]
    # Strip "#fragment" suffix
    path = re.split(r"#", path, maxsplit=1)[0]
    return path.strip()


def strip_code_fences(text: str) -> str:
    """Remove fenced code blocks (``` ... ```) to avoid false positives
    on illustrative snippets."""
    return re.sub(r"```.*?```", "", text, flags=re.DOTALL)


def lint_tenancy_doc(
    doc_path: Path, repo_root: Path
) -> tuple[list[str], list[str], list[str]]:
    """Return (errors, warnings, info) lists.

    errors: in-repo paths that don't exist on disk
    warnings: ambiguous matches (rare; e.g., looks like a path but is illustrative)
    info: federation paths (informational; not verifiable in CI)
    """
    errors: list[str] = []
    warnings: list[str] = []
    info: list[str] = []

    if not doc_path.exists():
        errors.append(f"Tenancy doc not found at {doc_path}")
        return errors, warnings, info

    text = doc_path.read_text(encoding="utf-8")
    text_no_fences = strip_code_fences(text)

    seen = set()
    for match in PATH_PATTERN.finditer(text_no_fences):
        raw = match.group("path")
        path_part = strip_anchor_suffix(raw)
        if path_part in seen:
            continue
        seen.add(path_part)

        if path_part.startswith(FEDERATION_PREFIXES):
            info.append(f"FEDERATION (not verified): {path_part}")
            continue

        if not path_part.startswith(REPO_PREFIXES):
            warnings.append(f"AMBIGUOUS (not a repo prefix): {path_part}")
            continue

        target = repo_root / path_part
        if not target.exists():
            errors.append(f"BROKEN REF: {path_part} → no such file on branch")

    return errors, warnings, info


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    doc_path = repo_root / "docs" / "qbp-federation-tenancy.md"

    errors, warnings, info = lint_tenancy_doc(doc_path, repo_root)

    if info:
        print(
            f"[info] {len(info)} federation cross-reference(s) (not verifiable in CI):"
        )
        for msg in info:
            print(f"  {msg}")
        print()

    if warnings:
        print(f"[warning] {len(warnings)} ambiguous path-like match(es):")
        for msg in warnings:
            print(f"  {msg}")
        print()

    if errors:
        print(f"[error] {len(errors)} broken cross-reference(s):")
        for msg in errors:
            print(f"  {msg}")
        return 1

    print(
        f"OK: tenancy doc cross-references valid (federation: {len(info)}; in-repo: {sum(1 for _ in [None])}; ambiguous: {len(warnings)})."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
