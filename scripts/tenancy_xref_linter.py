#!/usr/bin/env python3
"""Tenancy doc cross-reference linter (QBP #433 AC1; #738 ACs 1-2).

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
  reported as INFO unless annotated — see below)

Federation refs and the `expected-on-sibling` annotation (#738):
  A federation ref may be annotated with an HTML comment on the SAME line
  or on the line IMMEDIATELY AFTER it::

      `~/Documents/Contextus/doc/contextus-tenancy-pattern.md`
      <!-- expected-on-sibling: Contextus doc/contextus-tenancy-pattern.md -->

  The annotation declares the sibling repo (one path component) and the
  path inside it. It binds by path identity: `~/Documents/<repo>/<path>`
  must equal a federation ref on that line or the preceding one, otherwise
  the annotation is an ORPHAN and the lint FAILS (an annotation that binds
  to nothing would otherwise be a silent no-op). `..` segments, absolute
  paths and a `repo` with a slash are MALFORMED and also FAIL.

  Sibling checkouts are looked up under `$QBP_SIBLING_ROOT` (or
  `--sibling-root`), defaulting to `~/Documents`:
    - sibling dir present and path exists   -> VERIFIED       (PASS)
    - sibling dir present and path missing  -> BROKEN SIBLING (FAIL, exit 1)
    - sibling dir absent (e.g. CI)          -> INFO "not verifiable here"
  Unannotated federation refs stay INFO ("not verified"), exactly as before.
  There is never a silent pass: every annotated ref is reported as one of
  VERIFIED / BROKEN SIBLING / not verifiable here.

Exit codes: 0 OK; 1 on any FAIL (in-repo broken ref, broken sibling ref,
orphan or malformed annotation, missing doc).

NOT matched:
- Bare GitHub PR/issue/comment URLs (handled by link-checker.yml)
- External URLs (handled by link-checker.yml)
- Filesystem references (and annotations) inside code fences — these are
  illustrative, not citations
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# In-repo prefixes — paths under these must exist for the linter to pass.
REPO_PREFIXES = ("archive/", "paper/", "proofs/", "docs/", "research/", "scripts/")

# Out-of-repo prefixes — federation cross-refs; INFO unless annotated.
FEDERATION_PREFIX = "~/Documents/"
FEDERATION_PREFIXES = (FEDERATION_PREFIX,)

# Env var naming the directory that holds sibling checkouts (default ~/Documents).
SIBLING_ROOT_ENV = "QBP_SIBLING_ROOT"

# Regex: captures backtick-quoted paths.
# Backtick-quoted: `path/to/file`
# Pattern allows the path to optionally end with line/section anchors like :42 or §3.4.
PATH_PATTERN = re.compile(
    r"`(?P<path>(?:archive/|paper/|proofs/|docs/|research/|scripts/|~/Documents/)[^`\s][^`]*)`"
)

# `<!-- expected-on-sibling: <repo> <path> -->` — repo and path are whitespace-free.
ANNOTATION_PATTERN = re.compile(
    r"<!--\s*expected-on-sibling:\s*(?P<repo>\S+)\s+(?P<path>\S+)\s*-->"
)


@dataclass
class LintResult:
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    info: list[str] = field(default_factory=list)
    verified: list[str] = field(default_factory=list)
    in_repo_checked: int = 0
    federation_total: int = 0
    federation_annotated: int = 0
    federation_verified: int = 0
    federation_unverifiable: int = 0

    @property
    def ok(self) -> bool:
        return not self.errors


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
    """Blank out fenced code blocks (``` ... ```) to avoid false positives
    on illustrative snippets. Newlines inside the fence are preserved so
    line numbers (and same-line / next-line annotation adjacency) survive."""
    return re.sub(
        r"```.*?```", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.DOTALL
    )


def validate_annotation(repo: str, path: str) -> str | None:
    """Return a reason string if the annotation is malformed, else None."""
    if "/" in repo or "\\" in repo or repo in (".", ".."):
        return f"repo {repo!r} must be a single path component"
    if path.startswith("/") or path.startswith("~"):
        return f"path {path!r} must be relative to the sibling repo"
    if ".." in path.split("/"):
        return f"path {path!r} must not contain '..'"
    return None


def default_sibling_root() -> Path:
    override = os.environ.get(SIBLING_ROOT_ENV)
    if override:
        return Path(override).expanduser()
    return Path.home() / "Documents"


def lint_tenancy_doc(
    doc_path: Path, repo_root: Path, sibling_root: Path | None = None
) -> LintResult:
    """Lint one doc. See module docstring for the contract."""
    res = LintResult()
    if sibling_root is None:
        sibling_root = default_sibling_root()

    if not doc_path.exists():
        res.errors.append(f"Tenancy doc not found at {doc_path}")
        return res

    text = doc_path.read_text(encoding="utf-8")
    lines = strip_code_fences(text).split("\n")

    # Pass 1: collect refs per line (dedup by stripped path, first occurrence wins).
    ordered_paths: list[str] = []
    seen: set[str] = set()
    refs_by_line: list[set[str]] = []
    for line in lines:
        here: set[str] = set()
        for match in PATH_PATTERN.finditer(line):
            path_part = strip_anchor_suffix(match.group("path"))
            here.add(path_part)
            if path_part not in seen:
                seen.add(path_part)
                ordered_paths.append(path_part)
        refs_by_line.append(here)

    # Pass 2: collect annotations; bind each to a federation ref on the same
    # line or the preceding line by path identity.
    annotations: dict[str, tuple[str, str]] = {}  # ref path -> (repo, path)
    for lineno, line in enumerate(lines):
        for m in ANNOTATION_PATTERN.finditer(line):
            repo, rel = m.group("repo"), m.group("path")
            bad = validate_annotation(repo, rel)
            if bad:
                res.errors.append(
                    f"MALFORMED ANNOTATION (line {lineno + 1}): "
                    f"expected-on-sibling: {repo} {rel} → {bad}"
                )
                continue
            declared = f"{FEDERATION_PREFIX}{repo}/{rel}"
            candidates = set(refs_by_line[lineno])
            if lineno > 0:
                candidates |= refs_by_line[lineno - 1]
            if declared not in candidates:
                res.errors.append(
                    f"ORPHAN ANNOTATION (line {lineno + 1}): "
                    f"expected-on-sibling: {repo} {rel} → declares {declared}, "
                    f"but no such federation ref on this line or the one before"
                )
                continue
            annotations[declared] = (repo, rel)

    # Pass 3: verify.
    for path_part in ordered_paths:
        if path_part.startswith(FEDERATION_PREFIXES):
            res.federation_total += 1
            ann = annotations.get(path_part)
            if ann is None:
                res.info.append(f"FEDERATION (not verified): {path_part}")
                continue
            res.federation_annotated += 1
            repo, rel = ann
            sibling_dir = sibling_root / repo
            if not sibling_dir.is_dir():
                res.federation_unverifiable += 1
                res.info.append(
                    f"FEDERATION (annotated; not verifiable here — "
                    f"sibling {repo} not checked out under {sibling_root}): {path_part}"
                )
                continue
            target = sibling_dir / rel
            if target.exists():
                res.federation_verified += 1
                res.verified.append(f"VERIFIED on sibling {repo}: {path_part}")
            else:
                res.errors.append(
                    f"BROKEN SIBLING REF: {path_part} → no such path at {target}"
                )
            continue

        if not path_part.startswith(REPO_PREFIXES):
            res.warnings.append(f"AMBIGUOUS (not a repo prefix): {path_part}")
            continue

        res.in_repo_checked += 1
        target = repo_root / path_part
        if not target.exists():
            res.errors.append(f"BROKEN REF: {path_part} → no such file on branch")

    return res


def report(res: LintResult) -> int:
    if res.info:
        print(f"[info] {len(res.info)} federation cross-reference(s) not verified:")
        for msg in res.info:
            print(f"  {msg}")
        print()

    if res.verified:
        print(f"[pass] {len(res.verified)} federation cross-reference(s) verified:")
        for msg in res.verified:
            print(f"  {msg}")
        print()

    if res.warnings:
        print(f"[warning] {len(res.warnings)} ambiguous path-like match(es):")
        for msg in res.warnings:
            print(f"  {msg}")
        print()

    summary = (
        f"in-repo: {res.in_repo_checked} checked; "
        f"federation: {res.federation_total} total — "
        f"annotated: {res.federation_annotated}, "
        f"verified: {res.federation_verified}, "
        f"unverifiable: {res.federation_unverifiable}; "
        f"ambiguous: {len(res.warnings)}"
    )

    if res.errors:
        print(f"[error] {len(res.errors)} broken cross-reference(s) / annotation(s):")
        for msg in res.errors:
            print(f"  {msg}")
        print(f"\nFAIL: tenancy doc cross-references ({summary}).")
        return 1

    print(f"OK: tenancy doc cross-references valid ({summary}).")
    return 0


def main(argv: list[str] | None = None) -> int:
    default_root = Path(__file__).resolve().parent.parent
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument(
        "--doc",
        type=Path,
        default=None,
        help="doc to lint (default: <repo-root>/docs/qbp-federation-tenancy.md)",
    )
    ap.add_argument(
        "--repo-root",
        type=Path,
        default=default_root,
        help="repo root for in-repo refs (default: parent of scripts/)",
    )
    ap.add_argument(
        "--sibling-root",
        type=Path,
        default=None,
        help=f"dir holding sibling checkouts (default: ${SIBLING_ROOT_ENV} or ~/Documents)",
    )
    args = ap.parse_args(argv)

    repo_root: Path = args.repo_root.resolve()
    doc_path: Path = args.doc or (repo_root / "docs" / "qbp-federation-tenancy.md")
    sibling_root: Path | None = (
        args.sibling_root.expanduser() if args.sibling_root else None
    )

    res = lint_tenancy_doc(doc_path, repo_root, sibling_root)
    return report(res)


if __name__ == "__main__":
    sys.exit(main())
