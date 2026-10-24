#!/usr/bin/env python3
"""Prediction-Classification gate for the ground-truth docs (QBP #736, re-filed from #170 AC4).

Every `research/*_expected_results.md` must carry a `## Prediction Classification`
section (docs/schemas/ground_truth_schema.md §6, REQUIRED) whose first table has a
`Type` column with every cell in exactly {Validation, Novel, OPEN}:

- Validation — the doc states that QBP reproduces the standard QM/QED/GR value.
- Novel      — the doc states a QBP-specific deviation with a number.
- OPEN       — neither statement is in the doc; the Notes cell says what is missing.

The gate is structural only: it checks that the section exists and that the Type
column is well-formed. It does NOT (and must not) judge whether a classification
is correct — that is a research claim reviewed on the PR, not a lint.

Rules
  1. A level-2 heading `## Prediction Classification` (an optional `N.` section
     number is allowed: `## 5. Prediction Classification`). Level 3+ does not count.
  2. The section (heading → next level-2 heading / EOF) contains a Markdown table
     whose header row has a cell reading exactly `Type`.
  3. The table has at least one data row, and every Type cell is exactly one of
     `Validation`, `Novel`, `OPEN` (case-sensitive, no markup, no suffix).
  4. Fenced code blocks are ignored, so a pasted template inside ``` does not pass.

Usage
  python3 scripts/check_prediction_classification.py            # gate: exit 1 on any FAIL
  python3 scripts/check_prediction_classification.py --list     # per-file status table
  python3 scripts/check_prediction_classification.py --research-dir <dir>
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from typing import List, Optional, Sequence, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(HERE)
DEFAULT_RESEARCH_DIR = os.path.join(REPO_ROOT, "research")

DOC_GLOB_SUFFIX = "_expected_results.md"
ALLOWED_TYPES = ("Validation", "Novel", "OPEN")

HEADING_RE = re.compile(r"^##\s+(?:\d+\.\s+)?Prediction Classification\s*$")
LEVEL2_RE = re.compile(r"^##\s+\S")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
SEPARATOR_CELL_RE = re.compile(r"^:?-{3,}:?$")


def strip_fences(lines: Sequence[str]) -> List[str]:
    """Blank out lines inside ``` / ~~~ fences (keeps line numbers stable)."""
    out: List[str] = []
    in_fence = False
    for line in lines:
        if FENCE_RE.match(line):
            in_fence = not in_fence
            out.append("")
            continue
        out.append("" if in_fence else line)
    return out


UNESCAPED_PIPE_RE = re.compile(r"(?<!\\)\|")


def split_cells(row: str) -> List[str]:
    """`| a | b |` → ['a', 'b'] (outer pipes optional; GFM `\|` is a literal pipe)."""
    s = row.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith("\\|"):
        s = s[:-1]
    return [c.strip().replace("\\|", "|") for c in UNESCAPED_PIPE_RE.split(s)]


def find_section(lines: Sequence[str]) -> Optional[Tuple[int, int]]:
    """(start, end) line-index range of the Prediction Classification section, or None."""
    start = None
    for i, line in enumerate(lines):
        if HEADING_RE.match(line):
            start = i
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if LEVEL2_RE.match(lines[j]):
            end = j
            break
    return start, end


def find_table(lines: Sequence[str]) -> Optional[Tuple[List[str], List[List[str]]]]:
    """First Markdown table in `lines` → (header cells, data rows); None if absent."""
    i = 0
    n = len(lines)
    while i < n - 1:
        if lines[i].lstrip().startswith("|") and lines[i + 1].lstrip().startswith("|"):
            sep = split_cells(lines[i + 1])
            if sep and all(SEPARATOR_CELL_RE.match(c) for c in sep):
                header = split_cells(lines[i])
                rows: List[List[str]] = []
                k = i + 2
                while k < n and lines[k].lstrip().startswith("|"):
                    rows.append(split_cells(lines[k]))
                    k += 1
                return header, rows
        i += 1
    return None


def check_text(text: str) -> List[str]:
    """Return the list of problems (empty = PASS) for one doc's text."""
    lines = strip_fences(text.splitlines())
    section = find_section(lines)
    if section is None:
        return ["missing `## Prediction Classification` heading (level 2)"]
    start, end = section
    table = find_table(lines[start + 1 : end])
    if table is None:
        return ["section has no Markdown table"]
    header, rows = table
    if "Type" not in header:
        return [f"table header has no `Type` column (header: {header})"]
    col = header.index("Type")
    if not rows:
        return ["table has no data rows"]
    problems: List[str] = []
    for r_idx, row in enumerate(rows, start=1):
        if col >= len(row):
            problems.append(f"row {r_idx}: no Type cell")
            continue
        cell = row[col]
        if cell not in ALLOWED_TYPES:
            problems.append(
                f"row {r_idx}: Type cell {cell!r} not in {'/'.join(ALLOWED_TYPES)}"
            )
    return problems


def find_docs(research_dir: str) -> List[str]:
    if not os.path.isdir(research_dir):
        return []
    return sorted(
        os.path.join(research_dir, f)
        for f in os.listdir(research_dir)
        if f.endswith(DOC_GLOB_SUFFIX)
    )


def check_docs(research_dir: str) -> List[Tuple[str, List[str]]]:
    results: List[Tuple[str, List[str]]] = []
    for path in find_docs(research_dir):
        with open(path, encoding="utf-8") as fh:
            results.append((path, check_text(fh.read())))
    return results


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--research-dir",
        default=DEFAULT_RESEARCH_DIR,
        help="directory holding *_expected_results.md (default: <repo>/research)",
    )
    ap.add_argument(
        "--list", action="store_true", help="print per-file status for every doc"
    )
    args = ap.parse_args(argv)

    results = check_docs(args.research_dir)
    if not results:
        print(
            f"check_prediction_classification: no *{DOC_GLOB_SUFFIX} under "
            f"{args.research_dir}",
            file=sys.stderr,
        )
        return 1

    n_fail = 0
    for path, problems in results:
        rel = os.path.relpath(path, REPO_ROOT)
        if problems:
            n_fail += 1
            print(f"FAIL  {rel}")
            for p in problems:
                print(f"      - {p}")
        elif args.list:
            print(f"OK    {rel}")

    total = len(results)
    print(
        f"check_prediction_classification: {total - n_fail}/{total} docs carry a "
        f"well-formed `## Prediction Classification` section"
    )
    return 1 if n_fail else 0


if __name__ == "__main__":
    sys.exit(main())
