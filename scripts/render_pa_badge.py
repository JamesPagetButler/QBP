#!/usr/bin/env python3
"""QBP#692 AC5 — render the PA badge of a CTH anchor from the ledger's stored grades.

    PA <pa_local>/<pa_effective> [<assistant names from proof_assistants, or —>]

The badge READS `pa_local` / `pa_effective` / `proof_assistants` as written by
scripts/encode_pa_from_evidence.py; it computes nothing and never substitutes a count of
assistants (or the engine's clean_count) for a grade — the golden test in
scripts/test_pa_encoder.py pins that. An anchor with no stored grade renders `—`.

Usage:
  python3 scripts/render_pa_badge.py --anchor PROOF-hessian        # one line
  python3 scripts/render_pa_badge.py --all                         # markdown table
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DASH = "—"


def _grade(v: Any) -> str:
    return str(v) if isinstance(v, int) and not isinstance(v, bool) else DASH


def assistant_names(anchor: Dict[str, Any]) -> List[str]:
    arr = anchor.get("proof_assistants")
    if not isinstance(arr, list):
        return []
    return [
        str(a.get("assistant", "?"))
        for a in arr
        if isinstance(a, dict) and a.get("assistant")
    ]


def render_badge(anchor: Dict[str, Any]) -> str:
    """`PA <local>/<effective> [names]` — grades are read, never derived from counts."""
    names = assistant_names(anchor)
    return (
        f"PA {_grade(anchor.get('pa_local'))}/{_grade(anchor.get('pa_effective'))} "
        f"[{', '.join(names) if names else DASH}]"
    )


def render_table(anchors: List[Dict[str, Any]]) -> str:
    rows = ["| anchor | kind | badge |", "|---|---|---|"]
    for a in anchors:
        rows.append(
            f"| {a['id']} | {a.get('provenance_kind', DASH)} | {render_badge(a)} |"
        )
    return "\n".join(rows) + "\n"


def load_anchors(ledger_path: Path) -> List[Dict[str, Any]]:
    return json.loads(ledger_path.read_text(encoding="utf-8"))["anchors"]


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--anchor", help="anchor id to render")
    g.add_argument(
        "--all",
        action="store_true",
        help="markdown table of every anchor that carries a stored PA grade",
    )
    ap.add_argument("--ledger", type=Path, default=LEDGER)
    return ap


def main(argv: Optional[List[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    anchors = load_anchors(args.ledger)
    if args.anchor:
        hit = [a for a in anchors if a.get("id") == args.anchor]
        if not hit:
            print(f"no anchor {args.anchor!r} in {args.ledger}", file=sys.stderr)
            return 2
        print(render_badge(hit[0]))
        return 0
    graded = [a for a in anchors if "pa_local" in a or "pa_effective" in a]
    sys.stdout.write(render_table(graded))
    return 0


if __name__ == "__main__":
    sys.exit(main())
