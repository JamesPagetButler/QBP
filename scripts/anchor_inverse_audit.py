#!/usr/bin/env python3
"""Inverse anchor audit (#464, Phase A) — the RE-RUNNABLE replacement for the
hand-authored scripts/inventory_verification_report.md.

Walks the Lean corpus and the CTH ledger and answers, per theorem, "is it
anchored, and does its anchor cite a real file?". Surfaces three gap sets:

  (1) Lean-side ORPHANS   — a theorem/lemma no anchor references (by name or file).
  (2) anchor-side PHANTOMS — an anchor cites a `.lean` path that does not exist.
  (3) stale-path DRIFT     — an anchor cites an archive/legacy path (archive/, lean4/)
                             instead of the live `proofs/` tree.

This is the INVERSE of `cth migrate` (which walks anchors forward). Emits a
markdown report + a machine-readable JSON with all three gap sets (discovery).

ENFORCEMENT (--check), post-FAULT-S4-007: only the UNDER-claim direction
(lean_side_orphans + per-file) is ratcheted here. The OVER-claim gaps (phantoms,
stale-path) are RETIRED from enforcement — superseded, strictly better, by the
ABSOLUTE C3-FULL evidence bar + the itemised shrink-only register in
scripts/check_anchor_manifest.py (a scalar "16 phantoms tolerated" green-lights the
debt; PATTERN-02). They remain in the JSON report for discovery only. The orphan
ratchet is itself slated to become an absolute manifest-based under-claim gate (#619).

Usage:
  anchor_inverse_audit.py [--proofs-dir proofs] [--ledger <path>]
                          [--out-md analysis/foundations-inverse-anchor-audit.md]
                          [--out-json analysis/foundations-inverse-anchor-audit.json]
                          [--baseline <path>] [--update-baseline] [--check]
"""

import argparse
import glob
import json
import os
import re
import sys

# Name capture is delimiter-based (stops at whitespace/`:`/`(`/`{`/`[`) rather than an
# ASCII character class, so unicode-named theorems (Lean allows them: `theorem φ_iso …`)
# are NOT missed (Gemini #584 review). Comments/`example`/`def` still excluded: the line
# must start (after optional attr/modifiers) with the `theorem`/`lemma` keyword.
THM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:({\[]+)"
)
LEAN_PATH_RE = re.compile(r"[\w./-]+\.lean")
DEFAULT_LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"


def strip_comments_by_line(raw_lines):
    """Yield (lineno, code) with Lean comments removed, preserving line numbers.

    Handles nested `/- ... -/` block comments and `-- ...` line comments so that
    prose mentioning "theorem `foo`" inside a docstring is NOT mistaken for a
    declaration (Gemini #584 false-positive class). Does not model string literals
    (theorem-declaration lines don't contain comment-like string content in practice).
    """
    depth = 0
    for i, raw in enumerate(raw_lines, 1):
        code = []
        k, n = 0, len(raw)
        while k < n:
            two = raw[k : k + 2]
            if depth > 0:
                if two == "-/":
                    depth -= 1
                    k += 2
                    continue
                if two == "/-":
                    depth += 1
                    k += 2
                    continue
                k += 1
                continue
            if two == "/-":
                depth += 1
                k += 2
                continue
            if two == "--":
                break  # rest of line is a line comment
            code.append(raw[k])
            k += 1
        yield i, "".join(code)


def collect_theorems(proofs_dir):
    """Return list of (name, relpath, lineno) for every theorem/lemma (comment-aware)."""
    out = []
    for path in sorted(
        glob.glob(os.path.join(proofs_dir, "**", "*.lean"), recursive=True)
    ):
        if "/.lake/" in path:
            continue
        with open(path, encoding="utf-8") as f:
            raw_lines = f.readlines()
        for i, code in strip_comments_by_line(raw_lines):
            m = THM_RE.match(code)
            if m:
                out.append((m.group(2), os.path.normpath(path), i))
    return out


def load_anchors(ledger_path):
    """Return the list of anchor dicts regardless of top-level shape."""
    d = json.load(open(ledger_path, encoding="utf-8"))
    if isinstance(d, list):
        return d
    for key in ("anchors", "inventory", "nodes"):
        v = d.get(key)
        if isinstance(v, list):
            return v
        if isinstance(v, dict):
            return list(v.values())
    # dict-of-anchors keyed by id
    vals = [v for v in d.values() if isinstance(v, dict) and "id" in v]
    return vals if vals else []


def anchor_lean_refs(anchors):
    """Collect the theorem-names and .lean file paths anchors reference."""
    ref_names = set()
    ref_files = set()  # normalized as-cited
    file_citations = []  # (anchor_id, cited_path)
    for a in anchors:
        if not isinstance(a, dict):
            continue
        aid = a.get("id", "?")
        # explicit theorem-name lists
        for t in a.get("theorems", []) or []:
            if isinstance(t, str):
                ref_names.add(t.strip())
            elif isinstance(t, dict) and "name" in t:
                ref_names.add(str(t["name"]).strip())
        # proof_file: a path, a citation ("Hurwitz 1898"), or phantom
        pf = a.get("proof_file")
        if isinstance(pf, str) and pf.strip().endswith(".lean"):
            ref_files.add(pf.strip())
            file_citations.append((aid, pf.strip()))
        # .lean paths mentioned in prose fields
        for field in ("notes", "description", "theory_citation"):
            v = a.get(field)
            if isinstance(v, str):
                for p in LEAN_PATH_RE.findall(v):
                    ref_files.add(p)
                    file_citations.append((aid, p))
    return ref_names, ref_files, file_citations


def basename_index(theorems):
    by_name = {}
    by_file = {}
    for name, path, line in theorems:
        by_name.setdefault(name, []).append((path, line))
        by_file.setdefault(path, []).append((name, line))
        by_file.setdefault(os.path.basename(path), []).append((name, line))
    return by_name, by_file


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proofs-dir", default="proofs")
    ap.add_argument("--ledger", default=DEFAULT_LEDGER)
    ap.add_argument("--out-md", default="analysis/foundations-inverse-anchor-audit.md")
    ap.add_argument(
        "--out-json", default="analysis/foundations-inverse-anchor-audit.json"
    )
    ap.add_argument(
        "--baseline", default="analysis/.inverse-anchor-audit-baseline.json"
    )
    ap.add_argument("--update-baseline", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument(
        "--stamp",
        default="(unstamped)",
        help="generation date, passed in (no clock in CI)",
    )
    args = ap.parse_args()

    theorems = collect_theorems(args.proofs_dir)
    anchors = load_anchors(args.ledger)
    ref_names, ref_files, file_citations = anchor_lean_refs(anchors)
    by_name, by_file = basename_index(theorems)

    # existing on-disk lean files (relative + basename)
    on_disk = set()
    for p in glob.glob(os.path.join(args.proofs_dir, "**", "*.lean"), recursive=True):
        if "/.lake/" not in p:
            on_disk.add(os.path.normpath(p))
            on_disk.add(os.path.basename(p))

    # (1) orphans: theorem anchored iff its name is cited OR its file is cited
    cited_files_norm = {os.path.normpath(f) for f in ref_files} | {
        os.path.basename(f) for f in ref_files
    }
    orphans = []
    for name, path, line in theorems:
        anchored = (
            (name in ref_names)
            or (path in cited_files_norm)
            or (os.path.basename(path) in cited_files_norm)
        )
        if not anchored:
            orphans.append((name, path, line))

    # (2) phantoms: cited .lean path that doesn't exist on disk anywhere
    phantoms = []
    for aid, cited in file_citations:
        norm = os.path.normpath(cited)
        if (
            norm not in on_disk
            and os.path.basename(cited) not in on_disk
            and not os.path.exists(cited)
        ):
            phantoms.append((aid, cited))

    # (3) stale-path drift: cites archive/ or lean4/ legacy trees
    stale = [
        (aid, c)
        for aid, c in file_citations
        if re.match(r"(archive/|lean4/|.*qbp-lean/)", c)
    ]

    stats = {
        "theorems_total": len(theorems),
        "anchors_total": len(anchors),
        "anchors_with_theorems_list": sum(
            1 for a in anchors if isinstance(a, dict) and a.get("theorems")
        ),
        "anchors_with_proof_file": sum(
            1
            for a in anchors
            if isinstance(a, dict)
            and isinstance(a.get("proof_file"), str)
            and a["proof_file"].endswith(".lean")
        ),
        "lean_side_orphans": len(orphans),
        "anchor_side_phantoms": len(set(phantoms)),
        "stale_path_citations": len(set(stale)),
    }

    os.makedirs(os.path.dirname(args.out_json), exist_ok=True)
    with open(args.out_json, "w", encoding="utf-8") as f:
        json.dump(
            {
                "stats": stats,
                "orphans": [{"name": n, "file": p, "line": ln} for n, p, ln in orphans],
                "phantoms": [
                    {"anchor": a, "cited": c} for a, c in sorted(set(phantoms))
                ],
                "stale": [{"anchor": a, "cited": c} for a, c in sorted(set(stale))],
            },
            f,
            indent=2,
            sort_keys=True,
        )
        f.write("\n")

    # per-directory orphan breakdown
    bydir = {}
    for n, p, ln in orphans:
        d = (
            "/".join(p.split("/")[:3])
            if p.startswith("proofs/")
            else os.path.dirname(p)
        )
        bydir[d] = bydir.get(d, 0) + 1

    lines = []
    lines.append("# Foundations Inverse Anchor Audit (#464)\n")
    lines.append(
        f"**Generated:** {args.stamp} · **Tool:** `scripts/anchor_inverse_audit.py` (re-runnable; replaces the hand-authored `scripts/inventory_verification_report.md`)"
    )
    lines.append(f"**Inputs:** `{args.proofs_dir}/` Lean corpus · `{args.ledger}`\n")
    lines.append("## 1. Summary\n")
    lines.append("| Metric | Count |")
    lines.append("|---|---|")
    for k, v in stats.items():
        lines.append(f"| {k.replace('_', ' ')} | {v} |")
    lines.append(
        "\n> **Note — `lean_side_orphans` is a LOWER BOUND.** A theorem counts as "
        "*anchored* if any anchor cites its **file** (or its name), so a theorem in a "
        "file some anchor references is counted anchored even if no anchor addresses "
        "*that* theorem. True per-theorem orphans are ≥ this count; the exact figure "
        "lands in Phase B (per-theorem classification, #464). The CI gate closes the "
        "resulting ratchet loophole with a **per-file theorem-count ratchet**: new "
        "theorems added to an already-file-anchored file are caught (they can't hide "
        "behind the coarse global count), forcing a deliberate baseline bump that "
        "confirms the new theorems are anchored."
    )
    lines.append("\n## 2. Lean-side orphans by directory\n")
    lines.append("| Directory | Orphan theorems |")
    lines.append("|---|---|")
    for d, c in sorted(bydir.items(), key=lambda x: -x[1]):
        lines.append(f"| `{d}` | {c} |")
    lines.append("\n## 3. Anchor-side phantoms (cite a non-existent `.lean`)\n")
    if phantoms:
        for a, c in sorted(set(phantoms)):
            lines.append(f"- `{a}` → `{c}`")
    else:
        lines.append("_none_")
    lines.append("\n## 4. Stale-path drift (cite archive/legacy trees)\n")
    if stale:
        for a, c in sorted(set(stale)):
            lines.append(f"- `{a}` → `{c}`")
    else:
        lines.append("_none_")
    lines.append("\n## 5. Full orphan list\n")
    lines.append(
        "See `" + args.out_json + "` for the machine-readable per-theorem list "
        f"({len(orphans)} orphans). Classification (back-fill vs unanchored-by-design) is Phase B (#464)."
    )
    lines.append("")
    with open(args.out_md, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(
        f"theorems={stats['theorems_total']} orphans={stats['lean_side_orphans']} "
        f"phantoms={stats['anchor_side_phantoms']} stale={stats['stale_path_citations']}"
    )
    print(f"wrote {args.out_md} + {args.out_json}")

    # Per-file theorem counts — closes the file-level-anchoring ratchet loophole
    # (Gemini #584): a new theorem added to an already-file-anchored file does NOT
    # raise the global orphan count, so the scalar ratchet alone would miss it. This
    # per-file count catches new theorems in ANY baselined file, forcing a deliberate
    # baseline bump (at which point the reviewer confirms the new theorems are anchored).
    per_file = {}
    for _n, p, _ln in theorems:
        per_file[p] = per_file.get(p, 0) + 1

    # FAULT-S4-007 (PATTERN-02): the OVER-claim ratchets (anchor_side_phantoms,
    # stale_path_citations) are RETIRED here. They are superseded — strictly better —
    # by the ABSOLUTE C3-FULL evidence bar + the itemised, issue-linked, shrink-only
    # register (docs/cth/proof-anchor-remediation.json): 0 tolerated, each item named,
    # no silent baseline-bump. A scalar tolerance ("anchor_side_phantoms: 16") green-lights
    # the debt; that is the bug this whole remediation exists for. phantoms/stale are still
    # COMPUTED and emitted in the JSON report (discovery), just no longer ENFORCED here.
    # Only the UNDER-claim direction is enforced by this ratchet — the evidence bar does not
    # cover proof->anchor. (lean_side_orphans is itself a ratchet, tracked for conversion to
    # an absolute manifest-based under-claim gate — #619.)
    ENFORCED_KEYS = ("lean_side_orphans",)
    enforced_ratchet = {k: stats[k] for k in ENFORCED_KEYS}
    if args.update_baseline:
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump(
                {**enforced_ratchet, "per_file_theorems": per_file},
                f,
                indent=2,
                sort_keys=True,
            )
            f.write("\n")
        print(
            f"baseline updated: {enforced_ratchet} + per_file({len(per_file)} files) "
            f"[over-claim ratchets retired → C3-FULL evidence bar]"
        )
        return 0
    if args.check:
        try:
            base = json.load(open(args.baseline, encoding="utf-8"))
        except FileNotFoundError:
            print(f"::error::baseline {args.baseline} missing — run --update-baseline")
            return 1
        bad = False
        for k, v in enforced_ratchet.items():
            if v > base.get(k, 0):
                print(
                    f"::error::inverse-audit ratchet violated — {k}: {v} > baseline {base.get(k, 0)}"
                )
                bad = True
        base_pf = base.get("per_file_theorems", {})
        for f_path, cnt in sorted(per_file.items()):
            if cnt > base_pf.get(f_path, 0):
                print(
                    f"::error::per-file ratchet violated — {f_path}: {cnt} theorems > "
                    f"baseline {base_pf.get(f_path, 0)}. New theorems must ship with a CTH "
                    f"anchor; then run --update-baseline to record the anchored growth."
                )
                bad = True
        return 1 if bad else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
