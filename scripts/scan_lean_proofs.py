#!/usr/bin/env python3
"""
Lean 4 Proof Scanner for QBP Knowledge Graph.

Scans .lean files under proofs/QBP/ to:
1. Extract theorem/def/lemma declarations and detect sorry usage
2. Create/update Proof vertices in the knowledge graph
3. Validate proof_link hyperedges reference valid theorems

Usage:
    python scripts/scan_lean_proofs.py scan              # Show discovered proofs
    python scripts/scan_lean_proofs.py scan --apply       # Write to knowledge graph
    python scripts/scan_lean_proofs.py validate           # Validate proof_link edges
    python scripts/scan_lean_proofs.py validate --apply   # Also scan before validating
"""

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

# Add scripts directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from qbp_knowledge_sqlite import QBPKnowledgeSQLite


@dataclass
class LeanDeclaration:
    """A theorem, def, or lemma found in a Lean file."""

    kind: str  # "theorem", "def", "lemma", "noncomputable def"
    name: str
    file: str  # relative path from project root
    line: int
    has_sorry: bool = False
    namespace: str = ""
    docstring: str = ""


@dataclass
class LeanFile:
    """Summary of a single Lean file."""

    path: str  # relative path from project root
    declarations: List[LeanDeclaration] = field(default_factory=list)
    has_sorry: bool = False
    namespace: str = ""


def scan_lean_file(file_path: Path, root: Path) -> LeanFile:
    """
    Parse a .lean file for theorem/def/lemma declarations.

    Uses regex-based scanning (not a full Lean parser).
    """
    rel_path = str(file_path.relative_to(root))
    result = LeanFile(path=rel_path)

    content = file_path.read_text()
    lines = content.split("\n")

    # Track namespace
    namespace = ""
    for line in lines:
        ns_match = re.match(r"^namespace\s+(\S+)", line)
        if ns_match:
            namespace = ns_match.group(1)
            result.namespace = namespace

    # Check for sorry in file
    result.has_sorry = "sorry" in content

    # Pattern for declarations
    decl_pattern = re.compile(
        r"^(noncomputable\s+)?(theorem|def|lemma)\s+(\w+)", re.MULTILINE
    )

    # Track docstrings (Lean 4 uses /-- ... -/ format)
    docstring_pattern = re.compile(r"/\-\-(.*?)\-/", re.DOTALL)
    docstrings = {}
    for m in docstring_pattern.finditer(content):
        # Find the next declaration after this docstring
        after_pos = m.end()
        rest = content[after_pos:].lstrip()
        decl_match = re.match(r"(noncomputable\s+)?(theorem|def|lemma)\s+(\w+)", rest)
        if decl_match:
            name = decl_match.group(3)
            docstrings[name] = m.group(1).strip()

    for m in decl_pattern.finditer(content):
        noncomputable = m.group(1) is not None
        kind = m.group(2)
        name = m.group(3)
        line_num = content[: m.start()].count("\n") + 1

        if noncomputable:
            kind = f"noncomputable {kind}"

        # Check if this specific declaration uses sorry
        # Look from this declaration to the next one (or end of file)
        decl_start = m.start()
        next_decl = decl_pattern.search(content, m.end())
        decl_end = next_decl.start() if next_decl else len(content)
        decl_body = content[decl_start:decl_end]
        has_sorry = "sorry" in decl_body

        decl = LeanDeclaration(
            kind=kind,
            name=name,
            file=rel_path,
            line=line_num,
            has_sorry=has_sorry,
            namespace=namespace,
            docstring=docstrings.get(name, ""),
        )
        result.declarations.append(decl)

    return result


def scan_all_proofs(root: Path) -> List[LeanFile]:
    """Scan all .lean files under proofs/QBP/."""
    proofs_dir = root / "proofs" / "QBP"
    if not proofs_dir.exists():
        print(f"Warning: {proofs_dir} does not exist")
        return []

    results = []
    for lean_file in sorted(proofs_dir.rglob("*.lean")):
        result = scan_lean_file(lean_file, root)
        results.append(result)

    return results


def sync_to_knowledge_graph(
    scan_results: List[LeanFile], kb: QBPKnowledgeSQLite, dry_run: bool = True
) -> Dict[str, Any]:
    """
    Create/update Proof vertices in the knowledge graph.

    Args:
        scan_results: Output from scan_all_proofs
        kb: Knowledge base instance
        dry_run: If True, only report what would change

    Returns:
        Summary of actions taken/planned
    """
    actions: Dict[str, List[str]] = {"created": [], "updated": [], "skipped": []}

    for lean_file in scan_results:
        proof_id = "proof:" + lean_file.path.replace("/", "-").replace(".lean", "")

        theorems = [
            d.name for d in lean_file.declarations if d.kind in ("theorem", "lemma")
        ]

        attrs = {
            "lean_file": lean_file.path,
            "theorems": theorems,
            "verified": not lean_file.has_sorry,
            "no_sorry": not lean_file.has_sorry,
            "namespace": lean_file.namespace,
            "declaration_count": len(lean_file.declarations),
        }

        existing = kb.get_vertex(proof_id)

        if existing:
            if dry_run:
                actions["updated"].append(proof_id)
            else:
                kb.add_vertex(proof_id, "Proof", attrs, skip_if_exists=False)
                actions["updated"].append(proof_id)
        else:
            if dry_run:
                actions["created"].append(proof_id)
            else:
                kb.add_proof(
                    proof_id,
                    lean_file.path,
                    **{k: v for k, v in attrs.items() if k != "lean_file"},
                )
                actions["created"].append(proof_id)

        actions["skipped"] = []  # Nothing skipped in current logic

    return actions


def validate_proof_links(
    scan_results: List[LeanFile], kb: QBPKnowledgeSQLite
) -> Dict[str, Any]:
    """
    Validate proof_link hyperedges against scanned Lean files.

    Checks:
    1. Referenced proof vertex exists
    2. Referenced theorem name exists in the .lean file
    3. Referenced .lean file exists on disk
    """
    root = Path(__file__).parent.parent
    errors: List[str] = []
    warnings: List[str] = []
    checked = 0

    # Build lookup: theorem name -> LeanFile
    theorem_lookup: Dict[str, LeanFile] = {}
    file_lookup: Dict[str, LeanFile] = {}
    for lf in scan_results:
        file_lookup[lf.path] = lf
        for decl in lf.declarations:
            theorem_lookup[decl.name] = lf

    # Get all proof_link hyperedges
    proof_links = kb.get_hyperedges_by_type("proof_link")

    for pl in proof_links:
        checked += 1
        edge_id = pl.get("id", "unknown")
        theorem_name = pl.get("theorem", "")
        members = pl.get("members", [])

        # Check proof vertex exists
        proof_members = [m for m in members if m.startswith("proof:")]
        for pm in proof_members:
            vertex = kb.get_vertex(pm)
            if not vertex:
                errors.append(f"{edge_id}: proof vertex '{pm}' does not exist")
                continue

            lean_file = vertex.get("lean_file", "")
            if lean_file and not (root / lean_file).exists():
                errors.append(
                    f"{edge_id}: lean file '{lean_file}' does not exist on disk"
                )

        # Check theorem name exists in scan results
        if theorem_name and theorem_name not in theorem_lookup:
            warnings.append(
                f"{edge_id}: theorem '{theorem_name}' not found in scanned files"
            )
        elif theorem_name:
            lf = theorem_lookup[theorem_name]
            decl = next(d for d in lf.declarations if d.name == theorem_name)
            if decl.has_sorry:
                warnings.append(
                    f"{edge_id}: theorem '{theorem_name}' contains sorry "
                    f"(incomplete proof) in {lf.path}"
                )

    return {
        "valid": len(errors) == 0,
        "checked": checked,
        "errors": errors,
        "warnings": warnings,
    }


def main():
    import argparse

    root = Path(__file__).parent.parent

    parser = argparse.ArgumentParser(description="QBP Lean Proof Scanner")
    parser.add_argument("--db", default="knowledge/qbp.db", help="Database path")

    subparsers = parser.add_subparsers(dest="command")

    # Scan
    scan_p = subparsers.add_parser("scan", help="Scan Lean files for declarations")
    scan_p.add_argument(
        "--apply", action="store_true", help="Write results to knowledge graph"
    )
    scan_p.add_argument("--json", action="store_true", help="Output as JSON")

    # Validate
    validate_p = subparsers.add_parser(
        "validate", help="Validate proof_link hyperedges"
    )
    validate_p.add_argument(
        "--apply",
        action="store_true",
        help="Also sync scan results before validating",
    )

    args = parser.parse_args()

    if args.command == "scan":
        results = scan_all_proofs(root)

        if args.json:
            output = []
            for lf in results:
                output.append(
                    {
                        "file": lf.path,
                        "namespace": lf.namespace,
                        "has_sorry": lf.has_sorry,
                        "declarations": [
                            {
                                "kind": d.kind,
                                "name": d.name,
                                "line": d.line,
                                "has_sorry": d.has_sorry,
                            }
                            for d in lf.declarations
                        ],
                    }
                )
            print(json.dumps(output, indent=2))
        else:
            total_decls = 0
            total_sorry = 0
            for lf in results:
                print(f"\n{lf.path} (namespace: {lf.namespace})")
                print(f"  Sorry in file: {'YES' if lf.has_sorry else 'No'}")
                for d in lf.declarations:
                    sorry_marker = " [SORRY]" if d.has_sorry else ""
                    print(f"  L{d.line:3d} {d.kind} {d.name}{sorry_marker}")
                    total_decls += 1
                    if d.has_sorry:
                        total_sorry += 1

            print(f"\nTotal: {len(results)} files, {total_decls} declarations")
            if total_sorry:
                print(f"WARNING: {total_sorry} declarations contain sorry")
            else:
                print("All proofs complete (no sorry)")

        if args.apply:
            kb = QBPKnowledgeSQLite(args.db)
            actions = sync_to_knowledge_graph(results, kb, dry_run=False)
            print(f"\nKnowledge graph updated:")
            print(f"  Created: {len(actions['created'])} vertices")
            print(f"  Updated: {len(actions['updated'])} vertices")
        elif not args.json:
            # Show what would happen
            kb = QBPKnowledgeSQLite(args.db, read_only=True)
            actions = sync_to_knowledge_graph(results, kb, dry_run=True)
            if actions["created"] or actions["updated"]:
                print(f"\nDry run (use --apply to write):")
                for v in actions["created"]:
                    print(f"  Would create: {v}")
                for v in actions["updated"]:
                    print(f"  Would update: {v}")

    elif args.command == "validate":
        results = scan_all_proofs(root)

        if args.apply:
            kb = QBPKnowledgeSQLite(args.db)
            sync_to_knowledge_graph(results, kb, dry_run=False)
            print("Synced scan results to knowledge graph")
        else:
            kb = QBPKnowledgeSQLite(args.db, read_only=True)

        validation = validate_proof_links(results, kb)
        print(f"\nProof Link Validation")
        print(f"{'=' * 40}")
        print(f"Links checked: {validation['checked']}")
        print(f"Status: {'VALID' if validation['valid'] else 'INVALID'}")

        if validation["errors"]:
            print(f"\nERRORS ({len(validation['errors'])}):")
            for e in validation["errors"]:
                print(f"  x {e}")

        if validation["warnings"]:
            print(f"\nWARNINGS ({len(validation['warnings'])}):")
            for w in validation["warnings"]:
                print(f"  ! {w}")

        if validation["valid"] and not validation["warnings"]:
            print("\nAll proof_link hyperedges validated successfully")

        if not validation["valid"]:
            sys.exit(1)

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
