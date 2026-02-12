#!/usr/bin/env python3
"""
Migration script: YAML knowledge entries → Hypergraph-DB

Migrates legacy YAML files from knowledge/ subdirectories to the
Hypergraph-DB format, inferring hyperedges from relationships.

Usage:
    python scripts/migrate_yaml_to_hypergraph.py
    python scripts/migrate_yaml_to_hypergraph.py --dry-run
    python scripts/migrate_yaml_to_hypergraph.py --include-proofs
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional

import yaml

# Add scripts to path for import
sys.path.insert(0, str(Path(__file__).parent))
from qbp_knowledge import QBPKnowledge


def load_yaml_file(path: Path) -> Optional[Dict[str, Any]]:
    """Load a YAML file, returning None on error."""
    try:
        with open(path, "r") as f:
            data = yaml.safe_load(f)
        # Convert any date objects to strings (for JSON serialization)
        return _convert_dates(data) if data else None
    except Exception as e:
        print(f"  Warning: Failed to load {path}: {e}")
        return None


def _convert_dates(obj):
    """Recursively convert date objects to strings."""
    from datetime import date, datetime

    if isinstance(obj, (date, datetime)):
        return str(obj)
    elif isinstance(obj, dict):
        return {k: _convert_dates(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [_convert_dates(item) for item in obj]
    return obj


def migrate_source(
    kb: QBPKnowledge, data: Dict[str, Any], dry_run: bool = False
) -> str:
    """Migrate a Source entry."""
    source_id = data.get("id", "").replace("source-", "")
    if not source_id:
        return None

    metadata = data.get("metadata", {})
    title = metadata.get("title", data.get("title", "Unknown"))

    attrs = {
        "category": data.get("category", "paper"),
        "tags": data.get("tags", []),
        "added_date": data.get("added_date"),
        "added_by": data.get("added_by"),
        "research_sprint": data.get("research_sprint"),
    }

    # Add metadata fields
    if "authors" in metadata:
        attrs["authors"] = [
            a.get("name", a) if isinstance(a, dict) else a for a in metadata["authors"]
        ]
    if "date" in metadata:
        attrs["date"] = str(metadata["date"])
    if "url" in metadata:
        attrs["url"] = metadata["url"]
    if "doi" in metadata:
        attrs["doi"] = metadata["doi"]
    if "venue" in metadata:
        attrs["venue"] = metadata["venue"]

    # Add optional fields
    if "abstract" in data:
        attrs["abstract"] = data["abstract"]
    if "key_insights" in data:
        attrs["key_insights"] = data["key_insights"]
    if "qbp_relevance" in data:
        attrs["qbp_relevance"] = data["qbp_relevance"]

    # Filter None values
    attrs = {k: v for k, v in attrs.items() if v is not None}

    if dry_run:
        print(f"  Would add source: {source_id} - {title[:50]}")
        return f"source:{source_id}"

    return kb.add_source(source_id, title, **attrs)


def migrate_concept(
    kb: QBPKnowledge, data: Dict[str, Any], dry_run: bool = False
) -> str:
    """Migrate a Concept entry."""
    concept_id = data.get("id", "").replace("concept-", "")
    if not concept_id:
        return None

    term = data.get("term", "Unknown")

    attrs = {
        "definition": data.get("definition"),
        "formal_definition": data.get("formal_definition"),
        "aliases": data.get("aliases", []),
        "tags": data.get("tags", []),
        "added_date": data.get("added_date"),
        "added_by": data.get("added_by"),
    }

    attrs = {k: v for k, v in attrs.items() if v is not None}

    if dry_run:
        print(f"  Would add concept: {concept_id} - {term[:50]}")
        return f"concept:{concept_id}"

    return kb.add_concept(concept_id, term, **attrs)


def migrate_claim(kb: QBPKnowledge, data: Dict[str, Any], dry_run: bool = False) -> str:
    """Migrate a Claim entry."""
    claim_id = data.get("id", "").replace("claim-", "")
    if not claim_id:
        return None

    statement = data.get("statement", "Unknown")

    attrs = {
        "context": data.get("context"),
        "status": data.get("status", "proposed"),
        "tags": data.get("tags", []),
        "implications": data.get("implications", []),
        "added_date": data.get("added_date"),
        "added_by": data.get("added_by"),
    }

    attrs = {k: v for k, v in attrs.items() if v is not None}

    if dry_run:
        print(f"  Would add claim: {claim_id} - {statement[:50]}")
        return f"claim:{claim_id}"

    return kb.add_claim(claim_id, statement, **attrs)


def migrate_question(
    kb: QBPKnowledge, data: Dict[str, Any], dry_run: bool = False
) -> str:
    """Migrate a Question entry."""
    question_id = data.get("id", "").replace("question-", "")
    if not question_id:
        return None

    question = data.get("question", "Unknown")

    attrs = {
        "context": data.get("context"),
        "status": data.get("status", "open"),
        "priority": data.get("priority", "medium"),
        "tags": data.get("tags", []),
        "related_issues": data.get("related_issues", []),
        "investigation_approaches": data.get("investigation_approaches", []),
        "success_criteria": data.get("success_criteria", []),
        "added_date": data.get("added_date"),
        "added_by": data.get("added_by"),
        "research_sprint": data.get("research_sprint"),
    }

    attrs = {k: v for k, v in attrs.items() if v is not None}

    if dry_run:
        print(f"  Would add question: {question_id} - {question[:50]}")
        return f"question:{question_id}"

    return kb.add_question(question_id, question, **attrs)


def infer_hyperedges_from_question(
    kb: QBPKnowledge, data: Dict[str, Any], question_id: str, dry_run: bool = False
):
    """Infer investigation hyperedge from question background."""
    background = data.get("background", [])
    if len(background) < 2:
        return

    # Collect source references
    source_ids = []
    for bg in background:
        source = bg.get("source", "")
        if source:
            # Normalize ID
            if not source.startswith("source:"):
                source = f"source:{source}"
            source_ids.append(source)

    if len(source_ids) >= 1:
        members = [question_id] + source_ids
        if dry_run:
            print(
                f"  Would add investigation hyperedge: {question_id} + {len(source_ids)} sources"
            )
        else:
            try:
                kb.add_hyperedge(
                    tuple(members),
                    "investigation",
                    {"inferred_from": "yaml_background"},
                )
            except Exception as e:
                print(f"  Warning: Could not create investigation hyperedge: {e}")


def infer_hyperedges_from_claim(
    kb: QBPKnowledge, data: Dict[str, Any], claim_id: str, dry_run: bool = False
):
    """Infer evidence_chain from claim evidence array."""
    evidence = data.get("evidence", [])
    if len(evidence) < 2:
        return

    source_ids = []
    max_strength = 1  # Track highest confidence

    for ev in evidence:
        source = ev.get("source", "")
        strength = ev.get("strength", "supporting")

        if source:
            if not source.startswith(("source:", "proof:")):
                source = f"source:{source}"
            source_ids.append(source)

        if strength == "strong":
            max_strength = 3
        elif strength == "supporting" and max_strength < 2:
            max_strength = 2

    if len(source_ids) >= 2:
        members = [claim_id] + source_ids
        if dry_run:
            print(
                f"  Would add evidence_chain: {claim_id} + {len(source_ids)} sources (tier {max_strength})"
            )
        else:
            try:
                kb.add_evidence_chain(
                    claim_id,
                    source_ids,
                    confidence_tier=max_strength,
                    inferred_from="yaml_evidence",
                )
            except Exception as e:
                print(f"  Warning: Could not create evidence_chain: {e}")


def scan_lean_proofs(proofs_dir: Path) -> List[Dict[str, Any]]:
    """Scan Lean proof files for theorem definitions."""
    proofs = []

    # QBP-specific proof files
    qbp_proofs = [
        proofs_dir / "QBP" / "Basic.lean",
        proofs_dir / "QBP" / "Experiments" / "SternGerlach.lean",
        proofs_dir / "QBP" / "Experiments" / "AngleDependent.lean",
    ]

    theorem_pattern = re.compile(r"^theorem\s+(\w+)", re.MULTILINE)

    for lean_file in qbp_proofs:
        if not lean_file.exists():
            continue

        relative_path = str(lean_file.relative_to(proofs_dir.parent))
        content = lean_file.read_text()

        theorems = theorem_pattern.findall(content)
        has_sorry = "sorry" in content

        proofs.append(
            {
                "file": relative_path,
                "theorems": theorems,
                "verified": not has_sorry,
                "no_sorry": not has_sorry,
            }
        )

    return proofs


def add_lean_proofs(kb: QBPKnowledge, proofs_dir: Path, dry_run: bool = False):
    """Add Proof vertices for Lean files."""
    proofs = scan_lean_proofs(proofs_dir)

    for proof in proofs:
        proof_id = Path(proof["file"]).stem.lower()

        if dry_run:
            print(f"  Would add proof: {proof_id} ({len(proof['theorems'])} theorems)")
        else:
            try:
                kb.add_proof(
                    proof_id,
                    proof["file"],
                    theorems=proof["theorems"],
                    verified=proof["verified"],
                    no_sorry=proof["no_sorry"],
                )
            except Exception as e:
                print(f"  Warning: Could not add proof {proof_id}: {e}")


def main():
    parser = argparse.ArgumentParser(description="Migrate YAML to Hypergraph-DB")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be done without making changes",
    )
    parser.add_argument(
        "--include-proofs",
        action="store_true",
        help="Also scan and add Lean proof files",
    )
    parser.add_argument(
        "--knowledge-dir",
        type=str,
        default="knowledge",
        help="Path to knowledge directory",
    )
    parser.add_argument(
        "--proofs-dir", type=str, default="proofs", help="Path to proofs directory"
    )
    parser.add_argument(
        "--output", type=str, default="knowledge/qbp.hgdb", help="Output database path"
    )

    args = parser.parse_args()

    knowledge_dir = Path(args.knowledge_dir)
    proofs_dir = Path(args.proofs_dir)

    print(f"Migration: YAML → Hypergraph-DB")
    print(f"  Knowledge dir: {knowledge_dir}")
    print(f"  Output: {args.output}")
    print(f"  Dry run: {args.dry_run}")
    print()

    # Load existing or create new
    if args.dry_run:
        kb = QBPKnowledge()
    else:
        kb = QBPKnowledge(args.output)

    migrated = {"sources": 0, "concepts": 0, "claims": 0, "questions": 0, "proofs": 0}
    hyperedges_created = 0

    # Migrate sources
    print("Migrating sources...")
    sources_dir = knowledge_dir / "sources"
    if sources_dir.exists():
        for yaml_file in sources_dir.glob("*.yaml"):
            data = load_yaml_file(yaml_file)
            if data and data.get("type") == "Source":
                result = migrate_source(kb, data, args.dry_run)
                if result:
                    migrated["sources"] += 1

    # Migrate concepts
    print("Migrating concepts...")
    concepts_dir = knowledge_dir / "concepts"
    if concepts_dir.exists():
        for yaml_file in concepts_dir.glob("*.yaml"):
            data = load_yaml_file(yaml_file)
            if data and data.get("type") == "Concept":
                result = migrate_concept(kb, data, args.dry_run)
                if result:
                    migrated["concepts"] += 1

    # Migrate claims
    print("Migrating claims...")
    claims_dir = knowledge_dir / "claims"
    if claims_dir.exists():
        for yaml_file in claims_dir.glob("*.yaml"):
            data = load_yaml_file(yaml_file)
            if data and data.get("type") == "Claim":
                result = migrate_claim(kb, data, args.dry_run)
                if result:
                    migrated["claims"] += 1
                    # Infer evidence chain
                    infer_hyperedges_from_claim(kb, data, result, args.dry_run)

    # Migrate questions
    print("Migrating questions...")
    questions_dir = knowledge_dir / "questions"
    if questions_dir.exists():
        for yaml_file in questions_dir.glob("*.yaml"):
            data = load_yaml_file(yaml_file)
            if data and data.get("type") == "Question":
                result = migrate_question(kb, data, args.dry_run)
                if result:
                    migrated["questions"] += 1
                    # Infer investigation hyperedge
                    infer_hyperedges_from_question(kb, data, result, args.dry_run)

    # Add Lean proofs
    if args.include_proofs:
        print("Scanning Lean proofs...")
        add_lean_proofs(kb, proofs_dir, args.dry_run)
        proofs = scan_lean_proofs(proofs_dir)
        migrated["proofs"] = len(proofs)

    # Save
    if not args.dry_run:
        kb.save()
        print()
        print(kb.summary())

    print()
    print("Migration Summary:")
    print(f"  Sources: {migrated['sources']}")
    print(f"  Concepts: {migrated['concepts']}")
    print(f"  Claims: {migrated['claims']}")
    print(f"  Questions: {migrated['questions']}")
    print(f"  Proofs: {migrated['proofs']}")

    if args.dry_run:
        print()
        print("(Dry run - no changes made)")


if __name__ == "__main__":
    main()
