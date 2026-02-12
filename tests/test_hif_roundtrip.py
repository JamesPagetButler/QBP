"""Tests for HIF round-trip import/export and HyperNetX conversion."""

import json
import os
import sys
import tempfile

import pytest

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

from qbp_knowledge_sqlite import QBPKnowledgeSQLite


@pytest.fixture
def kb(tmp_path):
    """Create a temporary knowledge base with test data."""
    db_path = str(tmp_path / "test.db")
    kb = QBPKnowledgeSQLite(db_path)

    # Add test vertices
    kb.add_concept("concept:test-a", "Test Concept A", tags=["test"])
    kb.add_concept("concept:test-b", "Test Concept B", tags=["test"])
    kb.add_claim("claim:test-1", "Test claim statement", status="supported")
    kb.add_source("source:test-paper", "Test Paper", category="paper")

    # Add test hyperedges
    kb.add_evidence_chain("claim:test-1", ["source:test-paper"], confidence_tier=2)
    kb.add_equivalence(["concept:test-a", "concept:test-b"], description="Test equiv")

    return kb


def test_hif_roundtrip(kb, tmp_path):
    """Test that export → import preserves all data."""
    hif_path = str(tmp_path / "export.hif.json")

    # Export
    kb.export_hif(hif_path)

    # Verify HIF file structure
    with open(hif_path) as f:
        hif = json.load(f)

    assert "nodes" in hif
    assert "edges" in hif
    assert "incidences" in hif
    assert len(hif["nodes"]) == 4  # 4 vertices
    assert len(hif["edges"]) == 2  # 2 hyperedges

    # Import into fresh database
    db2_path = str(tmp_path / "reimported.db")
    kb2 = QBPKnowledgeSQLite(db2_path)
    counts = kb2.import_hif(hif_path)

    assert counts["nodes"] == 4
    assert counts["edges"] == 2

    # Verify data preserved
    original_summary = kb.summary()
    reimported_summary = kb2.summary()

    assert (
        original_summary["vertices"]["total"] == reimported_summary["vertices"]["total"]
    )
    assert (
        original_summary["hyperedges"]["total"]
        == reimported_summary["hyperedges"]["total"]
    )

    # Verify specific vertex data
    concept_a = kb2.get_vertex("concept:test-a")
    assert concept_a is not None
    assert concept_a["term"] == "Test Concept A"

    claim = kb2.get_vertex("claim:test-1")
    assert claim is not None
    assert claim["statement"] == "Test claim statement"


def test_hif_to_hypernetx(kb):
    """Test conversion to HyperNetX format."""
    try:
        import hypernetx  # noqa: F401
    except ImportError:
        pytest.skip("hypernetx not installed")

    H = kb.to_hypernetx()

    # Check basic structure
    assert len(H.edges) == 2
    assert len(H.nodes) > 0

    # Check that vertices in edges are correct
    edge_members = set()
    for edge in H.edges:
        for node in H.edges[edge]:
            edge_members.add(node)

    assert "concept:test-a" in edge_members
    assert "concept:test-b" in edge_members
    assert "claim:test-1" in edge_members


def test_hif_export_format(kb, tmp_path):
    """Test that exported HIF matches the standard format."""
    hif_path = str(tmp_path / "format_check.hif.json")
    kb.export_hif(hif_path)

    with open(hif_path) as f:
        hif = json.load(f)

    # Check required top-level keys
    assert hif["network-type"] == "undirected"
    assert "metadata" in hif

    # Check node format
    for node in hif["nodes"]:
        assert "node" in node
        assert "attrs" in node

    # Check edge format
    for edge in hif["edges"]:
        assert "edge" in edge
        assert "attrs" in edge

    # Check incidence format
    for inc in hif["incidences"]:
        assert "node" in inc
        assert "edge" in inc


def test_import_hif_cli(kb, tmp_path):
    """Test import-hif CLI subcommand via direct method call."""
    hif_path = str(tmp_path / "cli_test.hif.json")
    kb.export_hif(hif_path)

    # Create fresh db and import
    db2_path = str(tmp_path / "cli_import.db")
    kb2 = QBPKnowledgeSQLite(db2_path)
    counts = kb2.import_hif(hif_path)

    assert counts["nodes"] == 4
    assert counts["edges"] == 2

    # Validate round-tripped data
    result = kb2.validate()
    assert result["valid"], f"Validation errors: {result['errors']}"
