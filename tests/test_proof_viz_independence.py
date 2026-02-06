"""
test_proof_viz_independence.py — Enforce the independence boundary between
formal proofs and simulation code.

The Phase 4c interactive proof visualization must derive ONLY from
Phase 4a proof metadata (Lean files). It must never depend on Phase 2
simulation code (src/qphysics.py, results/, etc.).

These tests enforce this boundary at three levels:
  1. Static dependency analysis (no simulation imports)
  2. JSON schema validation (no simulation data fields)
  3. Sabotage test (output unchanged without simulation code)

Run:
    python3 -m pytest tests/test_proof_viz_independence.py -v
"""

import ast
import json
import subprocess
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
EXPORT_SCRIPT = PROJECT_ROOT / "src" / "viz" / "interactive" / "export_data.py"
PROOF_GRAPH_JSON = (
    PROJECT_ROOT / "src" / "viz" / "interactive" / "data" / "proof_graph_01.json"
)

# Directories that the export script must NOT depend on
FORBIDDEN_DIRS = [
    PROJECT_ROOT / "src" / "qphysics.py",
    PROJECT_ROOT / "src" / "viz" / "theme.py",
    PROJECT_ROOT / "src" / "viz" / "stern_gerlach_demo.py",
    PROJECT_ROOT / "src" / "viz" / "quaternion_rotation.py",
    PROJECT_ROOT / "results",
    PROJECT_ROOT / "analysis",
]

# Modules that must never appear as imports in export_data.py
FORBIDDEN_IMPORTS = {
    "qphysics",
    "numpy",
    "quaternion",
    "pandas",
    "matplotlib",
    "vpython",
    "scipy",
}


# ============================================================================
# Test 1: Static dependency analysis
# ============================================================================


class TestStaticDependencies:
    """Verify export_data.py has no imports from simulation code."""

    def test_export_script_exists(self):
        assert EXPORT_SCRIPT.exists(), f"export_data.py not found at {EXPORT_SCRIPT}"

    def test_no_forbidden_imports(self):
        """Parse the AST of export_data.py and check all imports."""
        source = EXPORT_SCRIPT.read_text()
        tree = ast.parse(source, filename=str(EXPORT_SCRIPT))

        imported_modules = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imported_modules.add(alias.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    imported_modules.add(node.module.split(".")[0])

        violations = imported_modules & FORBIDDEN_IMPORTS
        assert not violations, (
            f"export_data.py imports forbidden simulation modules: {violations}\n"
            f"The proof graph exporter must only use standard library modules "
            f"and must never depend on simulation code."
        )

    def test_only_stdlib_imports(self):
        """Verify all imports are from the Python standard library."""
        source = EXPORT_SCRIPT.read_text()
        tree = ast.parse(source, filename=str(EXPORT_SCRIPT))

        # Standard library modules that export_data.py is allowed to use
        ALLOWED_MODULES = {
            "json",
            "re",
            "sys",
            "pathlib",
            "os",
            "typing",
            "collections",
            "dataclasses",
            "argparse",
            "textwrap",
        }

        imported_modules = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imported_modules.add(alias.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    imported_modules.add(node.module.split(".")[0])

        non_stdlib = imported_modules - ALLOWED_MODULES
        assert not non_stdlib, (
            f"export_data.py imports non-standard-library modules: {non_stdlib}\n"
            f"Allowed: {ALLOWED_MODULES}"
        )

    def test_no_simulation_path_references(self):
        """Check that export_data.py doesn't reference simulation paths."""
        source = EXPORT_SCRIPT.read_text()
        forbidden_patterns = [
            "qphysics.py",
            "results/",
            "analysis/",
            "stern_gerlach_demo",
            "quaternion_rotation",
            ".csv",
        ]
        for pattern in forbidden_patterns:
            assert pattern not in source, (
                f"export_data.py references forbidden path/pattern: '{pattern}'\n"
                f"The exporter must only reference Lean proof files."
            )

    def test_reads_only_lean_files(self):
        """Verify the script only reads from proofs/ directory."""
        source = EXPORT_SCRIPT.read_text()
        tree = ast.parse(source, filename=str(EXPORT_SCRIPT))

        # Find all string constants that look like file paths
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                val = node.value
                # If it looks like a file reference, it should be a .lean file
                if any(ext in val for ext in [".py", ".csv", ".json", ".txt"]):
                    # Allow the output .json file reference and self-references
                    if "proof_graph" in val or "export_data" in val:
                        continue
                    assert ".lean" in val or val.startswith(
                        "data/"
                    ), f"export_data.py references non-Lean file: '{val}'"


# ============================================================================
# Test 2: JSON schema validation
# ============================================================================


class TestJsonSchema:
    """Verify the proof graph JSON contains only formal proof data."""

    @pytest.fixture
    def proof_data(self):
        assert (
            PROOF_GRAPH_JSON.exists()
        ), f"proof_graph_01.json not found. Run export_data.py first."
        with open(PROOF_GRAPH_JSON) as f:
            return json.load(f)

    def test_top_level_fields(self, proof_data):
        """Only allowed top-level fields."""
        allowed = {"experiment", "title", "description", "walk_order", "nodes"}
        actual = set(proof_data.keys())
        extra = actual - allowed
        assert not extra, (
            f"Unexpected top-level fields in proof graph: {extra}\n"
            f"Allowed: {allowed}"
        )

    def test_node_fields(self, proof_data):
        """Each node must have only allowed fields."""
        allowed = {
            "id",
            "name",
            "kind",
            "statement",
            "physical_meaning",
            "dependencies",
            "source_file",
        }
        for node in proof_data["nodes"]:
            actual = set(node.keys())
            extra = actual - allowed
            assert not extra, (
                f"Node '{node.get('name', '?')}' has unexpected fields: {extra}\n"
                f"Allowed: {allowed}"
            )

    def test_no_floating_point_values(self, proof_data):
        """Proof graph should not contain float values (simulation artifacts)."""

        def check_no_floats(obj, path=""):
            if isinstance(obj, float):
                pytest.fail(
                    f"Float value {obj} found at {path} — "
                    f"proof graph should contain only strings, lists, and ints."
                )
            elif isinstance(obj, dict):
                for k, v in obj.items():
                    check_no_floats(v, f"{path}.{k}")
            elif isinstance(obj, list):
                for i, v in enumerate(obj):
                    check_no_floats(v, f"{path}[{i}]")

        check_no_floats(proof_data)

    def test_no_simulation_keywords_in_values(self, proof_data):
        """Values should not contain simulation-specific keywords."""
        simulation_keywords = {
            "mean",
            "stdev",
            "standard deviation",
            "sample",
            "measurement_count",
            "seed",
            "random",
            "histogram",
            "frequency",
            "counts",
            "batch",
        }

        def check_values(obj, path=""):
            if isinstance(obj, str):
                lower = obj.lower()
                for kw in simulation_keywords:
                    if kw in lower:
                        pytest.fail(
                            f"Simulation keyword '{kw}' found in value at {path}: "
                            f"'{obj[:80]}...'"
                        )
            elif isinstance(obj, dict):
                for k, v in obj.items():
                    check_values(v, f"{path}.{k}")
            elif isinstance(obj, list):
                for i, v in enumerate(obj):
                    check_values(v, f"{path}[{i}]")

        check_values(proof_data)

    def test_node_kinds_are_valid(self, proof_data):
        """Node kinds must be axiom, definition, or theorem."""
        valid_kinds = {"axiom", "definition", "theorem"}
        for node in proof_data["nodes"]:
            assert node["kind"] in valid_kinds, (
                f"Node '{node['name']}' has invalid kind '{node['kind']}'. "
                f"Valid: {valid_kinds}"
            )

    def test_dependencies_reference_existing_nodes(self, proof_data):
        """All dependency references must point to nodes that exist."""
        node_ids = {n["id"] for n in proof_data["nodes"]}
        for node in proof_data["nodes"]:
            for dep in node.get("dependencies", []):
                assert dep in node_ids, (
                    f"Node '{node['name']}' depends on '{dep}' "
                    f"which is not in the node list."
                )

    def test_source_files_are_lean(self, proof_data):
        """All source_file references must be .lean files."""
        for node in proof_data["nodes"]:
            src = node.get("source_file", "")
            if src:
                assert src.endswith(
                    ".lean"
                ), f"Node '{node['name']}' references non-Lean source: '{src}'"

    def test_walk_order_covers_all_nodes(self, proof_data):
        """Walk order must include all nodes exactly once."""
        walk = proof_data["walk_order"]
        node_ids = [n["id"] for n in proof_data["nodes"]]
        assert sorted(walk) == sorted(node_ids), (
            f"Walk order doesn't match node list.\n"
            f"In walk but not nodes: {set(walk) - set(node_ids)}\n"
            f"In nodes but not walk: {set(node_ids) - set(walk)}"
        )


# ============================================================================
# Test 3: Sabotage test (independence from simulation)
# ============================================================================


class TestSabotageIndependence:
    """Verify export_data.py produces identical output regardless of
    whether the Python simulation code exists."""

    def test_output_unchanged_without_simulation_dir(self, tmp_path):
        """Run export_data.py with PYTHONPATH cleared — no access to
        simulation modules — and verify the output is identical."""
        # First, generate the reference output
        result_ref = subprocess.run(
            [sys.executable, str(EXPORT_SCRIPT)],
            capture_output=True,
            text=True,
            cwd=str(PROJECT_ROOT),
        )
        assert (
            result_ref.returncode == 0
        ), f"export_data.py failed:\n{result_ref.stderr}"

        # Read reference output
        ref_json = PROOF_GRAPH_JSON.read_text()

        # Now run with PYTHONPATH pointing to empty dir (no simulation access)
        env_clean = {
            "PYTHONPATH": str(tmp_path),  # empty, blocks local imports
            "PATH": "/usr/bin:/bin",
            "HOME": str(tmp_path),
        }
        result_clean = subprocess.run(
            [sys.executable, str(EXPORT_SCRIPT)],
            capture_output=True,
            text=True,
            cwd=str(PROJECT_ROOT),
            env=env_clean,
        )
        assert (
            result_clean.returncode == 0
        ), f"export_data.py failed in clean env:\n{result_clean.stderr}"

        # Re-read the output (script overwrites the file)
        clean_json = PROOF_GRAPH_JSON.read_text()

        assert ref_json == clean_json, (
            "export_data.py produces different output when simulation "
            "code is not accessible. This indicates a hidden dependency."
        )

    def test_lean_files_are_sole_input(self):
        """Verify the script reads exactly the expected Lean files."""
        source = EXPORT_SCRIPT.read_text()

        # Check that BASIC_LEAN and SG_LEAN are the only file inputs
        assert "Basic.lean" in source, "export_data.py should reference Basic.lean"
        assert (
            "SternGerlach.lean" in source
        ), "export_data.py should reference SternGerlach.lean"

        # Count Path / open / read_text calls to ensure no unexpected file reads
        tree = ast.parse(source)
        # This is a structural check — we're verifying the script shape
        file_refs = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr == "read_text":
                file_refs.append(node)
        # Should have exactly 2 read_text() calls (one per Lean file)
        # plus potentially the output write
        assert len(file_refs) <= 3, (
            f"export_data.py has {len(file_refs)} read_text() calls. "
            f"Expected at most 3 (2 Lean inputs + 1 self-reference at most)."
        )
