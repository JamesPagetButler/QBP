#!/usr/bin/env python3
"""
export_data.py — Parse Lean proof files and export proof dependency graph as JSON.

Reads:
  proofs/QBP/Basic.lean
  proofs/QBP/Experiments/SternGerlach.lean

Outputs:
  data/proof_graph_01.json

This is a semi-automated tool: it extracts theorem names and dependencies
from the Lean source, and augments them with human-curated physical meanings.
"""

import json
import re
import sys
from pathlib import Path

# Project root (two levels up from this script's location in src/viz/interactive/)
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent

BASIC_LEAN = PROJECT_ROOT / "proofs" / "QBP" / "Basic.lean"
SG_LEAN = PROJECT_ROOT / "proofs" / "QBP" / "Experiments" / "SternGerlach.lean"
OUTPUT = Path(__file__).resolve().parent / "data" / "proof_graph_01.json"


def parse_lean_file(path: Path) -> list[dict]:
    """Extract theorem/def names and their statements from a Lean file."""
    items = []
    text = path.read_text()

    # Match theorem/def declarations
    pattern = re.compile(
        r"(?:^|\n)\s*(?:/--.*?-/\s*\n)?"  # optional doc comment
        r"(theorem|def|noncomputable def|abbrev)\s+"
        r"(\w+)"                              # name
        r"(.*?)(?=\n(?:theorem|def|noncomputable|abbrev|end |--|/-)|\Z)",  # body
        re.DOTALL
    )

    for m in pattern.finditer(text):
        kind = m.group(1).strip()
        name = m.group(2)
        body = m.group(3).strip()

        # Clean up the statement (first line of body)
        statement_lines = []
        for line in body.split("\n"):
            stripped = line.strip()
            if stripped.startswith("--") or stripped.startswith("/-"):
                break
            if stripped.startswith("simp") or stripped.startswith("exact"):
                break
            if stripped:
                statement_lines.append(stripped)
            if ":=" in stripped or "by" == stripped.rstrip():
                break

        statement = " ".join(statement_lines)

        # Determine kind
        if kind in ("def", "noncomputable def", "abbrev"):
            node_kind = "definition" if "def" in kind else "definition"
        else:
            node_kind = "theorem"

        items.append({
            "name": name,
            "kind": node_kind,
            "statement": statement,
            "source": path.name,
        })

    return items


# Human-curated physical meanings for the Stern-Gerlach proof chain
PHYSICAL_MEANINGS = {
    "isUnitQuaternion": "Axiom 1: A quantum state is a unit quaternion (|psi|^2 = 1).",
    "isPureQuaternion": "Axiom 2: An observable is a pure quaternion (scalar part = 0).",
    "spin_x_is_pure": "SPIN_X = i is a valid observable (pure quaternion).",
    "spin_y_is_pure": "SPIN_Y = j is a valid observable (pure quaternion).",
    "spin_z_is_pure": "SPIN_Z = k is a valid observable (pure quaternion).",
    "vecDot": "Dot product of vector parts: measures alignment between states.",
    "expectationValue": "Expectation value: vecDot of state and observable vector parts.",
    "probUp": "Probability of measuring +1 (spin up): (1 + <O>) / 2.",
    "probDown": "Probability of measuring -1 (spin down): (1 - <O>) / 2.",
    "expectation_orthogonal_is_zero": "General principle: perpendicular states always give zero expectation.",
    "prob_up_orthogonal_is_half": "General: perpendicular measurement gives 50% spin-up.",
    "spinXState": "Experiment state: particle with spin along +x axis (quaternion i).",
    "spinZObservable": "Measurement axis: spin measured along z axis (quaternion k).",
    "spinXState_is_pure": "The spin-x state satisfies the pure quaternion axiom.",
    "spinZObservable_is_pure": "The spin-z observable satisfies the pure quaternion axiom.",
    "x_z_orthogonal": "The x and z spin axes are perpendicular: their dot product is zero.",
    "expectation_x_measured_z_is_zero": "Core result: <O_z> = 0 for spin-x state. Average measurement is zero.",
    "prob_up_x_measured_z_is_half": "Probability of spin-up (+1) is exactly 50%.",
    "prob_down_x_measured_z_is_half": "Probability of spin-down (-1) is exactly 50%.",
}

# Dependency graph (manually curated from the Lean import chain)
DEPENDENCIES = {
    "isUnitQuaternion": [],
    "isPureQuaternion": [],
    "spin_x_is_pure": ["isPureQuaternion"],
    "spin_z_is_pure": ["isPureQuaternion"],
    "vecDot": [],
    "expectationValue": ["vecDot"],
    "probUp": ["expectationValue"],
    "probDown": ["expectationValue"],
    "expectation_orthogonal_is_zero": ["isPureQuaternion", "vecDot"],
    "prob_up_orthogonal_is_half": ["expectation_orthogonal_is_zero"],
    "spinXState": ["spin_x_is_pure"],
    "spinZObservable": ["spin_z_is_pure"],
    "spinXState_is_pure": ["spin_x_is_pure"],
    "spinZObservable_is_pure": ["spin_z_is_pure"],
    "x_z_orthogonal": ["vecDot", "spinXState", "spinZObservable"],
    "expectation_x_measured_z_is_zero": [
        "expectation_orthogonal_is_zero",
        "spinXState", "spinZObservable", "x_z_orthogonal"
    ],
    "prob_up_x_measured_z_is_half": ["expectation_x_measured_z_is_zero"],
    "prob_down_x_measured_z_is_half": ["expectation_x_measured_z_is_zero"],
}

# Nodes to include in the Stern-Gerlach visualization (walk order)
SG_WALK_ORDER = [
    "isUnitQuaternion",
    "isPureQuaternion",
    "vecDot",
    "spin_x_is_pure",
    "spin_z_is_pure",
    "spinXState",
    "spinZObservable",
    "x_z_orthogonal",
    "expectation_orthogonal_is_zero",
    "expectation_x_measured_z_is_zero",
    "prob_up_x_measured_z_is_half",
    "prob_down_x_measured_z_is_half",
]


def build_graph() -> dict:
    """Build the proof graph JSON structure."""
    # Parse Lean files for statement text
    basic_items = parse_lean_file(BASIC_LEAN)
    sg_items = parse_lean_file(SG_LEAN)
    all_items = {item["name"]: item for item in basic_items + sg_items}

    nodes = []
    for name in SG_WALK_ORDER:
        item = all_items.get(name, {})
        kind = "axiom" if name in ("isUnitQuaternion", "isPureQuaternion") else \
               item.get("kind", "theorem")

        node = {
            "id": name,
            "name": name,
            "kind": kind,
            "statement": item.get("statement", name),
            "physical_meaning": PHYSICAL_MEANINGS.get(name, ""),
            "dependencies": DEPENDENCIES.get(name, []),
            "source_file": item.get("source", ""),
        }
        nodes.append(node)

    return {
        "experiment": "01_stern_gerlach",
        "title": "Stern-Gerlach: Spin-X measured on Z-axis",
        "description": (
            "Formal proof that a spin-x state measured on the z-axis "
            "produces a 50/50 probability split, as predicted by the "
            "QBP quaternion framework and observed in the Stern-Gerlach experiment."
        ),
        "walk_order": SG_WALK_ORDER,
        "nodes": nodes,
    }


def main():
    graph = build_graph()

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT, "w") as f:
        json.dump(graph, f, indent=2)

    print(f"Exported {len(graph['nodes'])} nodes to {OUTPUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
