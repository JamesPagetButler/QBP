#!/usr/bin/env python3
"""
Phase 4d: Differential Testing Harness

Compares Python qphysics.py computations against Lean-proven oracle predictions.
Uses the Cedar pattern: proven oracle generates expected values, Python must match.

Usage:
    python scripts/differential_test.py                    # Run all tests
    python scripts/differential_test.py --tolerance 1e-8   # Custom tolerance
    python scripts/differential_test.py --verbose          # Show all comparisons

Exit codes:
    0 = All tests pass (0 divergences)
    1 = Divergences detected
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import numpy as np

# Add project root to path for qphysics import
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))

import qphysics  # noqa: E402


def load_oracle_predictions(path: Path | None = None) -> list[dict[str, Any]]:
    """Load oracle predictions from JSON file."""
    if path is None:
        path = project_root / "tests" / "oracle_predictions.json"
    with open(path) as f:
        return json.load(f)


def compute_python_prediction(theta_rad: float) -> dict[str, float]:
    """Compute predictions using qphysics.py for a given angle."""
    psi = qphysics.create_tilted_state(theta_rad)
    obs = qphysics.SPIN_Z

    exp_val = qphysics.expectation_value(psi, obs)
    prob_up = (1 + exp_val) / 2.0
    prob_down = (1 - exp_val) / 2.0

    return {
        "expectation": exp_val,
        "prob_up": prob_up,
        "prob_down": prob_down,
    }


def run_differential_tests(
    oracle_path: Path | None = None,
    tolerance: float = 1e-6,
    verbose: bool = False,
) -> tuple[int, int, list[dict[str, Any]]]:
    """
    Run differential tests comparing Python against Lean oracle.

    Returns:
        (total_tests, divergences_count, divergence_details)
    """
    predictions = load_oracle_predictions(oracle_path)
    divergences: list[dict[str, Any]] = []
    total = 0

    for case in predictions:
        theta = case["theta_rad"]
        python = compute_python_prediction(theta)

        for field in ["prob_up", "prob_down", "expectation"]:
            total += 1
            oracle_val = case[field]
            python_val = python[field]
            diff = abs(oracle_val - python_val)

            if verbose:
                status = "PASS" if diff <= tolerance else "FAIL"
                print(
                    f"  [{status}] {case['label']}.{field}: "
                    f"oracle={oracle_val:.10f} python={python_val:.10f} "
                    f"diff={diff:.2e}"
                )

            if diff > tolerance:
                divergences.append(
                    {
                        "label": case["label"],
                        "field": field,
                        "theta_rad": theta,
                        "oracle": oracle_val,
                        "python": python_val,
                        "difference": diff,
                    }
                )

    return total, len(divergences), divergences


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Phase 4d: Differential Testing (Python vs Lean Oracle)"
    )
    parser.add_argument(
        "--tolerance",
        type=float,
        default=1e-6,
        help="Maximum allowed difference (default: 1e-6)",
    )
    parser.add_argument(
        "--oracle",
        type=Path,
        default=None,
        help="Path to oracle_predictions.json",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Show all comparisons"
    )
    args = parser.parse_args()

    print("Phase 4d: Differential Testing — Python vs Lean Oracle")
    print(f"Tolerance: {args.tolerance:.0e}")
    print()

    total, divergences, details = run_differential_tests(
        oracle_path=args.oracle,
        tolerance=args.tolerance,
        verbose=args.verbose,
    )

    print()
    print(f"Results: {total} comparisons, {divergences} divergences")

    if divergences > 0:
        print("\nDIVERGENCES DETECTED:")
        for d in details:
            print(
                f"  {d['label']}.{d['field']}: "
                f"oracle={d['oracle']:.10f} python={d['python']:.10f} "
                f"diff={d['difference']:.2e}"
            )
        return 1
    else:
        print("All tests PASS — Python matches Lean oracle.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
