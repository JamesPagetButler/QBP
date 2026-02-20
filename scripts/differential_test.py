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


def compute_spin_prediction(case: dict[str, Any]) -> dict[str, float]:
    """Compute spin measurement predictions for Experiments 01/01b/edge/3d."""
    if "theta_s" in case:
        # General 3D case (#211)
        psi = qphysics.create_general_state(case["theta_s"], case["phi_s"])
        obs = qphysics.create_general_state(case["theta_o"], case["phi_o"])
    else:
        # xz-plane case (original)
        psi = qphysics.create_tilted_state(case["theta_rad"])
        obs = qphysics.SPIN_Z

    exp_val = qphysics.expectation_value(psi, obs)
    prob_up = (1 + exp_val) / 2.0
    prob_down = (1 - exp_val) / 2.0

    return {
        "expectation": exp_val,
        "prob_up": prob_up,
        "prob_down": prob_down,
    }


def _coupling_handler(case: dict[str, Any]) -> dict[str, float]:
    result = qphysics.coupling_decomposition(
        case["U0"], case["U1"], case["a0"], case["b0"], case["a1"], case["b1"]
    )
    return {
        "re": result["re"],
        "imI": result["imI"],
        "imJ": result["imJ"],
        "imK": result["imK"],
    }


def _normSq_handler(case: dict[str, Any]) -> dict[str, float]:
    return {
        "normSq": qphysics.normSq_sympForm(
            case["re0"], case["im0"], case["re1"], case["im1"]
        )
    }


def _visibility_handler(case: dict[str, Any]) -> dict[str, float]:
    return {"visibility": qphysics.visibility(case["Imax"], case["Imin"])}


def _fraunhofer_handler(case: dict[str, Any]) -> dict[str, float]:
    return {
        "intensity": qphysics.fraunhofer_intensity(
            case["I0"], case["d"], case["lam"], case["L"], case["x"]
        )
    }


def _fringe_spacing_handler(case: dict[str, Any]) -> dict[str, float]:
    return {"spacing": qphysics.fringe_spacing(case["lam"], case["L"], case["d"])}


def _eta_handler(case: dict[str, Any]) -> dict[str, float]:
    return {"eta": qphysics.quat_fraction(case["normSq0"], case["normSq1"])}


def _decay_constant_handler(case: dict[str, Any]) -> dict[str, float]:
    return {"kappa": qphysics.decay_constant(case["U1"], case["d_sep"])}


def _decay_length_handler(case: dict[str, Any]) -> dict[str, float]:
    return {"decay_length": qphysics.decay_length(case["kappa_in"])}


# Dispatch table: label prefix → handler function.
# Order matters: longer prefixes checked first to avoid ambiguity.
_DOUBLESLIT_DISPATCH: list[tuple[str, Any]] = [
    ("decay_constant", _decay_constant_handler),
    ("decay_length", _decay_length_handler),
    ("coupling", _coupling_handler),
    ("normSq", _normSq_handler),
    ("visibility", _visibility_handler),
    ("fraunhofer", _fraunhofer_handler),
    ("fringe_spacing", _fringe_spacing_handler),
    ("eta", _eta_handler),
]


def compute_doubleslit_prediction(case: dict[str, Any]) -> dict[str, float]:
    """Compute DoubleSlit scalar predictions for Experiment 03.

    Dispatches by label prefix via _DOUBLESLIT_DISPATCH table.
    Input fields are read from the oracle JSON case; output fields are returned.
    """
    label = case["label"]
    for prefix, handler in _DOUBLESLIT_DISPATCH:
        if label.startswith(prefix):
            return handler(case)
    raise ValueError(f"Unknown Exp 03 label: {label}")


def compute_python_prediction(case: dict[str, Any]) -> dict[str, float]:
    """Compute predictions using qphysics.py for a given test case.

    Dispatches to experiment-specific handler based on experiment type.
    """
    if case.get("experiment") == "03":
        return compute_doubleslit_prediction(case)
    return compute_spin_prediction(case)


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
        python = compute_python_prediction(case)

        # Compare all fields returned by the Python prediction
        for field in sorted(python.keys()):
            if field not in case:
                divergences.append(
                    {
                        "label": case["label"],
                        "field": field,
                        "oracle": None,
                        "python": python[field],
                        "difference": float("inf"),
                    }
                )
                total += 1
                continue
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
