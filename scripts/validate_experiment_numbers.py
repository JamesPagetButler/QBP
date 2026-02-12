#!/usr/bin/env python3
"""
Validate experiment number uniqueness across the codebase.

Checks that no two experiments have the same number in:
- research/XX_*_expected_results.md
- experiments/XX_*/
- results/XX_*/

Note: Sub-experiments use letter suffixes (e.g., 01b is an extension of 01).
The base number (01) and sub-experiment (01b) are considered distinct.

Usage:
    python scripts/validate_experiment_numbers.py

Exit codes:
    0 - All experiment numbers are unique
    1 - Duplicate experiment numbers found
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path


def extract_experiment_number(name: str) -> str | None:
    """
    Extract experiment number from a directory or file name.

    Matches patterns like:
    - 01_stern_gerlach -> 01
    - 01b_angle_dependent -> 01b
    - 03_double_slit -> 03

    Returns None if no experiment number found.
    """
    match = re.match(r"^(\d{2}[a-z]?)_", name)
    return match.group(1) if match else None


def find_experiments(base_path: Path) -> dict[str, list[str]]:
    """
    Find all experiment numbers in a directory.

    Returns dict mapping experiment number to list of names.
    """
    experiments: dict[str, list[str]] = defaultdict(list)

    if not base_path.exists():
        return experiments

    for item in base_path.iterdir():
        name = item.name
        exp_num = extract_experiment_number(name)
        if exp_num:
            experiments[exp_num].append(name)

    return experiments


def validate_no_duplicates(
    experiments: dict[str, list[str]], location: str
) -> list[str]:
    """
    Check for duplicate experiment numbers.

    Returns list of error messages.
    """
    errors = []
    for exp_num, names in experiments.items():
        if len(names) > 1:
            name_list = "\n".join(f"  - {n}" for n in names)
            errors.append(
                f"Duplicate experiment number '{exp_num}' in {location}:\n"
                f"{name_list}"
            )
    return errors


def main():
    """Main validation routine."""
    root = Path(__file__).parent.parent
    all_errors = []

    # Check research files
    research_experiments = find_experiments(root / "research")
    # Filter to only expected_results.md files
    research_filtered = defaultdict(list)
    for exp_num, names in research_experiments.items():
        for name in names:
            if name.endswith("_expected_results.md"):
                research_filtered[exp_num].append(name)
    all_errors.extend(validate_no_duplicates(research_filtered, "research/"))

    # Check experiment directories
    exp_experiments = find_experiments(root / "experiments")
    all_errors.extend(validate_no_duplicates(exp_experiments, "experiments/"))

    # Check results directories
    results_experiments = find_experiments(root / "results")
    all_errors.extend(validate_no_duplicates(results_experiments, "results/"))

    # Cross-check: warn if research file exists without experiment dir
    research_nums = set(research_filtered.keys())
    exp_nums = set(exp_experiments.keys())

    for num in research_nums - exp_nums:
        # This is a warning, not an error (planned experiments are okay)
        print(f"Note: research/{num}_* exists but experiments/{num}_*/ does not")

    # Cross-check: warn if results dir exists without experiment dir
    results_nums = set(results_experiments.keys())
    for num in results_nums - exp_nums:
        print(
            f"Warning: results/{num}_* exists but experiments/{num}_*/ does not "
            "(orphan results directory)"
        )

    if all_errors:
        print("VALIDATION FAILED: Duplicate experiment numbers found\n")
        for error in all_errors:
            print(error)
            print()
        print(
            "Fix: Ensure each experiment has a unique number. "
            "Use letter suffixes (e.g., 01b) for sub-experiments."
        )
        return 1

    print("VALIDATION PASSED: All experiment numbers are unique")

    # Print summary
    all_nums = sorted(research_nums | exp_nums)
    if all_nums:
        print(f"\nExperiments found: {', '.join(all_nums)}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
