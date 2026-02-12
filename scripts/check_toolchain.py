#!/usr/bin/env python3
"""
Toolchain Health Check

Verifies that local development tools match CI expectations.
Run this at session start to catch configuration drift early.

Usage:
    python scripts/check_toolchain.py
    python scripts/check_toolchain.py --fix  # Auto-fix version mismatches
"""

import subprocess
import sys
import re
from pathlib import Path

# Expected versions (must match .pre-commit-config.yaml and CI)
EXPECTED = {
    "black": "24.4.2",
    "mypy": "1.14",  # Major.minor only - patch can vary
    "python": "3.10",  # Minimum version
}

# ANSI colors
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
RESET = "\033[0m"


def get_version(tool: str) -> str | None:
    """Get installed version of a tool."""
    try:
        if tool == "python":
            result = subprocess.run(
                [sys.executable, "--version"],
                capture_output=True,
                text=True,
            )
            match = re.search(r"(\d+\.\d+\.\d+)", result.stdout)
        else:
            result = subprocess.run(
                [tool, "--version"],
                capture_output=True,
                text=True,
            )
            match = re.search(r"(\d+\.\d+\.?\d*)", result.stdout + result.stderr)

        return match.group(1) if match else None
    except FileNotFoundError:
        return None


def version_matches(installed: str, expected: str) -> bool:
    """Check if installed version is >= expected (major.minor)."""
    if not installed:
        return False
    inst_parts = [int(x) for x in installed.split(".")[:2]]
    exp_parts = [int(x) for x in expected.split(".")[:2]]
    return inst_parts >= exp_parts


def check_pre_commit_installed() -> bool:
    """Check if pre-commit hooks are installed."""
    hook_path = Path(".git/hooks/pre-commit")
    return hook_path.exists() and "pre-commit" in hook_path.read_text()


def main(fix: bool = False) -> int:
    print("=" * 50)
    print("QBP Toolchain Health Check")
    print("=" * 50)
    print()

    issues = []

    # Check each tool
    for tool, expected in EXPECTED.items():
        installed = get_version(tool)
        if not installed:
            print(f"{RED}[MISSING]{RESET} {tool}: not found")
            issues.append(f"{tool} not installed")
        elif version_matches(installed, expected):
            print(f"{GREEN}[OK]{RESET} {tool}: {installed} (expected {expected}+)")
        else:
            print(
                f"{YELLOW}[MISMATCH]{RESET} {tool}: {installed} (expected {expected}+)"
            )
            if tool != "python":
                issues.append(f"{tool} version mismatch")

    print()

    # Check pre-commit hooks
    if check_pre_commit_installed():
        print(f"{GREEN}[OK]{RESET} pre-commit hooks installed")
    else:
        print(f"{YELLOW}[WARN]{RESET} pre-commit hooks not installed")
        issues.append("pre-commit hooks not installed")

    # Check pyproject.toml exists
    if Path("pyproject.toml").exists():
        print(f"{GREEN}[OK]{RESET} pyproject.toml exists")
    else:
        print(f"{YELLOW}[WARN]{RESET} pyproject.toml missing")
        issues.append("pyproject.toml missing")

    print()

    # Summary
    if not issues:
        print(f"{GREEN}All checks passed!{RESET}")
        return 0

    print(f"{YELLOW}Issues found:{RESET}")
    for issue in issues:
        print(f"  - {issue}")

    if fix:
        print()
        print("Attempting fixes...")

        # Fix tool versions
        if "black version mismatch" in issues:
            print("  Installing black==24.4.2...")
            subprocess.run([sys.executable, "-m", "pip", "install", "black==24.4.2"])

        if "mypy version mismatch" in issues:
            print("  Installing mypy>=1.14...")
            subprocess.run([sys.executable, "-m", "pip", "install", "mypy>=1.14"])

        if "pre-commit hooks not installed" in issues:
            print("  Installing pre-commit hooks...")
            subprocess.run(["pre-commit", "install"])

        print()
        print("Re-run this script to verify fixes.")
    else:
        print()
        print(f"Run with --fix to auto-repair, or manually:")
        print(f"  pip install black==24.4.2 mypy>=1.14")
        print(f"  pre-commit install")

    return 1


if __name__ == "__main__":
    fix_mode = "--fix" in sys.argv
    sys.exit(main(fix=fix_mode))
