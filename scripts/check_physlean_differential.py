#!/usr/bin/env python3
"""PhysLean <-> QBP differential pre-commit guard (QBP #492-class / #504).

Runs the prebuilt PhysLean bridge oracle (an independent PhysLean QuantumInfo
derivation of the spin-1/2 angle-dependent Born-rule predictions) and diffs its
emitted JSON against QBP's ground-truth ``tests/oracle_predictions.json`` using
the bridge's own ``diff_oracle.py`` harness. A bit-exact mismatch surfaces a
cross-backend discrepancy -- exactly the class of data-quality / physics bug the
bridge was built to catch (#490, #492).

Design contract (read this -- it is the reason this guard is safe to ship):

* The PhysLean bridge is an ~8 GB Lean build that lives OUTSIDE this repo's
  master-based history (PR #493). If the bridge executable or its diff harness
  is absent -- not built, or the bridge project not merged -- this guard prints
  a LOUD warning and exits 0. It NEVER triggers the 8 GB build, and it NEVER
  fails silently.
* When the bridge IS present, the guard propagates ``diff_oracle.py``'s exit
  code verbatim (0 PASS / 1 FAIL), so a real discrepancy blocks the commit.

Usage::

    python scripts/check_physlean_differential.py
    python scripts/check_physlean_differential.py --self-test   # inject a known
                                                                # corruption -> FAIL

Environment overrides (verification / non-default layouts only)::

    QBP_PHYSLEAN_BRIDGE_DIR   path to the ``proofs-physlean-bridge`` directory
                              (default: ``<repo-root>/proofs-physlean-bridge``)
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

# ANSI colors (match scripts/check_toolchain.py).
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
RESET = "\033[0m"

# Bridge layout, relative to the bridge directory.
BRIDGE_EXE_RELPATH = Path(".lake") / "build" / "bin" / "physlean_oracle"
DIFF_SCRIPT_NAME = "diff_oracle.py"
# QBP ground-truth fixture, relative to repo root.
QBP_FIXTURE_RELPATH = Path("tests") / "oracle_predictions.json"
# Self-test corruption: perturb one PhysLean value to confirm FAIL fires (AC-T4
# shape). Format consumed by diff_oracle.py's --corrupt: LABEL:FIELD:DELTA.
SELF_TEST_CORRUPTION = "angle_dep_45.000000deg:prob_up:0.001"


def repo_root() -> Path:
    """Return the git repository root, or fall back to this file's grandparent."""
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        )
        return Path(out.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return Path(__file__).resolve().parent.parent


def bridge_dir(root: Path) -> Path:
    """Resolve the PhysLean bridge directory (env override wins)."""
    override = os.environ.get("QBP_PHYSLEAN_BRIDGE_DIR")
    if override:
        return Path(override)
    return root / "proofs-physlean-bridge"


def warn_skip(reason: str) -> int:
    """Print a LOUD skip warning and return success (never block the commit)."""
    print(f"{YELLOW}{'=' * 72}{RESET}", file=sys.stderr)
    print(
        f"{YELLOW}PhysLean differential guard SKIPPED -- {reason}.{RESET}",
        file=sys.stderr,
    )
    print(
        f"{YELLOW}The ~8 GB PhysLean bridge build is intentionally NOT triggered "
        f"by this hook.{RESET}",
        file=sys.stderr,
    )
    print(
        f"{YELLOW}Build/merge the bridge to enable bit-exact cross-backend "
        f"checking; see #504.{RESET}",
        file=sys.stderr,
    )
    print(f"{YELLOW}{'=' * 72}{RESET}", file=sys.stderr)
    return 0


def run_bridge_oracle(exe: Path) -> str:
    """Run the PhysLean bridge oracle and return its JSON stdout.

    The oracle emits the JSON document on stdout; any build/log chatter is
    stripped by slicing from the first ``[`` to the last ``]``.
    """
    result = subprocess.run(
        [str(exe)],
        capture_output=True,
        text=True,
        check=True,
    )
    out = result.stdout
    start = out.find("[")
    end = out.rfind("]")
    if start == -1 or end == -1 or end < start:
        raise ValueError("PhysLean oracle produced no JSON array on stdout:\n" + out)
    return out[start : end + 1]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="PhysLean<->QBP differential pre-commit guard"
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="inject a known PhysLean corruption to confirm the guard FAILs",
    )
    args = parser.parse_args()

    root = repo_root()
    bdir = bridge_dir(root)
    exe = bdir / BRIDGE_EXE_RELPATH
    diff_script = bdir / DIFF_SCRIPT_NAME
    fixture = root / QBP_FIXTURE_RELPATH

    # Absent-bridge path: warn loudly, exit 0 (never block, never build).
    if not exe.exists():
        return warn_skip(f"bridge oracle not built at {exe}")
    if not diff_script.exists():
        return warn_skip(f"bridge diff harness not found at {diff_script}")
    if not fixture.exists():
        return warn_skip(f"QBP fixture not found at {fixture}")

    # Present-bridge path: run the oracle, diff against the QBP fixture.
    try:
        physlean_json = run_bridge_oracle(exe)
    except (subprocess.CalledProcessError, ValueError, OSError) as exc:
        print(
            f"{RED}PhysLean differential guard ERROR: failed to run bridge "
            f"oracle: {exc}{RESET}",
            file=sys.stderr,
        )
        return 1

    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as tmp:
        tmp.write(physlean_json)
        tmp_path = tmp.name

    try:
        cmd = [
            sys.executable,
            str(diff_script),
            "--physlean",
            tmp_path,
            "--qbp",
            str(fixture),
        ]
        if args.self_test:
            cmd += ["--corrupt", SELF_TEST_CORRUPTION]
        # diff_oracle.py prints its table + verdict to stdout/stderr already.
        completed = subprocess.run(cmd)
    finally:
        os.unlink(tmp_path)

    if completed.returncode != 0:
        print(
            f"{RED}PhysLean differential guard: FAIL "
            f"(see #492-class data-quality vs physics-discrepancy guidance in "
            f"the diff output above).{RESET}",
            file=sys.stderr,
        )
    else:
        print(
            f"{GREEN}PhysLean differential guard: PASS "
            f"(QBP and PhysLean agree bit-exactly).{RESET}",
            file=sys.stderr,
        )
    return completed.returncode


if __name__ == "__main__":
    sys.exit(main())
