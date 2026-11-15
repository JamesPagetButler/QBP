#!/usr/bin/env python3
"""Generate / check the Python-side pinned test vectors for si_conversion (#329).

    python3 scripts/gen_si_conversion_vectors.py          # (re)write the fixture
    python3 scripts/gen_si_conversion_vectors.py --check  # exit 1 if fixture drifted

Output: tests/fixtures/si_conversion_vectors.json

This is the PYTHON side of the cross-language agreement (issue #329 AC
"Cross-language verification (Python and Lean agree)").  The Lean side —
emitting the same vectors from proofs/QBP/Units/Oracle.lean — waits on #354
(Real->Float bridge) and is NOT produced here.  Where this file overlaps the
existing Lean oracle fixture (tests/fixtures/si_test_vectors.json: electron /
neutron scale factors, position / energy / potential at 3.7 / 5.5 / 10.0) the
inputs are identical on purpose so tests/test_si_conversion_contract.py can
assert Python == Lean on the overlap.

Floats are written with repr() (shortest round-tripping, 17 sig. digits), so
the fixture reproduces bit-for-bit on any IEEE 754 double platform.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.simulation import si_conversion as si  # noqa: E402

FIXTURE = ROOT / "tests" / "fixtures" / "si_conversion_vectors.json"

# Inputs. electron/neutron match the Lean oracle (GenTestVectors.lean);
# muon/uranium are the TestStressParticles extremes from test_si_conversion.py.
PARTICLES = {
    "electron": (9.109_383_7015e-31, 5.0e-11),  # CODATA 2018 mass; 0.05 nm
    "neutron": (1.674_927_498_04e-27, 1.8e-10),  # CODATA 2018 mass; thermal
    "muon": (1.883_531_627e-28, 1.0e-12),  # CODATA 2018 mass; hard X-ray
    "uranium238": (3.952_860e-25, 5.0e-12),  # heavy-mass extreme
}
CODE_INPUTS = {"x_code": 3.7, "E_code": 5.5, "U_code": 10.0}
SI_INPUTS = {"val_m": 1.0e-9, "val_J": 1.0e-18}
# Layer 2 (PROVISIONAL) inputs: the values used in TestQuaternionicQuantities.
QUAT_INPUTS = [
    {"U1_si": 1e-18, "E_kin_si": 1e-17, "v_g_si": 1e6},
    {"U1_si": 5e-18, "E_kin_si": 1e-17, "v_g_si": 1e6},
    {"U1_si": 2e-18, "E_kin_si": 1e-17, "v_g_si": 1e6},
]


def build() -> dict:
    status = {r.name: r.status for r in si.STATUS_REGISTRY}
    constants = [
        {"name": n, "value": getattr(si, n), "status": status[n]}
        for n in (
            "H_SI",
            "HBAR_SI",
            "EV_IN_JOULES",
            "C_SI",
            "HBAR_CODE",
            "M_CODE",
            "K0_CODE",
            "V_Z_CODE",
        )
    ]
    vectors: list[dict] = []
    for particle, (m, lam) in PARTICLES.items():
        sc = si.compute_scales(m, lam)
        inputs = {"m_si": m, "lambda_si": lam}
        vectors.append(
            {
                "function": "compute_scales",
                "status": status["compute_scales"],
                "particle": particle,
                "inputs": inputs,
                "outputs": {
                    k: getattr(sc, k) for k in ("L0", "E0", "T0", "v_z_si", "k_si")
                },
            }
        )
        one_arg = [
            ("convert_position", "x_code", CODE_INPUTS["x_code"]),
            ("convert_energy", "E_code", CODE_INPUTS["E_code"]),
            ("convert_potential", "U_code", CODE_INPUTS["U_code"]),
            ("convert_length_to_code", "val_m", SI_INPUTS["val_m"]),
            ("convert_energy_to_code", "val_J", SI_INPUTS["val_J"]),
        ]
        for fn, arg, val in one_arg:
            vectors.append(
                {
                    "function": fn,
                    "status": status[fn],
                    "particle": particle,
                    "scales_from": inputs,
                    "inputs": {arg: val},
                    "output": getattr(si, fn)(val, sc),
                }
            )
    for q in QUAT_INPUTS:
        qq = si.compute_quaternionic_quantities(**q)
        vectors.append(
            {
                "function": "compute_quaternionic_quantities",
                "status": status["compute_quaternionic_quantities"],
                "inputs": q,
                "outputs": {"L_Q": qq.L_Q, "zeta": qq.zeta},
            }
        )
    return {
        "generator": "scripts/gen_si_conversion_vectors.py",
        "library": "src/simulation/si_conversion.py",
        "library_version": si.__version__,
        "lean_side": (
            "PENDING #354 — Python-side pin only. Overlap with the Lean oracle "
            "fixture tests/fixtures/si_test_vectors.json is asserted equal in "
            "tests/test_si_conversion_contract.py."
        ),
        "tolerance_rel": 1e-15,
        "constants": constants,
        "vectors": vectors,
    }


def dumps(d: dict) -> str:
    return json.dumps(d, indent=1) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="fail if fixture differs")
    args = ap.parse_args()
    text = dumps(build())
    if args.check:
        if not FIXTURE.exists() or FIXTURE.read_text() != text:
            print(f"DRIFT: {FIXTURE} differs from generator output", file=sys.stderr)
            return 1
        print(f"OK: {FIXTURE} matches generator ({len(build()['vectors'])} vectors)")
        return 0
    FIXTURE.write_text(text)
    print(f"wrote {FIXTURE} ({len(build()['vectors'])} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
