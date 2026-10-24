"""
API contract tests for src/simulation/si_conversion.py (#329, Python slice).

Complements tests/test_si_conversion.py (unit + hypothesis + Lean oracle) and
tests/test_si_defining_constants.py (7 SI defining constants).  This file adds:

  1. Versioned API + ESTABLISHED/PROVISIONAL status registry
  2. Coverage enumeration: every public callable has a registry entry AND a
     test that names it — adding a function without either fails here
  3. Property tests not previously present: composition (a->b->c == a->c),
     frame change, dimensional consistency, potential / Layer-2 round-trips
  4. Cross-language AC, Python side: the pinned fixture
     tests/fixtures/si_conversion_vectors.json reproduces, and agrees with
     the Lean oracle fixture (si_test_vectors.json) on the overlap.  The Lean
     side of emitting si_conversion_vectors.json waits on #354.
"""

from __future__ import annotations

import ast
import inspect
import json
import math
import re
from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.simulation import si_conversion as si
from src.simulation.si_conversion import (
    ESTABLISHED,
    EV_IN_JOULES,
    HBAR_SI,
    K0_CODE,
    M_CODE,
    PROVISIONAL,
    STATUS_REGISTRY,
    V_Z_CODE,
    QuantityStatus,
    ScaleFactors,
    compute_quaternionic_quantities,
    compute_scales,
    convert_energy,
    convert_energy_to_code,
    convert_length_to_code,
    convert_position,
    convert_potential,
    established_quantities,
    provisional_quantities,
    quantity_status,
)

TESTS_DIR = Path(__file__).parent
PY_FIXTURE = TESTS_DIR / "fixtures" / "si_conversion_vectors.json"
LEAN_FIXTURE = TESTS_DIR / "fixtures" / "si_test_vectors.json"
SI_TEST_FILES = sorted(TESTS_DIR.glob("test_si*.py"))

# Names that are API *about* the registry rather than quantities in it.
REGISTRY_API = {"quantity_status", "provisional_quantities", "established_quantities"}

# ---------------------------------------------------------------------------
# hypothesis strategies (same physical ranges as test_si_conversion.py)
# ---------------------------------------------------------------------------
st_mass = st.floats(
    min_value=1e-31, max_value=1e-24, allow_nan=False, allow_infinity=False
)
st_wavelength = st.floats(
    min_value=1e-12, max_value=1e-8, allow_nan=False, allow_infinity=False
)
st_code_value = st.floats(
    min_value=-1e6,
    max_value=1e6,
    allow_nan=False,
    allow_infinity=False,
    allow_subnormal=False,
).filter(lambda x: x == 0.0 or abs(x) > 1e-250)
st_pos_si_energy = st.floats(
    min_value=1e-22, max_value=1e-14, allow_nan=False, allow_infinity=False
)
st_velocity = st.floats(
    min_value=1.0, max_value=1e8, allow_nan=False, allow_infinity=False
)
st_factor = st.floats(
    min_value=1e-3, max_value=1e3, allow_nan=False, allow_infinity=False
)


def _public_members() -> dict[str, object]:
    """Public callables (functions + classes) defined in si_conversion itself."""
    out: dict[str, object] = {}
    for name, obj in inspect.getmembers(si):
        if name.startswith("_"):
            continue
        if not (inspect.isfunction(obj) or inspect.isclass(obj)):
            continue
        if getattr(obj, "__module__", None) != si.__name__:
            continue
        out[name] = obj
    return out


def _public_constants() -> dict[str, object]:
    """Module-level UPPER_CASE numeric constants."""
    return {
        n: v
        for n, v in vars(si).items()
        if re.fullmatch(r"[A-Z][A-Z0-9_]*", n)
        and isinstance(v, (int, float))
        and not isinstance(v, bool)
    }


def _test_function_sources() -> list[str]:
    """Unparsed source of every test_* function in tests/test_si*.py."""
    sources: list[str] = []
    for path in SI_TEST_FILES:
        tree = ast.parse(path.read_text(), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"):
                sources.append(ast.unparse(node))
    return sources


# ===================================================================
# 1. Version + registry
# ===================================================================


class TestVersionAndRegistry:
    def test_version_is_semver(self) -> None:
        assert re.fullmatch(r"\d+\.\d+\.\d+", si.__version__), si.__version__

    def test_status_literals(self) -> None:
        assert ESTABLISHED == "ESTABLISHED" and PROVISIONAL == "PROVISIONAL"

    def test_registry_entries_well_formed(self) -> None:
        names = [r.name for r in STATUS_REGISTRY]
        assert len(names) == len(set(names)), "duplicate registry names"
        for rec in STATUS_REGISTRY:
            assert isinstance(rec, QuantityStatus)
            assert rec.status in (ESTABLISHED, PROVISIONAL), rec
            assert rec.kind in {
                "constant",
                "function",
                "type",
                "quantity",
                "utility",
            }, rec
            assert len(rec.basis) >= 20, f"basis too thin to audit: {rec}"

    def test_partition_is_complete_and_disjoint(self) -> None:
        est = {r.name for r in established_quantities()}
        prov = {r.name for r in provisional_quantities()}
        assert est.isdisjoint(prov)
        assert est | prov == {r.name for r in STATUS_REGISTRY}

    def test_provisional_is_exactly_layer2(self) -> None:
        """The PROVISIONAL set is the module's existing Layer-2 line — nothing
        more, nothing less. Changing it is a physics decision for the beekeeper."""
        assert {r.name for r in provisional_quantities()} == {
            "QuaternionicQuantities",
            "compute_quaternionic_quantities",
            "L_Q",
            "zeta",
        }

    def test_established_constants_cite_si_or_derivation(self) -> None:
        for n in ("H_SI", "EV_IN_JOULES", "C_SI"):
            assert "2019 SI" in quantity_status(n).basis, n
        assert "H_SI" in quantity_status("HBAR_SI").basis
        assert "v_z_code_eq_40" in quantity_status("V_Z_CODE").basis

    def test_quantity_status_lookup_and_keyerror(self) -> None:
        assert quantity_status("compute_scales").status == ESTABLISHED
        assert quantity_status("zeta").status == PROVISIONAL
        with pytest.raises(KeyError):
            quantity_status("not_a_quantity")

    def test_registry_is_immutable(self) -> None:
        rec = quantity_status("zeta")
        with pytest.raises(Exception):
            rec.status = ESTABLISHED  # type: ignore[misc]


# ===================================================================
# 2. Coverage enumeration (inspect)
# ===================================================================


class TestPublicSurfaceCoverage:
    def test_every_public_callable_is_registered(self) -> None:
        public = set(_public_members()) - REGISTRY_API - {"QuantityStatus"}
        registered = {
            r.name for r in STATUS_REGISTRY if r.kind in ("function", "type", "utility")
        }
        missing = public - registered
        assert (
            not missing
        ), f"public callables without a status entry: {sorted(missing)}"
        stale = registered - public
        assert (
            not stale
        ), f"registry names that are not public callables: {sorted(stale)}"

    def test_every_public_constant_is_registered(self) -> None:
        consts = set(_public_constants()) - {"ESTABLISHED", "PROVISIONAL"}
        registered = {r.name for r in STATUS_REGISTRY if r.kind == "constant"}
        assert consts == registered, (
            sorted(consts - registered),
            sorted(registered - consts),
        )

    def test_every_public_callable_has_a_test(self) -> None:
        """Each public function/class must be named inside at least one test_*
        body in tests/test_si*.py.  A new public function without a test fails."""
        sources = _test_function_sources()
        assert len(sources) > 100, "test discovery broke"
        untested = [
            name
            for name in _public_members()
            if not any(re.search(rf"\b{re.escape(name)}\b", src) for src in sources)
        ]
        assert not untested, f"public callables never exercised by a test: {untested}"

    def test_public_surface_snapshot(self) -> None:
        """Explicit list so an accidental public addition/removal is visible in
        the diff (bump __version__ when this changes)."""
        assert sorted(_public_members()) == [
            "QuantityStatus",
            "QuaternionicQuantities",
            "ScaleFactors",
            "annotate_columns",
            "compute_quaternionic_quantities",
            "compute_scales",
            "convert_energy",
            "convert_energy_to_code",
            "convert_length_to_code",
            "convert_position",
            "convert_potential",
            "established_quantities",
            "provisional_quantities",
            "quantity_status",
        ]


# ===================================================================
# 3. Property tests: composition, frame change, dimensions
# ===================================================================


class TestPropertyComposition:
    """a->b->c == a->c, in IEEE 754 within a few ulp."""

    @given(U=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_potential_via_energy_equals_direct(
        self, U: float, m_si: float, lam_si: float
    ) -> None:
        """code potential -> J (convert_energy of U*V_Z) -> eV  ==  convert_potential."""
        sc = compute_scales(m_si, lam_si)
        via_energy = convert_energy(U * V_Z_CODE, sc) / EV_IN_JOULES
        assert convert_potential(U, sc) == pytest.approx(
            via_energy, rel=1e-14, abs=1e-300
        )

    @given(U=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_potential_round_trip_through_energy_inverse(
        self, U: float, m_si: float, lam_si: float
    ) -> None:
        """convert_potential has no dedicated inverse; its round-trip composes
        eV -> J -> code via convert_energy_to_code, then removes the Jacobian."""
        sc = compute_scales(m_si, lam_si)
        U_eV = convert_potential(U, sc)
        back = convert_energy_to_code(U_eV * EV_IN_JOULES, sc) / V_Z_CODE
        assert back == pytest.approx(U, rel=1e-13, abs=1e-300)

    @given(x=st_code_value, m1=st_mass, l1=st_wavelength, m2=st_mass, l2=st_wavelength)
    @settings(max_examples=200)
    def test_length_frame_change_is_L0_ratio(
        self, x: float, m1: float, l1: float, m2: float, l2: float
    ) -> None:
        """code(frame1) -> SI -> code(frame2) == x * L0_1 / L0_2."""
        s1, s2 = compute_scales(m1, l1), compute_scales(m2, l2)
        moved = convert_length_to_code(convert_position(x, s1), s2)
        assert moved == pytest.approx(x * s1.L0 / s2.L0, rel=1e-13, abs=1e-300)

    @given(E=st_code_value, m1=st_mass, l1=st_wavelength, m2=st_mass, l2=st_wavelength)
    @settings(max_examples=200)
    def test_energy_frame_change_is_E0_ratio(
        self, E: float, m1: float, l1: float, m2: float, l2: float
    ) -> None:
        s1, s2 = compute_scales(m1, l1), compute_scales(m2, l2)
        moved = convert_energy_to_code(convert_energy(E, s1), s2)
        assert moved == pytest.approx(E * s1.E0 / s2.E0, rel=1e-13, abs=1e-300)

    @given(
        val_m=st.floats(
            min_value=1e-15, max_value=1e-3, allow_nan=False, allow_infinity=False
        ),
        m_si=st_mass,
        lam_si=st_wavelength,
    )
    @settings(max_examples=200)
    def test_si_to_code_to_si_length(
        self, val_m: float, m_si: float, lam_si: float
    ) -> None:
        """SI->code->SI direction (the existing tests pin code->SI->code)."""
        sc = compute_scales(m_si, lam_si)
        assert convert_position(convert_length_to_code(val_m, sc), sc) == pytest.approx(
            val_m, rel=1e-14
        )

    @given(val_J=st_pos_si_energy, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_si_to_code_to_si_energy(
        self, val_J: float, m_si: float, lam_si: float
    ) -> None:
        sc = compute_scales(m_si, lam_si)
        assert convert_energy(convert_energy_to_code(val_J, sc), sc) == pytest.approx(
            val_J, rel=1e-14
        )


class TestPropertyDimensionalConsistency:
    """Dimensions tracked by ScaleFactors must close algebraically."""

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_action_scale_is_hbar(self, m_si: float, lam_si: float) -> None:
        """[E0]*[T0] = J*s must equal hbar_SI (action per code unit)."""
        sc = compute_scales(m_si, lam_si)
        assert sc.E0 * sc.T0 == pytest.approx(HBAR_SI, rel=1e-14)

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_velocity_scale_closes(self, m_si: float, lam_si: float) -> None:
        """[L0]/[T0] = m/s; v_z_si must be exactly V_Z_CODE of them."""
        sc = compute_scales(m_si, lam_si)
        assert sc.v_z_si == pytest.approx(V_Z_CODE * sc.L0 / sc.T0, rel=1e-13)

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_wavenumber_times_length_scale(self, m_si: float, lam_si: float) -> None:
        """[k_si]*[L0] is dimensionless and equals K0_CODE (k0 in code units)."""
        sc = compute_scales(m_si, lam_si)
        assert sc.k_si * sc.L0 == pytest.approx(K0_CODE, rel=1e-14)

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_kinetic_energy_closes(self, m_si: float, lam_si: float) -> None:
        """hbar^2 k^2 / (2m) in SI must equal E0 * (hbar_code^2 k0^2 / (2 m_code))."""
        sc = compute_scales(m_si, lam_si)
        E_kin_si = HBAR_SI**2 * sc.k_si**2 / (2 * m_si)
        E_kin_code = si.HBAR_CODE**2 * K0_CODE**2 / (2 * M_CODE)
        assert E_kin_si == pytest.approx(convert_energy(E_kin_code, sc), rel=1e-13)

    @given(U1=st_pos_si_energy, Ek=st_pos_si_energy, vg=st_velocity, a=st_factor)
    @settings(max_examples=200)
    def test_layer2_zeta_dimensionless_LQ_length(
        self, U1: float, Ek: float, vg: float, a: float
    ) -> None:
        """PROVISIONAL quantities still have to be dimensionally sane: zeta is
        invariant under a common energy rescale; L_Q scales as v_g/U1."""
        q = compute_quaternionic_quantities(U1, Ek, vg)
        q_scaled = compute_quaternionic_quantities(a * U1, a * Ek, vg)
        assert q_scaled.zeta == pytest.approx(q.zeta, rel=1e-13)
        assert q_scaled.L_Q == pytest.approx(q.L_Q / a, rel=1e-13)
        q_v = compute_quaternionic_quantities(U1, Ek, a * vg)
        assert q_v.L_Q == pytest.approx(a * q.L_Q, rel=1e-13)


# ===================================================================
# 4. Cross-language AC — Python side (pinned fixture)
# ===================================================================


def _call_vector(vec: dict) -> dict[str, float]:
    fn = getattr(si, vec["function"])
    if vec["function"] == "compute_scales":
        sc = fn(**vec["inputs"])
        return {k: getattr(sc, k) for k in vec["outputs"]}
    if vec["function"] == "compute_quaternionic_quantities":
        qq = fn(**vec["inputs"])
        return {k: getattr(qq, k) for k in vec["outputs"]}
    sc = compute_scales(**vec["scales_from"])
    (val,) = vec["inputs"].values()
    return {"output": fn(val, sc)}


@pytest.mark.skipif(
    not PY_FIXTURE.exists(), reason="run scripts/gen_si_conversion_vectors.py"
)
class TestPinnedVectorsPython:
    @pytest.fixture(autouse=True)
    def load(self) -> None:
        self.fx = json.loads(PY_FIXTURE.read_text())
        self.rtol = float(self.fx["tolerance_rel"])

    def test_fixture_metadata(self) -> None:
        assert self.fx["library_version"] == si.__version__
        assert "#354" in self.fx["lean_side"]
        assert self.rtol <= 1e-15

    def test_constants_reproduce(self) -> None:
        for c in self.fx["constants"]:
            assert getattr(si, c["name"]) == c["value"], c
            assert quantity_status(c["name"]).status == c["status"], c

    def test_every_vector_reproduces(self) -> None:
        assert len(self.fx["vectors"]) >= 20
        for vec in self.fx["vectors"]:
            got = _call_vector(vec)
            expected = vec["outputs"] if "outputs" in vec else {"output": vec["output"]}
            for k, e in expected.items():
                assert math.isclose(got[k], e, rel_tol=self.rtol), (
                    vec["function"],
                    k,
                    got[k],
                    e,
                )

    def test_vector_status_matches_registry(self) -> None:
        for vec in self.fx["vectors"]:
            assert vec["status"] == quantity_status(vec["function"]).status, vec[
                "function"
            ]

    def test_every_conversion_function_has_a_vector(self) -> None:
        funcs = {r.name for r in STATUS_REGISTRY if r.kind == "function"}
        pinned = {v["function"] for v in self.fx["vectors"]}
        assert (
            funcs <= pinned
        ), f"conversion functions without a pinned vector: {funcs - pinned}"

    def test_provisional_vectors_present_and_labelled(self) -> None:
        prov = [v for v in self.fx["vectors"] if v["status"] == PROVISIONAL]
        assert prov and all(
            v["function"] == "compute_quaternionic_quantities" for v in prov
        )

    def test_fixture_matches_generator(self) -> None:
        """The committed JSON is exactly what the generator emits today."""
        import importlib.util

        spec = importlib.util.spec_from_file_location(
            "gen_si_conversion_vectors",
            TESTS_DIR.parent / "scripts" / "gen_si_conversion_vectors.py",
        )
        assert spec and spec.loader
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        assert PY_FIXTURE.read_text() == mod.dumps(mod.build())

    @pytest.mark.skipif(not LEAN_FIXTURE.exists(), reason="Lean oracle vectors absent")
    def test_overlap_agrees_with_lean_oracle(self) -> None:
        """Where the Python pin and the Lean oracle share inputs, they must agree
        to 1e-15 relative.  This is the Python half of the cross-language AC."""
        lean = json.loads(LEAN_FIXTURE.read_text())
        checked = 0
        for particle in ("electron", "neutron"):
            lsf = next(e for e in lean["scale_factors"] if e["particle"] == particle)
            lrt = next(e for e in lean["round_trips"] if e["particle"] == particle)
            for vec in self.fx["vectors"]:
                if vec.get("particle") != particle:
                    continue
                f = vec["function"]
                if f == "compute_scales":
                    assert vec["inputs"]["m_si"] == pytest.approx(
                        float(lsf["mass_si"]), rel=1e-15
                    )
                    for k in ("L0", "E0", "T0", "v_z_si", "k_si"):
                        assert math.isclose(
                            vec["outputs"][k], float(lsf[k]), rel_tol=1e-15
                        ), (particle, k)
                        checked += 1
                elif f == "convert_position" and vec["inputs"]["x_code"] == float(
                    lrt["position_code"]
                ):
                    assert math.isclose(
                        vec["output"], float(lrt["position_si"]), rel_tol=1e-15
                    )
                    checked += 1
                elif f == "convert_energy" and vec["inputs"]["E_code"] == float(
                    lrt["energy_code"]
                ):
                    assert math.isclose(
                        vec["output"], float(lrt["energy_si"]), rel_tol=1e-15
                    )
                    checked += 1
                elif f == "convert_potential" and vec["inputs"]["U_code"] == float(
                    lrt["potential_code"]
                ):
                    assert math.isclose(
                        vec["output"], float(lrt["potential_eV"]), rel_tol=1e-15
                    )
                    checked += 1
        assert checked == 2 * (5 + 3), f"expected 16 overlap checks, did {checked}"
