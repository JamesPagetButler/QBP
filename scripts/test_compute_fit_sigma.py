"""Tests for scripts/compute_fit_sigma.py (QBP#809 phase 1, AC4).

Covers: the cap never RAISES (improves) status, only lowers/caps it; the exact
boundary behaviour at fit_sigma == 2 and fit_sigma == 5 (strictly greater-than, per
the issue's own ">5"/">2" wording); null handling (no usable error, and the
zero-denominator-with-nonzero-discrepancy undefined case); fit_history append-only
behaviour; and a mutant test proving a "cap that also raises status" bug would be
KILLED by these tests.

Run: python3 -m pytest scripts/test_compute_fit_sigma.py -v
     (or: python3 scripts/test_compute_fit_sigma.py)
"""

import importlib.util
import pathlib

_spec = importlib.util.spec_from_file_location(
    "compute_fit_sigma",
    pathlib.Path(__file__).resolve().parent / "compute_fit_sigma.py",
)
cfs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cfs)


# ---- sigma_meas_for ------------------------------------------------------------------


def test_sigma_meas_prefers_symmetric_measured_error():
    a = {"measured_error": 0.02, "measured_error_plus": 99, "measured_error_minus": 99}
    assert cfs.sigma_meas_for(a) == 0.02


def test_sigma_meas_asymmetric_pair_uses_facing_side_not_average():
    # T3 (qbp-oppenheimer, issuecomment-6886846959): the side FACING the prediction,
    # never the average. predicted > measured -> the discrepancy runs through the
    # upper error bar, so measured_error_plus is the right sigma, not (0.03+0.01)/2=0.02.
    a = {
        "predicted_value": 10.0,
        "measured_value": 9.0,
        "measured_error_plus": 0.03,
        "measured_error_minus": 0.01,
    }
    assert cfs.sigma_meas_for(a) == 0.03


def test_sigma_meas_asymmetric_pair_uses_minus_side_when_predicted_below_measured():
    a = {
        "predicted_value": 9.0,
        "measured_value": 10.0,
        "measured_error_plus": 0.03,
        "measured_error_minus": 0.01,
    }
    assert cfs.sigma_meas_for(a) == 0.01


def test_facing_side_vs_averaging_land_on_opposite_sides_of_a_cap_line():
    # T3's own request: a concrete case where the (wrong) average and the (correct)
    # facing-side convention disagree about which side of a cap boundary fit_sigma
    # lands on. predicted=12, measured=10: diff=2. Facing side (predicted>measured) is
    # measured_error_plus=0.9 -> fit_sigma=2/0.9=2.222 (> 2.0, WOULD cap to marginal).
    # The average of (0.9, 1.1) is 1.0 -> fit_sigma=2/1.0=2.0 (NOT > 2.0, no cap).
    a = {
        "predicted_value": 12.0,
        "measured_value": 10.0,
        "measured_error_plus": 0.9,
        "measured_error_minus": 1.1,
    }
    facing_sigma_meas = cfs.sigma_meas_for(a)
    assert facing_sigma_meas == 0.9
    average_sigma_meas = (0.9 + 1.1) / 2.0
    assert average_sigma_meas == 1.0

    facing_fit_sigma = cfs.raw_fit_sigma(12.0, 10.0, facing_sigma_meas)
    average_fit_sigma = cfs.raw_fit_sigma(12.0, 10.0, average_sigma_meas)
    assert round(facing_fit_sigma, 9) > cfs.FIT_SIGMA_MARGINAL_CAP  # 2.222... > 2.0
    assert round(average_fit_sigma, 9) == cfs.FIT_SIGMA_MARGINAL_CAP  # exactly 2.0

    assert cfs.capped_status("coherent", round(facing_fit_sigma, 9)) == "marginal"
    assert cfs.capped_status("coherent", round(average_fit_sigma, 9)) == "coherent"


def test_sigma_meas_none_when_asymmetric_pair_incomplete():
    assert cfs.sigma_meas_for({"measured_error_plus": 0.03}) is None
    assert cfs.sigma_meas_for({}) is None


def test_sigma_meas_rejects_bool_posing_as_number():
    # isinstance(True, int) is True in Python; measured_error: true must not be read as 1.
    assert cfs.sigma_meas_for({"measured_error": True}) is None


# ---- compute_fit_sigma_and_reason / raw_fit_sigma ------------------------------------


def test_fit_sigma_basic_value():
    a = {"predicted_value": 10.0, "measured_value": 9.0, "measured_error": 0.5}
    fs, reason = cfs.compute_fit_sigma_and_reason(a)
    assert fs == 2.0
    assert reason is None


def test_fit_sigma_null_when_no_usable_error():
    a = {"predicted_value": 10.0, "measured_value": 9.0}
    fs, reason = cfs.compute_fit_sigma_and_reason(a)
    assert fs is None
    assert reason is not None and "no usable measured" in reason


def test_fit_sigma_zero_denominator_zero_discrepancy_is_clean_zero():
    # predicted == measured, error == 0: fully consistent, fit_sigma is a clean 0.0 —
    # NOT the undefined case (e.g. MEAS-tolfac / FLAG-postd-IE class in the live ledger).
    a = {"predicted_value": 11.0, "measured_value": 11.0, "measured_error": 0.0}
    fs, reason = cfs.compute_fit_sigma_and_reason(a)
    assert fs == 0.0
    assert reason is None


def test_fit_sigma_zero_denominator_nonzero_discrepancy_is_undefined_null():
    # error == 0 but predicted != measured (e.g. FLAG-ngc2683-mass-discrepancy class):
    # division by zero with a real disagreement is undefined, not infinity, not zero.
    a = {"predicted_value": 145.2, "measured_value": 215.0, "measured_error": 0.0}
    fs, reason = cfs.compute_fit_sigma_and_reason(a)
    assert fs is None
    assert reason is not None and "zero denominator" in reason


def test_fit_sigma_rounds_away_float_noise_at_exact_boundary():
    # MEAS-alpha's real case: 128.05 - 127.95 computed in raw float64 is
    # 0.09999999999999432-ish, giving a ratio like 5.000000000000426 instead of the
    # mathematically exact 5.0 — rounding must land exactly on 5.0, not a hair over.
    a = {"predicted_value": 128.05, "measured_value": 127.95, "measured_error": 0.02}
    raw = cfs.raw_fit_sigma(128.05, 127.95, 0.02)
    assert (
        raw != 5.0
    )  # the float noise is real — this pins that the test fixture is honest
    fs, reason = cfs.compute_fit_sigma_and_reason(a)
    assert fs == 5.0
    assert reason is None


# ---- capped_status: never raises, exact boundaries ------------------------------------


def test_cap_never_raises_status_property_sample():
    """Property check over every (status, fit_sigma) pair in a representative grid:
    the result's severity is NEVER LOWER (better) than the input's severity."""
    fit_sigmas = [
        0.0,
        1.0,
        1.999999,
        2.0,
        2.0000001,
        3.0,
        4.999999,
        5.0,
        5.0000001,
        50.0,
        None,
    ]
    for status, sev in cfs.SEVERITY.items():
        for fs in fit_sigmas:
            new = cfs.capped_status(status, fs)
            assert cfs.SEVERITY[new] >= sev, (
                f"cap IMPROVED status: {status} (sev {sev}) + fit_sigma={fs} -> "
                f"{new} (sev {cfs.SEVERITY[new]})"
            )


def test_cap_never_raises_explicit_killed_case():
    # killed is maximally severe; a huge fit_sigma must never "improve" it to incoherent.
    assert cfs.capped_status("killed", 999.0) == "killed"


def test_cap_boundary_exactly_2_does_not_trigger_marginal():
    assert cfs.capped_status("coherent", 2.0) == "coherent"


def test_cap_boundary_just_above_2_triggers_marginal():
    assert cfs.capped_status("coherent", 2.0000001) == "marginal"


def test_cap_boundary_exactly_5_does_not_trigger_incoherent_only_marginal():
    # exactly 5.0: marginal cap fires (5.0 > 2.0) but NOT the incoherent cap (5.0 is not > 5.0).
    assert cfs.capped_status("coherent", 5.0) == "marginal"


def test_cap_boundary_just_above_5_triggers_incoherent():
    assert cfs.capped_status("coherent", 5.0000001) == "incoherent"


def test_cap_none_fit_sigma_never_changes_status():
    assert cfs.capped_status("coherent", None) == "coherent"


def test_cap_does_not_downgrade_an_already_worse_status():
    # fit_sigma says "at least marginal" but the anchor is already incoherent (worse) —
    # must stay incoherent, never be IMPROVED to marginal.
    assert cfs.capped_status("incoherent", 2.5) == "incoherent"


def test_cap_unknown_status_left_untouched_failsafe():
    assert (
        cfs.capped_status("some-future-enum-value", 999.0) == "some-future-enum-value"
    )


# ---- T2 (qbp-oppenheimer, issuecomment-6886846959): the four SEVERITY rulings --------


def test_t2_contested_is_never_capped_even_at_high_fit_sigma():
    # contested is a logical dispute state, not on the empirical scale (inter#238 R1) —
    # deliberately absent from SEVERITY, so it must be left untouched, never overwritten.
    assert cfs.capped_status("contested", 6.0) == "contested"
    assert "contested" not in cfs.SEVERITY


def test_t2_contested_still_reports_its_would_be_target():
    # target_cap_for is independent of whether the status is mapped — the report can
    # still say what contested WOULD be capped to, without actually capping it.
    assert cfs.target_cap_for(6.0) == "incoherent"
    assert cfs.target_cap_for(3.0) == "marginal"
    assert cfs.target_cap_for(1.0) is None
    assert cfs.target_cap_for(None) is None


def test_t2_untested_is_capped_to_marginal_above_the_line():
    # untested above marginal/incoherent: ACCEPT — a numeric measurement+error IS a
    # confrontation, so capping an untested anchor is a correct demotion, not a raise.
    assert cfs.capped_status("untested", 3.0) == "marginal"
    assert cfs.SEVERITY["marginal"] > cfs.SEVERITY["untested"]


def test_t2_refuted_is_never_capped_it_is_already_worse_than_incoherent():
    assert cfs.capped_status("refuted", 999.0) == "refuted"
    assert cfs.SEVERITY["refuted"] > cfs.SEVERITY["incoherent"]
    assert cfs.SEVERITY["refuted"] == cfs.SEVERITY["falsified"]  # the accepted tie


def test_t2_killed_is_never_capped_it_is_the_worst_grade():
    assert cfs.capped_status("killed", 999.0) == "killed"
    assert cfs.SEVERITY["killed"] == max(cfs.SEVERITY.values())


# ---- mutant test: a cap that ALSO raises status must be caught -----------------------


def _buggy_capped_status_that_also_raises(current_status, fit_sigma):
    """Deliberately buggy variant: sets status purely from fit_sigma, ignoring current
    severity — this WOULD un-kill a killed anchor or downgrade an incoherent one to
    marginal. This is exactly the regression class the issue requires a mutant test for.
    """
    if fit_sigma is None or current_status not in cfs.SEVERITY:
        return current_status
    if fit_sigma > cfs.FIT_SIGMA_INCOHERENT_CAP:
        return "incoherent"  # unconditional — no "only if worse" guard
    if fit_sigma > cfs.FIT_SIGMA_MARGINAL_CAP:
        return "marginal"  # unconditional — no "only if worse" guard
    return current_status


def test_mutant_cap_that_also_raises_is_killed_by_the_never_improves_test():
    # A killed anchor re-evaluated at a middling fit_sigma: correct code leaves it
    # killed; the buggy "always set from fit_sigma" variant improves it to marginal —
    # a real violation of "the cap never raises a status".
    correct = cfs.capped_status("killed", 3.0)
    buggy = _buggy_capped_status_that_also_raises("killed", 3.0)
    assert correct == "killed"
    assert buggy == "marginal"
    assert correct != buggy, "the mutant must diverge from correct behaviour here"

    # And the buggy variant fails the exact severity-never-decreases property the real
    # function is tested against above.
    assert cfs.SEVERITY[buggy] < cfs.SEVERITY["killed"]  # the bug: severity DECREASED
    assert cfs.SEVERITY[correct] >= cfs.SEVERITY["killed"]  # correct: never decreases


# ---- fit_history append-only -----------------------------------------------------------


def test_append_fit_history_extends_not_replaces():
    a = {"id": "X", "fit_history": [{"date": "d0", "fit_sigma": 1.0}]}
    entry = {"date": "d1", "fit_sigma": 2.0}
    new_history = cfs.append_fit_history(a, entry)
    assert new_history == [
        {"date": "d0", "fit_sigma": 1.0},
        {"date": "d1", "fit_sigma": 2.0},
    ]
    # the OLD list object on the anchor is untouched (no in-place mutation of the original)
    assert a["fit_history"] == [{"date": "d0", "fit_sigma": 1.0}]


def test_append_fit_history_from_absent():
    a = {"id": "X"}
    new_history = cfs.append_fit_history(a, {"date": "d0", "fit_sigma": 1.0})
    assert new_history == [{"date": "d0", "fit_sigma": 1.0}]


def test_append_fit_history_refuses_non_list():
    a = {"id": "X", "fit_history": "not-a-list"}
    try:
        cfs.append_fit_history(a, {"date": "d0", "fit_sigma": 1.0})
        assert False, "expected TypeError"
    except TypeError as e:
        assert "not a list" in str(e)


def test_mutant_fit_history_overwrite_loses_prior_entries():
    """Mutant test: a buggy encoder that ASSIGNS fit_history = [entry] instead of
    appending silently drops every prior evaluation — exactly the regression
    append_fit_history exists to prevent."""
    a = {
        "id": "X",
        "fit_history": [
            {"date": "d0", "fit_sigma": 1.0},
            {"date": "d1", "fit_sigma": 1.5},
        ],
    }
    entry = {"date": "d2", "fit_sigma": 2.0}

    correct = cfs.append_fit_history(a, entry)
    assert len(correct) == 3  # two prior + the new one

    buggy = [entry]  # the overwrite bug, inline
    assert len(buggy) == 1
    assert correct != buggy
    assert len(correct) != len(buggy), "the mutant must diverge: it loses prior entries"


# ---- is_candidate: only anchors with BOTH numeric fields are touched -----------------


def test_is_candidate_requires_both_numeric_fields():
    assert cfs.is_candidate({"predicted_value": 1.0, "measured_value": 2.0})
    assert not cfs.is_candidate({"predicted_value": 1.0})
    assert not cfs.is_candidate({"measured_value": 2.0})
    assert not cfs.is_candidate({})


def test_is_candidate_rejects_bool_and_non_numeric():
    assert not cfs.is_candidate({"predicted_value": True, "measured_value": 2.0})
    assert not cfs.is_candidate({"predicted_value": "1.0", "measured_value": 2.0})


# ---- prediction_source: best-effort provenance pointer -------------------------------


def test_prediction_source_prefers_theory_citation():
    a = {"theory_citation": "Someone 2020", "foundation_batch": "#466"}
    assert cfs.prediction_source(a) == "theory_citation:Someone 2020"


def test_prediction_source_falls_back_to_unresolved():
    assert cfs.prediction_source({}) == cfs._UNRESOLVED_SOURCE


if __name__ == "__main__":
    import sys

    failures = 0
    for name, fn in sorted(vars().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as e:
                failures += 1
                print(f"FAIL {name}: {e}")
    sys.exit(1 if failures else 0)
