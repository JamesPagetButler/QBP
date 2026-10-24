#!/usr/bin/env python3
"""Tests for the Prediction-Classification gate (scripts/check_prediction_classification.py, #736).

Per docs/cth/proof-anchor-best-practices.md ("a gate is judged by what it catches"),
the centrepiece is a set of ADVERSARIAL docs — missing section, heading at the wrong
level, template pasted inside a code fence, Type cell outside {Validation, Novel,
OPEN}, no Type column — each of which the gate must FAIL. A clean doc and the real
`research/` tree must PASS.

Each case writes synthetic docs into a tempdir and runs the real checker via
`--research-dir`. Run: python3 scripts/test_check_prediction_classification.py
(also pytest-collectible: `python3 -m pytest scripts/test_check_prediction_classification.py`).
"""

import importlib.util
import os
import subprocess
import sys
import tempfile
from typing import Dict

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_prediction_classification.py")
REAL_RESEARCH = os.path.join(os.path.dirname(HERE), "research")


def _check(cond, msg):
    """`assert` that survives `python3 -O`."""
    if not cond:
        raise AssertionError(msg)


def _load_checker():
    spec = importlib.util.spec_from_file_location(
        "check_prediction_classification", SCRIPT
    )
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CLEAN_DOC = """# Expected Results for X

## 1. The Phenomenon

Some text with a | pipe that is not a table.

## 5. Prediction Classification

| Prediction | Type | Standard value | Notes |
|------------|------|----------------|-------|
| P(+) = 0.5 | Validation | 0.5 | "identical to QM" (§3) |
| Decay rate κ = \\|U₁\\|/(ℏv) | Novel | n/a | "κ = \\|U₁\\|/(ℏv)" (§4) |
| Lamb shift ≈ 1057 MHz | OPEN | 1057 MHz | no QBP derivation in this doc |

### Classification Summary

**Validation:** ...

## 6. Acceptance Criteria
"""

UNNUMBERED_HEADING_DOC = CLEAN_DOC.replace(
    "## 5. Prediction Classification", "## Prediction Classification"
)

# --- adversarial docs: each must FAIL ---------------------------------------
NO_SECTION_DOC = "# Expected Results for Y\n\n## 1. The Phenomenon\n\nText.\n"

LEVEL3_HEADING_DOC = CLEAN_DOC.replace(
    "## 5. Prediction Classification", "### 5. Prediction Classification"
)

FENCED_TEMPLATE_DOC = """# Expected Results for Z

## 5. Prediction Classification

Template copied from the schema, never filled in:

```markdown
| Prediction | Type | Standard QM | Notes |
|------------|------|-------------|-------|
| P(+) = cos²(θ/2) | Validation | cos²(θ/2) | Identical to QM |
```
"""

BAD_CELL_DOC = CLEAN_DOC.replace("| Novel |", "| Unknown |")
LOWERCASE_CELL_DOC = CLEAN_DOC.replace("| Validation |", "| validation |")
SUFFIXED_OPEN_DOC = CLEAN_DOC.replace("| OPEN |", "| OPEN — not decidable |")
BOLD_CELL_DOC = CLEAN_DOC.replace("| Validation |", "| **Validation** |")

NO_TYPE_COLUMN_DOC = CLEAN_DOC.replace(
    "| Prediction | Type |", "| Prediction | Kind |"
).replace("|------------|------|", "|------------|------|")

HEADER_ONLY_DOC = """# Expected Results for W

## 5. Prediction Classification

| Prediction | Type | Standard value | Notes |
|------------|------|----------------|-------|

### Classification Summary
"""

NO_TABLE_DOC = """# Expected Results for V

## 5. Prediction Classification

Prose only; the table was never written.

## 6. Next
"""


def _run(files: Dict[str, str], *extra):
    """Write `files` into <tmp>/research and run the checker on it."""
    with tempfile.TemporaryDirectory() as tmp:
        rdir = os.path.join(tmp, "research")
        os.makedirs(rdir)
        for name, text in files.items():
            with open(os.path.join(rdir, name), "w", encoding="utf-8") as fh:
                fh.write(text)
        proc = subprocess.run(
            [sys.executable, SCRIPT, "--research-dir", rdir, *extra],
            capture_output=True,
            text=True,
        )
        return proc.returncode, proc.stdout, proc.stderr


def test_clean_doc_passes():
    rc, out, err = _run({"01_x_expected_results.md": CLEAN_DOC})
    _check(rc == 0, f"clean doc must pass: rc={rc}\n{out}\n{err}")
    _check("1/1 docs" in out, out)


def test_unnumbered_heading_passes():
    rc, out, _ = _run({"01_x_expected_results.md": UNNUMBERED_HEADING_DOC})
    _check(rc == 0, f"`## Prediction Classification` without a number must pass\n{out}")


def test_non_expected_results_files_are_ignored():
    """Only *_expected_results.md is gated; a derivation doc without the section is fine."""
    rc, out, _ = _run(
        {
            "01_x_expected_results.md": CLEAN_DOC,
            "07_particle_statistics_derivation.md": NO_SECTION_DOC,
            "README.md": "# research\n",
        }
    )
    _check(rc == 0, f"non-gated files must be ignored\n{out}")
    _check("1/1 docs" in out, out)


def test_adversarial_docs_fail():
    """The gate is judged by what it catches: each planted defect must FAIL alone."""
    cases = {
        "no_section": NO_SECTION_DOC,
        "level3_heading": LEVEL3_HEADING_DOC,
        "fenced_template": FENCED_TEMPLATE_DOC,
        "bad_cell": BAD_CELL_DOC,
        "lowercase_cell": LOWERCASE_CELL_DOC,
        "suffixed_open": SUFFIXED_OPEN_DOC,
        "bold_cell": BOLD_CELL_DOC,
        "no_type_column": NO_TYPE_COLUMN_DOC,
        "header_only": HEADER_ONLY_DOC,
        "no_table": NO_TABLE_DOC,
    }
    for label, text in cases.items():
        rc, out, _ = _run({"02_y_expected_results.md": text})
        _check(rc != 0, f"adversarial case {label!r} must FAIL but passed:\n{out}")
        _check("FAIL" in out and "02_y_expected_results.md" in out, f"{label}: {out}")


def test_one_bad_doc_fails_the_set_and_names_it():
    rc, out, _ = _run(
        {
            "01_x_expected_results.md": CLEAN_DOC,
            "02_y_expected_results.md": BAD_CELL_DOC,
        }
    )
    _check(rc != 0, out)
    _check("FAIL  " in out and "02_y_expected_results.md" in out, out)
    _check(
        "01_x_expected_results.md" not in out,
        f"passing doc must not be listed without --list\n{out}",
    )
    _check("1/2 docs" in out, out)


def test_list_prints_every_file():
    rc, out, _ = _run(
        {
            "01_x_expected_results.md": CLEAN_DOC,
            "02_y_expected_results.md": NO_SECTION_DOC,
        },
        "--list",
    )
    _check(rc != 0, out)
    _check("OK    " in out and "01_x_expected_results.md" in out, out)
    _check("FAIL  " in out and "02_y_expected_results.md" in out, out)


def test_empty_dir_fails():
    """No docs found is an error, not a vacuous pass (a wrong --research-dir must not go green)."""
    rc, _, err = _run({})
    _check(rc != 0, "empty research dir must fail")
    _check("no *_expected_results.md" in err, err)


def test_check_text_unit():
    mod = _load_checker()
    _check(mod.check_text(CLEAN_DOC) == [], mod.check_text(CLEAN_DOC))
    probs = mod.check_text(BAD_CELL_DOC)
    _check(len(probs) == 1 and "'Unknown'" in probs[0], probs)
    probs = mod.check_text(NO_SECTION_DOC)
    _check(probs and "heading" in probs[0], probs)
    _check(mod.split_cells("| a | b |") == ["a", "b"], "split_cells outer pipes")
    _check(mod.split_cells("a | b") == ["a", "b"], "split_cells no outer pipes")
    # GFM: `\|` inside a cell is a literal pipe, not a column break (03 §7 row 6).
    _check(
        mod.split_cells("| κ = \\|U₁\\|/(ℏv) | Novel |") == ["κ = |U₁|/(ℏv)", "Novel"],
        "escaped pipes must stay inside the cell",
    )


def test_real_research_tree_passes():
    """Regression anchor for #736: every committed ground-truth doc carries the section."""
    proc = subprocess.run(
        [sys.executable, SCRIPT, "--research-dir", REAL_RESEARCH, "--list"],
        capture_output=True,
        text=True,
    )
    _check(
        proc.returncode == 0,
        f"real research/ tree must pass:\n{proc.stdout}\n{proc.stderr}",
    )
    _check("FAIL" not in proc.stdout, proc.stdout)


def main() -> int:
    tests = [
        (name, fn)
        for name, fn in sorted(globals().items())
        if name.startswith("test_") and callable(fn)
    ]
    failed = 0
    for name, fn in tests:
        try:
            fn()
            print(f"PASS  {name}")
        except Exception as exc:  # noqa: BLE001 — report every failure, keep going
            failed += 1
            print(f"FAIL  {name}: {exc}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
