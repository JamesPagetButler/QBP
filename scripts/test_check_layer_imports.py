#!/usr/bin/env python3
"""Tests for the layer-import linter (scripts/check_layer_imports.py).

Focus: Rule 5 — BUILD-VISIBILITY. A .lean under a physics/Sprint12 dir that is
reachable from no `@[default_target]` root is not compiled by CI's bare `lake
build`, so a broken proof in it rides CI-green (the General3D.lean class,
#625/#619). "Reachable via a non-default target" (a lean_exe) is NOT enough — CI
does not build the exes (#646). The gate must flag such files, unless they are
listed in the shrink-only, issue-linked quarantine.

Per the gate-validation discipline in docs/cth/proof-anchor-best-practices.md ("a
gate is judged by what it catches"), the centrepiece is an ADVERSARIAL test that
plants a build-invisible physics file and asserts the gate catches it (#625 AC2).

Each case builds a minimal synthetic proofs/ tree in a tempdir and runs the real
checker via `--proofs`. Run: python3 scripts/test_check_layer_imports.py
(also pytest-collectible: `python3 -m pytest scripts/test_check_layer_imports.py`).

#502 (PR #497 Tier-3 Red Team F4): `IMPORT_RE` used to run on raw text, so an
`import QBP.Physics.X` at column 0 INSIDE a `/- ... -/` or `-- ...` comment counted
as a real import (rule 1/2 false positive) and fed the build-visibility closure
(rule 5 false "visible"). `test_comment_embedded_imports` is the regression test.
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_layer_imports.py")


def _check(cond, msg):
    """`assert` that survives `python3 -O` (CI runs without -O, but be safe)."""
    if not cond:
        raise AssertionError(msg)


def _load_checker():
    """Import check_layer_imports.py as a module (it is a script, not a package)."""
    spec = importlib.util.spec_from_file_location("check_layer_imports", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# A minimal, fully-clean proofs tree: passes rules 1–5.
#   - QBP lib (@[default_target]) root QBP.lean imports Foundations + one Experiments file.
#   - Sprint12 lib (@[default_target], its own srcDir) with one root file.
# No exe here — exe (non-default) behaviour is exercised in dedicated cases below.
BASE_FILES = {
    "lakefile.lean": (
        "import Lake\n"
        "open Lake DSL\n\n"
        "package «T» where\n\n"
        "@[default_target]\n"
        "lean_lib «QBP» where\n"
        "  roots := #[`QBP]\n\n"
        "@[default_target]\n"
        "lean_lib «QBPSprint12» where\n"
        '  srcDir := "Sprint12-Inherited"\n'
        "  roots := #[`S1]\n"
    ),
    "QBP.lean": "import QBP.Foundations\nimport QBP.Experiments.Exp1\n",
    "QBP/Foundations.lean": "import QBP.Foundations.F1\n",
    "QBP/Foundations/F1.lean": "-- foundations leaf\n",
    "QBP/Experiments/Exp1.lean": "-- physics leaf, visible via QBP.lean\n",
    "Sprint12-Inherited/S1.lean": "-- Sprint12 lib root, visible\n",
}

# A non-default `lean_exe` reaching an Oracle corpus (mirrors the real oracle exe).
NONDEFAULT_EXE = "\nlean_exe «oracle» where\n  root := `QBP.Oracle.Main\n"
ORACLE_FILES = {
    "QBP/Oracle/Main.lean": "import QBP.Oracle.Compute\n-- exe root\n",
    "QBP/Oracle/Compute.lean": "-- reached only via the exe root\n",
}


def run(files):
    """Write `files` under a temp proofs/ and return (returncode, stdout)."""
    with tempfile.TemporaryDirectory() as d:
        proofs = os.path.join(d, "proofs")
        for rel, content in files.items():
            p = os.path.join(proofs, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(content)
        res = subprocess.run(
            [sys.executable, SCRIPT, "--proofs", proofs],
            capture_output=True,
            text=True,
        )
        return res.returncode, res.stdout


def with_quarantine(files, entries):
    files = dict(files)
    files["QBP/.build-visibility-quarantine.json"] = json.dumps({"entries": entries})
    return files


def main():
    passed = 0

    def check(name, cond):
        nonlocal passed
        assert cond, f"FAILED: {name}"
        passed += 1

    # 0. Baseline: the clean synthetic tree passes all rules.
    rc, out = run(BASE_FILES)
    check("clean tree passes", rc == 0)

    # 1. ADVERSARIAL (#625 AC2): a planted, unreferenced physics file is flagged.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Orphan.lean"] = "-- not imported by anything\n"
    rc, out = run(files)
    check("planted invisible physics file fails", rc == 1)
    check("planted file named in the violation", "QBP/Experiments/Orphan.lean" in out)
    check("violation explains build-invisibility", "build-invisible" in out)

    # 2. Sprint12 coverage (#625 AC1): a non-root, unreferenced Sprint12 file is flagged.
    files = dict(BASE_FILES)
    files["Sprint12-Inherited/Orphan.lean"] = "-- not a lib root, imported by nothing\n"
    rc, out = run(files)
    check("planted invisible Sprint12 file fails", rc == 1)
    check("Sprint12 orphan named", "Sprint12-Inherited/Orphan.lean" in out)

    # 3. Transitive visibility: a physics file reached only via another visible
    #    physics file (not directly by QBP.lean) is visible — guards against a
    #    naive direct-import-only check.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Exp1.lean"] = "import QBP.Experiments.Exp2\n"
    files["QBP/Experiments/Exp2.lean"] = "-- reached transitively via Exp1\n"
    rc, out = run(files)
    check("transitively-reachable physics file passes", rc == 0)

    # 4. A file reachable ONLY via a NON-default target (lean_exe) is invisible to CI
    #    (bare `lake build` skips the exes) and must be flagged — the #646 class.
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"] + NONDEFAULT_EXE
    files.update(ORACLE_FILES)
    rc, out = run(files)
    check("exe-only (non-default) file is flagged as invisible", rc == 1)
    check("exe-only file named", "QBP/Oracle/Main.lean" in out)

    # 5. Same corpus, but the exe carries @[default_target] → CI builds it → visible.
    #    Proves the visibility hinges on the @[default_target] attribute, not on
    #    being a declared target.
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"] + (
        "\n@[default_target]\nlean_exe «oracle» where\n  root := `QBP.Oracle.Main\n"
    )
    files.update(ORACLE_FILES)
    rc, out = run(files)
    check("default_target exe makes its corpus visible", rc == 0)

    # 5b. A COMMENTED-OUT @[default_target] must NOT mark the target default
    #     (Gemini #645 false-positive concern): the exe corpus stays invisible.
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"] + (
        "\n-- @[default_target]\nlean_exe «oracle» where\n  root := `QBP.Oracle.Main\n"
    )
    files.update(ORACLE_FILES)
    rc, out = run(files)
    check("commented-out @[default_target] does not count", rc == 1)

    # 5c. Valid Lean ordering (docstring, then attribute, then decl) + blank lines
    #     must not break detection: the exe corpus is visible.
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"] + (
        "\n/-- the oracle exe -/\n@[default_target]\n\n"
        "lean_exe «oracle» where\n  root := `QBP.Oracle.Main\n"
    )
    files.update(ORACLE_FILES)
    rc, out = run(files)
    check("docstring-above-attr + blank line does not break detection", rc == 0)

    # 6. Quarantine lets a known-invisible file pass (with issue + reason).
    files = dict(BASE_FILES)
    files["lakefile.lean"] = files["lakefile.lean"] + NONDEFAULT_EXE
    files.update(ORACLE_FILES)
    files = with_quarantine(
        files,
        [
            {"file": "QBP/Oracle/Main.lean", "reason": "exe-only", "issue": "#646"},
            {"file": "QBP/Oracle/Compute.lean", "reason": "exe-only", "issue": "#646"},
        ],
    )
    rc, out = run(files)
    check("quarantined invisible files pass", rc == 0)

    # 7. A quarantine entry with no issue is rejected (no silent baselining).
    files = dict(BASE_FILES)
    files["QBP/Experiments/Orphan.lean"] = "-- intentionally unwired\n"
    files = with_quarantine(
        files, [{"file": "QBP/Experiments/Orphan.lean", "reason": "tracked"}]
    )
    rc, out = run(files)
    check("quarantine entry with no issue fails", rc == 1)
    check("no-issue violation explained", "no 'issue'" in out)

    # 8. Stale quarantine: a listed file that is actually build-visible must be removed.
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Experiments/Exp1.lean", "reason": "stale", "issue": "#646"}],
    )
    rc, out = run(files)
    check("stale (now-visible) quarantine entry fails", rc == 1)
    check("stale-visible violation explained", "stale quarantine entry" in out)

    # 9. Stale quarantine: a listed file that no longer exists must be removed.
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Experiments/Gone.lean", "reason": "deleted", "issue": "#646"}],
    )
    rc, out = run(files)
    check("stale (missing-file) quarantine entry fails", rc == 1)
    check("missing-file violation explained", "does not exist" in out)

    # 10. Quarantine may only govern the enforced tree (not e.g. Foundations).
    files = with_quarantine(
        BASE_FILES,
        [{"file": "QBP/Foundations/F1.lean", "reason": "wrong scope", "issue": "#646"}],
    )
    rc, out = run(files)
    check("quarantine outside enforced dir fails", rc == 1)
    check("out-of-scope violation explained", "not under an enforced dir" in out)

    # 11. Rule-2 regression: a physics file importing QBP.Substrate is still caught.
    files = dict(BASE_FILES)
    files["QBP/Experiments/Exp1.lean"] = "import QBP.Substrate.AC1\n"
    rc, out = run(files)
    check("physics importing Substrate fails", rc == 1)
    check("forbidden-import violation explained", "forbidden" in out)

    # 12. #502 regression: comment-embedded imports are not imports.
    passed += _comment_embedded_import_cases()
    passed += _strip_comments_unit_cases()

    print(f"check_layer_imports: {passed} tests passed")
    return 0


# A Foundations file whose only `import QBP.Physics...` / `import QBP.Substrate...`
# lines sit at column 0 INSIDE comments: a one-line block comment, a NESTED
# multi-line block comment, a `/-!` module docstring, and a `--` line comment.
# None of these is an import; the file is clean under rule 1.
COMMENTED_FOUNDATIONS_FILE = (
    "/- import QBP.Physics.OneLine -/\n"
    "/-! Module header. The following is what a Foundations file must NOT do:\n"
    "import QBP.Physics.InModuleDoc\n"
    "-/\n"
    "/- outer comment\n"
    "  /- nested comment, still inside the outer one\n"
    "import QBP.Substrate.Nested\n"
    "  -/ the inner comment is closed; the outer one continues -- still here\n"
    "import QBP.Physics.StillInsideOuter\n"
    "-/\n"
    "-- import QBP.Physics.LineComment\n"
    "theorem foundations_leaf : True := trivial\n"
)


def test_comment_embedded_imports() -> None:
    """pytest entry point for the #502 regression (CI runs `main()` directly)."""
    _comment_embedded_import_cases()


def test_strip_comments_unit() -> None:
    """pytest entry point for the `strip_comments` unit checks."""
    _strip_comments_unit_cases()


def _comment_embedded_import_cases() -> int:
    """#502 AC2: comment-embedded forbidden imports must NOT trigger; real ones must."""
    n = 0

    # (a) Only comment-embedded forbidden imports → rule 1 does NOT fire.
    files = dict(BASE_FILES)
    files["QBP/Foundations/F1.lean"] = COMMENTED_FOUNDATIONS_FILE
    rc, out = run(files)
    _check(rc == 0, f"comment-embedded imports counted as imports:\n{out}")
    n += 1

    # (b) The SAME file plus REAL forbidden imports in every shape Lean accepts
    #     (column 0; indented; after a same-line block comment; on the line that
    #     closes a block comment — PR #719 Red Team K1, verified against lean
    #     v4.30.0) → rule 1 fires on exactly the real ones, proving the stripper
    #     does not eat genuine import lines and the anchor is whitespace-tolerant.
    files = dict(BASE_FILES)
    files["QBP/Foundations/F1.lean"] = COMMENTED_FOUNDATIONS_FILE + (
        "import QBP.Physics.RealImport\n"
        "  import QBP.Physics.IndentedImport\n"
        "/- c -/ import QBP.Physics.AfterInlineComment\n"
        "/- opens here\n"
        "-/ import QBP.Physics.OnClosingLine\n"
    )
    rc, out = run(files)
    _check(rc == 1, "real forbidden imports after comments were not caught")
    for real in (
        "QBP.Physics.RealImport",
        "QBP.Physics.IndentedImport",
        "QBP.Physics.AfterInlineComment",
        "QBP.Physics.OnClosingLine",
    ):
        _check(real in out, f"real import {real} not reported:\n{out}")
    for ghost in (
        "OneLine",
        "InModuleDoc",
        "Nested",
        "StillInsideOuter",
        "LineComment",
    ):
        _check(ghost not in out, f"comment-embedded import {ghost} reported:\n{out}")
    n += 1

    # (b2) Rule 5 side of K1: a physics file reached only through an INDENTED or
    #      inline-comment-prefixed import in the default root is build-visible
    #      (lake follows it), so it must NOT be flagged.
    files = dict(BASE_FILES)
    files["QBP.lean"] = (
        "import QBP.Foundations\n"
        "  import QBP.Experiments.Exp1\n"
        "/- c -/ import QBP.Experiments.Exp2\n"
    )
    files["QBP/Experiments/Exp2.lean"] = (
        "-- reached via an inline-comment-prefixed import\n"
    )
    rc, out = run(files)
    _check(rc == 0, f"indented / inline-comment-prefixed imports not followed:\n{out}")
    n += 1

    # (c) Rule 5: a physics file reached ONLY through a commented-out import in the
    #     default root is build-INVISIBLE (lake does not follow comments) and must
    #     be flagged — the stripped text, not the raw text, feeds the closure.
    files = dict(BASE_FILES)
    files["QBP.lean"] = (
        "import QBP.Foundations\n"
        "import QBP.Experiments.Exp1\n"
        "-- import QBP.Experiments.Ghost\n"
        "/- import QBP.Experiments.Ghost -/\n"
    )
    files["QBP/Experiments/Ghost.lean"] = "-- reachable only via commented imports\n"
    rc, out = run(files)
    _check(rc == 1, "comment-only-reachable physics file passed as visible")
    _check("QBP/Experiments/Ghost.lean" in out and "build-invisible" in out, out)
    n += 1

    # (d) Rule 3: a Foundations module named only by a commented-out aggregator
    #     import is NOT imported → build-invisibility is reported.
    files = dict(BASE_FILES)
    files["QBP/Foundations.lean"] = (
        "import QBP.Foundations.F1\n-- import QBP.Foundations.F2\n"
    )
    files["QBP/Foundations/F2.lean"] = "-- named only in a comment\n"
    rc, out = run(files)
    _check(rc == 1, "comment-only aggregator import counted as an import")
    _check("QBP/Foundations/F2.lean" in out, out)
    n += 1

    # (e) The quarantine table lives INSIDE the aggregator's comment block and
    #     must still be read (it is parsed from raw, not stripped, text).
    files = dict(BASE_FILES)
    files["QBP/Foundations.lean"] = (
        "import QBP.Foundations.F1\n"
        "/-! Quarantine (build-invisibility, tracked):\n"
        "| `QBP.Foundations.F2` | #000 | reason |\n"
        "-/\n"
    )
    files["QBP/Foundations/F2.lean"] = "-- quarantined via the comment table\n"
    rc, out = run(files)
    _check(rc == 0, f"quarantine table inside comment block not honoured:\n{out}")
    n += 1
    return n


def _strip_comments_unit_cases() -> int:
    """Direct checks on `strip_comments`: nesting, newline alignment, real lines kept."""
    mod = _load_checker()
    strip = mod.strip_comments
    n = 0

    src = "import A\n/- x /- y -/ z\nimport B\n-/\nimport C -- trailing\n-- import D\n"
    out = strip(src)
    _check(out.count("\n") == src.count("\n"), "newlines must be preserved")
    _check(len(out) == len(src), "stripping must be length-preserving (column-aligned)")
    _check(mod.IMPORT_RE.findall(out) == ["A", "C"], mod.IMPORT_RE.findall(out))
    n += 1

    # `/-` inside a line comment does not open a block; the next line is code.
    _check(
        mod.imports_of_text("-- /- not a block\nimport E\n") == ["E"],
        "`/-` inside a line comment must not open a block",
    )
    n += 1
    # `--` inside a block comment does not end the block early.
    _check(
        mod.imports_of_text("/- a -- b\nimport F\n-/\nimport G\n") == ["G"],
        "`--` inside a block comment must not close it",
    )
    n += 1
    # Unterminated block comment swallows the rest, as Lean would.
    _check(
        mod.imports_of_text("/- open\nimport H\n") == [],
        "unterminated block comment must swallow the rest",
    )
    n += 1
    # K1 (PR #719): Lean accepts an indented import and an import after a same-line
    # block comment; both are real imports on stripped text.
    _check(
        mod.imports_of_text("  import I\n/- c -/ import J\n/- o\n-/ import K\n")
        == ["I", "J", "K"],
        "indented / inline-comment-prefixed imports must be detected",
    )
    n += 1
    # Real-world shape: module docstring then imports (the Foundations norm).
    _check(
        mod.imports_of_text(
            "/-!\n# Title\nimport QBP.Physics.Quoted is forbidden here\n-/\nimport Mathlib.Algebra.Ring.Basic\nimport QBP.Foundations.CDAlg\n"
        )
        == ["Mathlib.Algebra.Ring.Basic", "QBP.Foundations.CDAlg"],
        "module docstring then imports",
    )
    n += 1
    return n


if __name__ == "__main__":
    sys.exit(main())
