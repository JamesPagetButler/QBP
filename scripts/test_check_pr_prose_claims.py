#!/usr/bin/env python3
"""Tests for scripts/check_pr_prose_claims.py (#507 §1 title lint + §2 oracle premise audit).

Run: python3 scripts/test_check_pr_prose_claims.py
"""

import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_pr_prose_claims as m  # noqa: E402

SCRIPT = os.path.join(HERE, "check_pr_prose_claims.py")


# ── §1 title lint ────────────────────────────────────────────────────────────
def test_verdict_word_on_theory_pr_without_headline_flags():
    f = m.lint_title(
        "[foundations] proves the Hurwitz bound",
        "## Summary\nstuff",
        {"tier-3-review"},
        [],
    )
    assert len(f) == 1 and "proves" in f[0], f


def test_verdict_word_with_verdict_headline_is_clean():
    body = "## Summary\n\n**Verdict:** PROVED as stated (Lean file:line)\n"
    assert m.lint_title("proves X", body, {"tier-3-review"}, []) == []


def test_three_way_table_counts_as_headline():
    body = "| Claim | Experimental evidence | QBP | PhysLean |\n|---|---|---|---|\n"
    assert m.lint_title("confirms X", body, set(), ["proofs/QBP/A.lean"]) == []


def test_non_theory_pr_not_linted():
    assert m.lint_title("proves nothing: fix CI", "", set(), ["scripts/x.py"]) == []


def test_theory_by_path_without_label():
    f = m.lint_title("establishes Y", "", set(), ["docs/foundations/y.md"])
    assert len(f) == 1, f


def test_neutral_title_clean():
    assert (
        m.lint_title(
            "[foundations] #589: retire the Hurwitz axiom", "", {"tier-3-review"}, []
        )
        == []
    )


# ── §2 oracle premise audit ──────────────────────────────────────────────────
def test_oracle_with_fixture_and_sha_is_clean():
    body = "- [x] Differential oracle run: tests/fixtures/oracle_predictions.json @ 1a2b3c4d — 0 FAIL rows\n"
    assert m.lint_oracle(body) == []


def test_oracle_missing_both_flags():
    body = "- [x] oracle run output attached in the comment below\n"
    f = m.lint_oracle(body)
    assert (
        len(f) == 1 and "fixture/config path" in f[0] and "pinned commit sha" in f[0]
    ), f


def test_oracle_missing_sha_only():
    body = "oracle report: tests/fixtures/pred.json\n"
    f = m.lint_oracle(body)
    assert (
        len(f) == 1
        and "pinned commit sha" in f[0]
        and "fixture/config path" not in f[0]
    ), f


def test_oracle_window_lookahead():
    body = "Oracle evidence: see the run below\n  fixture tests/fixtures/pred.json\n  pinned at deadbeef1\n"
    assert m.lint_oracle(body) == []


def test_struck_oracle_line_ignored():
    body = "- [ ] ~~Differential oracle (PhysLean↔QBP)~~ ⊘ N/A, no oracle-facing code\n"
    assert m.lint_oracle(body) == []


def test_oracle_mention_without_evidence_claim_ignored():
    body = "The oracle fixture format is documented in docs/x.md\n"
    assert m.lint_oracle(body) == []


# ── CLI ──────────────────────────────────────────────────────────────────────
def run_cli(title, body, labels="", changed="", strict=False):
    with tempfile.TemporaryDirectory() as d:
        bf = os.path.join(d, "body.md")
        cf = os.path.join(d, "changed.txt")
        open(bf, "w", encoding="utf-8").write(body)
        open(cf, "w", encoding="utf-8").write(changed)
        cmd = [
            sys.executable,
            SCRIPT,
            "--title",
            title,
            "--body-file",
            bf,
            "--labels",
            labels,
            "--changed-file",
            cf,
        ]
        if strict:
            cmd.append("--strict")
        r = subprocess.run(cmd, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr


def test_cli_advisory_exit_zero_with_findings():
    rc, out = run_cli("proves X", "oracle run output here\n", labels="tier-3-review")
    assert rc == 0, out
    assert out.count("::warning") == 2, out
    assert "ADVISORY" in out, out


def test_cli_strict_exit_one_with_findings():
    rc, out = run_cli("proves X", "", labels="tier-3-review", strict=True)
    assert rc == 1, out
    assert "::error" in out and "STRICT" in out, out


def test_cli_strict_clean_exit_zero():
    rc, out = run_cli("retire axiom", "", labels="tier-3-review", strict=True)
    assert rc == 0, out


# ── Red Team round 1 (PR #731) regression cases ───────────────────────────────
def test_url_ending_in_json_is_not_a_fixture_path():  # G9
    f = m.lint_oracle("oracle run: https://gist.github.com/x/pred.json @ 1a2b3c4d\n")
    assert len(f) == 1 and "fixture/config path" in f[0], f


def test_workflow_yml_token_is_not_a_fixture_path():  # G9 (how #731's own body passed)
    f = m.lint_oracle("oracle evidence in pr-process-lints.yml run 1a2b3c4d\n")
    assert len(f) == 1 and "fixture/config path" in f[0], f


def test_decimal_run_id_is_not_a_sha():  # G10
    f = m.lint_oracle("oracle run 39845576520 — tests/fixtures/pred.json\n")
    assert len(f) == 1 and "pinned commit sha" in f[0], f


def test_hex_word_is_not_a_sha():  # G10
    f = m.lint_oracle("oracle report deadbee — tests/fixtures/pred.json\n")
    assert len(f) == 1 and "pinned commit sha" in f[0], f


def test_real_sha_and_repo_path_pass():
    assert (
        m.lint_oracle("oracle run @ 38a193c against tests/fixtures/pred.json\n") == []
    )
    assert (
        m.lint_oracle("oracle output: analysis/543/report.json, pinned e6d00ffd2cf7\n")
        == []
    )


def test_verdict_bullet_form_counts_as_headline():  # G12
    assert (
        m.lint_title(
            "proves X", "- **Verdict:** PROVED as stated", {"tier-3-review"}, []
        )
        == []
    )


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failed = 0
    for t in tests:
        try:
            t()
            print(f"PASS {t.__name__}")
        except AssertionError as e:
            failed += 1
            print(f"FAIL {t.__name__}: {e}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    sys.exit(1 if failed else 0)
