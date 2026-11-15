#!/usr/bin/env python3
"""Tests for scripts/pr_merge_blocking_boxes.py (#507 §4/§7, §2.2 contract).

Run: python3 scripts/test_pr_merge_blocking_boxes.py
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pr_merge_blocking_boxes as m  # noqa: E402

SCRIPT = os.path.join(HERE, "pr_merge_blocking_boxes.py")


def test_canonical_s22_block():
    body = """## §I4 review
Sign-off required (merge-blocking):
- [ ] @qbp-architecture — coherence
- [x] @cth-implementor — eval-side
Informational readers (non-blocking):
- [ ] @qbp-oppenheimer — theory shape
"""
    r = m.parse(body)
    assert r["unticked"] == ["@qbp-architecture — coherence"], r
    assert r["ticked"] == ["@cth-implementor — eval-side"], r


def test_sentinel_region_and_close():
    body = """Reviewers
<!-- merge-blocking -->
- [ ] @a sign
- [x] @b sign
<!-- /merge-blocking -->
- [ ] informational thing
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a sign"], r
    assert r["ticked"] == ["@b sign"], r


def test_heading_ends_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a

## Test Plan
- [ ] Formal proofs pass
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_blank_then_prose_ends_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a

Some prose paragraph here.
- [ ] not counted: outside the region
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_nil_boxes_not_counted_as_unticked():
    body = """Sign-off required (merge-blocking):
- [ ] ~~schema-axis co-sign~~ ⊘ n/a
- [ ] ⊘ two-axis
- [ ] @a real one
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a real one"], r
    assert len(r["nil"]) == 2, r


def test_outside_region_ignored():
    body = """## Verification
- [ ] Lean proofs compile
- [ ] Physical interpretation validated
## Checklist
- [ ] Theory aligns with QBP axioms
"""
    r = m.parse(body)
    assert r == {
        "ticked": [],
        "unticked": [],
        "nil": [],
        "evidence": [],
        "region": "absent",
    }, r


def test_code_fence_ignored():
    body = """Sign-off required (merge-blocking):
```
- [ ] inside a code block, not a box
```
- [ ] @a
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_informational_word_in_box_text_does_not_close_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a — includes informational notes
- [ ] @b
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a — includes informational notes", "@b"], r


def test_cli_output():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n- [x] @b\n"
    r = subprocess.run(
        [sys.executable, SCRIPT], input=body, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr
    assert "unticked=1 ticked=1 nil=0 region=present" in r.stdout, r.stdout
    assert r.stdout.startswith("unticked=1 "), r.stdout  # first-line contract
    assert "UNTICKED: @a" in r.stdout, r.stdout
    r2 = subprocess.run(
        [sys.executable, SCRIPT, "--json"], input=body, capture_output=True, text=True
    )
    assert '"unticked": ["@a"]' in r2.stdout, r2.stdout
    assert '"region": "present"' in r2.stdout, r2.stdout


def test_never_edits_anything():
    """The parser has no write path: the module exposes parse/main only, and main only prints."""
    src = open(SCRIPT, encoding="utf-8").read()
    assert "gh pr edit" not in src and "open(" not in src.replace(
        "open(args.body_file", ""
    )


# ── Red Team round 1 (PR #731) regression cases ───────────────────────────────
def test_heading_form_opener_counts_boxes():  # G1 (BLOCKING)
    body = "## Sign-off required (merge-blocking)\n- [ ] @a\n- [x] @b\n\n## Informational\n- [ ] @c\n"
    r = m.parse(body)
    assert r["unticked"] == ["@a"] and r["ticked"] == ["@b"], r


def test_prose_mention_does_not_open_region():  # G2
    body = "Not merge-blocking: FYI.\n- [ ] informational\nThis is not merge-blocking either.\n- [ ] also informational\n"
    r = m.parse(body)
    assert r == {
        "ticked": [],
        "unticked": [],
        "nil": [],
        "evidence": [],
        "region": "absent",
    }, r


def test_bold_label_line_opens_region():  # G2 (label forms)
    body = "**Merge-blocking:**\n- [ ] @a\n"
    assert m.parse(body)["unticked"] == ["@a"]


def test_struck_fragment_in_live_ask_stays_unticked():  # G3
    body = "Sign-off required (merge-blocking):\n- [ ] @a — ~~old~~ still owed\n- [ ] ~~whole option struck~~\n- [ ] ~~x~~ ⊘ reason\n"
    r = m.parse(body)
    assert r["unticked"] == ["@a — ~~old~~ still owed"], r
    assert len(r["nil"]) == 2, r


def test_sign_off_spelling_variants():
    for label in (
        "Sign off required:",
        "Signoff required:",
        "Sign-off required (merge-blocking):",
    ):
        assert m.parse(label + "\n- [ ] @a\n")["unticked"] == ["@a"], label


def test_heading_informational_closes_region():
    body = "## Sign-off required (merge-blocking)\n- [ ] @a\n## Informational readers (non-blocking)\n- [ ] @b\n"
    assert m.parse(body)["unticked"] == ["@a"]


# ── qbp-architecture §I4 concern (PR #731 @ b045a28): no-region case must FAIL CLOSED ──
def test_no_region_reports_absent():
    """A body using neither §2.2 form: unticked=0 is NOT "nothing owed" — region=absent."""
    body = """## Summary
Some change.

## Test plan
- [ ] CI green
- [x] unit tests
"""
    r = m.parse(body)
    assert r["region"] == "absent", r
    assert r["unticked"] == [] and r["ticked"] == [], r


def test_empty_body_reports_absent():
    assert m.parse("")["region"] == "absent"


def test_label_form_reports_present():
    body = "Sign-off required (merge-blocking):\n- [x] @a\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == [], r


def test_heading_form_reports_present():
    assert (
        m.parse("## Sign-off required (merge-blocking)\n- [x] @a\n")["region"]
        == "present"
    )


def test_sentinel_form_reports_present():
    body = "<!-- merge-blocking -->\n- [x] @a\n<!-- /merge-blocking -->\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == [], r


def test_present_even_when_region_holds_no_boxes():
    """An opener with nothing under it is still an assessable (empty) region."""
    assert (
        m.parse("Sign-off required (merge-blocking):\n\nnothing here\n")["region"]
        == "present"
    )


def test_other_shape_reviewer_boxes_are_absent_and_not_counted():
    """inter-style boxes (`- [ ] **§I4 @seat** (sign-off required)`) are NOT a §2.2 region:
    region=absent, and they are neither ticked-off nor counted as unticked."""
    body = """## Reviewers
- [ ] **§I4 @qbp-architecture** (sign-off required)
- [x] **§I4 @cth-implementor** (sign-off required)
- [ ] merge-blocking: @herschel
"""
    r = m.parse(body)
    assert r == {
        "ticked": [],
        "unticked": [],
        "nil": [],
        "evidence": [],
        "region": "absent",
    }, r


def test_prose_mention_is_absent():
    """A prose sentence mentioning the words opens nothing and leaves region=absent (G2)."""
    assert m.parse("This is not merge-blocking.\n- [ ] x\n")["region"] == "absent"


def test_cli_region_absent_line():
    r = subprocess.run(
        [sys.executable, SCRIPT],
        input="- [ ] **§I4 @a** (sign-off required)\n",
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr
    assert (
        r.stdout.splitlines()[0] == "unticked=0 ticked=0 nil=0 region=absent evidence=0"
    ), r.stdout
    r2 = subprocess.run(
        [sys.executable, SCRIPT, "--json"], input="", capture_output=True, text=True
    )
    assert '"region": "absent"' in r2.stdout, r2.stdout


def test_backticked_sentinel_mention_does_not_open_region():
    """A PR that DOCUMENTS the sentinel (in an inline code span) has no real region:
    region=absent, and following boxes are not counted (found on #731's own body)."""
    body = """| §4 | use the `<!-- merge-blocking -->` sentinel or `<!-- /merge-blocking -->` |
- [ ] not a sign-off box
"""
    r = m.parse(body)
    assert r == {
        "ticked": [],
        "unticked": [],
        "nil": [],
        "evidence": [],
        "region": "absent",
    }, r


def test_sentinel_at_end_of_prose_line_still_opens():
    body = "Reviewers <!-- merge-blocking -->\n- [ ] @a\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == ["@a"], r


def test_backticked_close_sentinel_does_not_close_region():
    body = "<!-- merge-blocking -->\n- [ ] @a — see `<!-- /merge-blocking -->` docs\n- [ ] @b\n"
    assert m.parse(body)["unticked"] == [
        "@a — see `<!-- /merge-blocking -->` docs",
        "@b",
    ]


# ── #815: notifier-owned CI-green evidence box ─────────────────────────────
CI_BOX = (
    "CI green at the head sha — evidence box: the notifier (`pr-check-status.yml`) "
    "ticks it once every technical check passes (TECH-GREEN) and un-ticks it at "
    "RED; do not hand-tick (#538)"
)


def test_ci_green_box_unticked_in_region_is_evidence_not_unticked():
    body = f"""Sign-off required (merge-blocking):
- [ ] Red Team review (@qbp-architecture)
- [ ] {CI_BOX}
"""
    r = m.parse(body)
    assert r["unticked"] == ["Red Team review (@qbp-architecture)"], r
    assert r["evidence"] == [CI_BOX], r
    assert r["ticked"] == [], r


def test_region_with_only_evidence_box_unticked_is_clear():
    body = f"""Sign-off required (merge-blocking):
- [x] Red Team review (@qbp-architecture)
- [ ] {CI_BOX}
- [x] Merge authorized (beekeeper)
"""
    r = m.parse(body)
    assert r["unticked"] == [] and len(r["evidence"]) == 1, r
    out = subprocess.run(
        [sys.executable, SCRIPT], input=body, capture_output=True, text=True
    ).stdout.splitlines()[0]
    assert out == "unticked=0 ticked=2 nil=0 region=present evidence=1", out


def test_ticked_ci_green_box_in_region_is_evidence_not_ticked():
    body = f"Sign-off required (merge-blocking):\n- [x] {CI_BOX}\n"
    r = m.parse(body)
    assert r["ticked"] == [] and r["evidence"] == [CI_BOX], r


def test_review_box_mentioning_ci_green_stays_a_normal_box():
    body = """Sign-off required (merge-blocking):
- [ ] Red Team review once CI green (@qbp-architecture)
- [ ] Human Visual Review after CI green (beekeeper)
"""
    r = m.parse(body)
    assert r["evidence"] == [], r
    assert len(r["unticked"]) == 2, r


def test_ci_green_box_outside_region_unchanged():
    body = f"""## Mechanical verification evidence
- [ ] {CI_BOX}

Sign-off required (merge-blocking):
- [ ] Merge authorized (beekeeper)
"""
    r = m.parse(body)
    assert r["unticked"] == ["Merge authorized (beekeeper)"], r
    assert r["evidence"] == [] and r["ticked"] == [], r


def test_only_first_ci_green_box_is_notifier_owned():
    """set_ci_box ticks only the FIRST match; a second CI-green box is a human box."""
    body = f"""- [ ] {CI_BOX}

Sign-off required (merge-blocking):
- [ ] CI green on the downstream repo too
"""
    r = m.parse(body)
    assert r["unticked"] == ["CI green on the downstream repo too"], r
    assert r["evidence"] == [], r


def test_predicate_matches_set_ci_box_awk():
    f = m.is_ci_green_evidence_box
    assert f(f"- [ ] {CI_BOX}") and f(f"  - [X] {CI_BOX}")
    for bad in (
        "- [ ] CI green — Gemini review",
        "- [ ] CI green sign-off",
        "- [ ] CI green signoff",
        "- [ ] CI green HVR",
        "- [ ] CI green, approve",
        "* [ ] CI green",  # awk box regex is dash-only
        "- [ ] CI is green",
    ):
        assert not f(bad), bad


def _workflow_awk_program() -> str:
    """The awk program of set_ci_box, extracted verbatim between its markers."""
    wf = os.path.join(HERE, "..", ".github", "workflows", "pr-check-status.yml")
    src = open(wf, encoding="utf-8").read()
    start = src.index("# BEGIN set_ci_box-awk")
    end = src.index("# END set_ci_box-awk")
    prog = src[start:end]
    assert "'" not in prog, "awk program must stay single-quote free"
    return prog


def _awk_ticked_index(body: str, prog: str | None = None):
    """Run the workflow's real awk (-v m=x) on body; index of the line it changed."""
    out = subprocess.run(
        ["awk", "-v", "m=x", prog if prog is not None else _workflow_awk_program()],
        input=body,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    old, new = body.splitlines(), out.splitlines()
    assert len(old) == len(new), (old, new)
    changed = [i for i, (a, b) in enumerate(zip(old, new)) if a != b]
    assert len(changed) <= 1, changed
    return changed[0] if changed else None


def test_workflow_awk_and_parser_pick_the_same_box():
    """N1/G1: the REAL awk from pr-check-status.yml vs _ci_box_index, same bodies."""
    fenced = f"""Template quoted for reference:
```markdown
- [ ] {CI_BOX}
```

Sign-off required (merge-blocking):
- [ ] {CI_BOX}
- [ ] Merge authorized (beekeeper)
"""
    plain = f"## Evidence\n- [ ] {CI_BOX}\n- [ ] other\n"
    review = "- [ ] Red Team review once CI green\n- [ ] Human Visual Review\n"
    two = f"- [ ] {CI_BOX}\n- [ ] CI green on the downstream repo too\n"
    tilde = f"~~~\n- [ ] {CI_BOX}\n~~~\n- [ ] {CI_BOX}\n"
    both_ci = f"- [ ] {CI_BOX}\n- [ ] {CI_BOX}\n"
    cases = {
        "probe-merge": (B1_PROBE_MERGE, 2),
        "probe-i4": (B1_PROBE_I4, None),  # real box already [x]: awk changes nothing
        "first-of-two": (both_ci, 0),
        "t1-oracle": (T1_PROBE_ORACLE, 2),
        "t1-lean": (T1_PROBE_LEAN, 2),
        "fenced": (fenced, 6),
        "plain": (plain, 1),
        "review": (review, None),
        "two": (two, 0),
        "tilde": (tilde, 3),
    }
    for name, (body, want) in cases.items():
        if name == "probe-i4":
            # awk must leave the §I4 box alone; the parser owns the real [x] box
            assert _awk_ticked_index(body) is None, name
            assert m._ci_box_index(body.splitlines()) == 2, name
            continue
        got_awk = _awk_ticked_index(body)
        got_py = m._ci_box_index(body.splitlines())
        assert got_awk == got_py == want, (name, got_awk, got_py, want)


def test_fenced_ci_box_above_region_does_not_steal_evidence():
    """G1: a fenced template copy above the region must not make the real box unticked."""
    body = f"""```
- [ ] {CI_BOX}
```

Sign-off required (merge-blocking):
- [ ] {CI_BOX}
- [ ] Merge authorized (beekeeper)
"""
    r = m.parse(body)
    assert r["evidence"] == [CI_BOX], r
    assert r["unticked"] == ["Merge authorized (beekeeper)"], r


def test_cli_line_keeps_notifier_sed_contract():
    """The notifier's two seds must still extract unticked + region."""
    body = f"Sign-off required (merge-blocking):\n- [ ] @a\n- [ ] {CI_BOX}\n"
    line = subprocess.run(
        [sys.executable, SCRIPT], input=body, capture_output=True, text=True
    ).stdout.splitlines()[0]
    for expr, want in (
        (r"s/^unticked=\([0-9]*\).*/\1/p", "1"),
        (r"s/^unticked=.*region=\([a-z]*\).*/\1/p", "present"),
    ):
        got = subprocess.run(
            ["sed", "-n", expr], input=line, capture_output=True, text=True
        ).stdout.strip()
        assert got == want, (expr, line, got)


# ── #815 B1 (Red Team): a sign-off box mentioning CI green must never be the
# evidence box — it would be auto-ticked at TECH-GREEN AND exempt from the count.
B1_PROBE_MERGE = f"""Sign-off required (merge-blocking):
- [ ] Merge authorized (beekeeper) — once CI green
- [ ] {CI_BOX}
"""
B1_PROBE_I4 = f"""Sign-off required (merge-blocking):
- [ ] §I4 architect: confirms CI green and the diff
- [x] {CI_BOX}
"""


def _assert_b1_rows_hold():
    r = m.parse(B1_PROBE_MERGE)
    assert r["unticked"] == ["Merge authorized (beekeeper) — once CI green"], r
    assert r["evidence"] == [CI_BOX], r
    r = m.parse(B1_PROBE_I4)
    assert r["unticked"] == ["§I4 architect: confirms CI green and the diff"], r
    assert r["evidence"] == [CI_BOX], r


def test_b1_signoff_box_mentioning_ci_green_stays_unticked():
    _assert_b1_rows_hold()


def test_b1_workflow_awk_never_ticks_the_signoff_probe():
    for body in (B1_PROBE_MERGE, B1_PROBE_I4):
        idx = _awk_ticked_index(body)
        if idx is not None:
            assert "CI green at the head sha" in body.splitlines()[idx], (body, idx)
    # merge probe: the awk ticks the REAL box (line 2), not the merge box (line 1)
    assert _awk_ticked_index(B1_PROBE_MERGE) == 2


def test_b1_predicate_accepts_every_known_template_wording():
    tpl_dir = os.path.join(HERE, "..", ".github", "PULL_REQUEST_TEMPLATE")
    lines = []
    for t in (1, 2, 3):
        with open(os.path.join(tpl_dir, f"tier-{t}.md"), encoding="utf-8") as fh:
            lines += [ln.rstrip("\n") for ln in fh if "CI green" in ln]
    assert len(lines) == 3, lines
    # OLD wording still on open PRs, and PR #814's line
    lines += [
        "- [ ] CI green at the head sha — evidence box: the notifier "
        "(`pr-check-status.yml`) ticks it at ALL-GREEN and un-ticks it at RED; "
        "do not hand-tick (#538)",
        "- [x] CI green at the head sha — evidence box: the notifier ticks it at "
        "ALL-GREEN and un-ticks it at RED; do not hand-tick (#538)",
    ]
    for ln in lines:
        assert m.is_ci_green_evidence_box(ln), ln
        assert _awk_ticked_index(ln.replace("[x]", "[ ]") + "\n") == 0, ln


def test_b1_exclusions_each_block_alone():
    base = "- [ ] CI green at the head sha — evidence box {}"
    for word in (
        "merge",
        "authorised",
        "authorized",
        "§I4",
        "I4",
        "beekeeper",
        "notary",
        "confirms",
        "review",
        "sign-off",
        "HVR",
        "approve",
    ):
        line = base.format(word)
        assert not m.is_ci_green_evidence_box(line), line
        assert _awk_ticked_index(line + "\n") is None, line


def test_b1_mutant_loose_predicate_is_killed():
    """Revert to the pre-B1 loose rule: the B1 regression rows must FAIL under it."""
    import re

    loose_ex = re.compile(r"review|sign.?off|visual|hvr|red team|gemini|approve")

    def loose(line):
        low = line.lower()
        return bool(
            m._CI_BOX_RE.match(line) and "ci green" in low and not loose_ex.search(low)
        )

    real = m.is_ci_green_evidence_box
    m.is_ci_green_evidence_box = loose
    try:
        try:
            _assert_b1_rows_hold()
            killed = False
        except AssertionError:
            killed = True
    finally:
        m.is_ci_green_evidence_box = real
    assert killed, "mutant (loose predicate) survived the B1 regression rows"
    _assert_b1_rows_hold()  # and the real predicate still passes


# ── #815 T1 (Red Team re-confirm): rows with "ci green" and NO excluded word, so
# ONLY the wording rule (_CI_REQUIRE / the two narrowed awk clauses) rejects them.
T1_ROWS = (
    "Differential oracle: CI green on PhysLean",
    "Lean build CI green (oppenheimer)",
)
T1_PROBE_ORACLE = f"""Sign-off required (merge-blocking):
- [ ] {T1_ROWS[0]}
- [ ] {CI_BOX}
"""
T1_PROBE_LEAN = f"""Sign-off required (merge-blocking):
- [ ] {T1_ROWS[1]}
- [ ] {CI_BOX}
"""


def test_t1_rows_carry_no_excluded_word():
    for row in T1_ROWS:
        assert "ci green" in row.lower()
        assert not m._CI_EXCLUDE_RE.search(row.lower()), row


def _assert_t1_rows_hold():
    for row, body in zip(T1_ROWS, (T1_PROBE_ORACLE, T1_PROBE_LEAN)):
        r = m.parse(body)
        assert r["unticked"] == [row], r
        assert r["evidence"] == [CI_BOX], r


def test_t1_wording_rule_keeps_rows_unticked():
    _assert_t1_rows_hold()
    for body in (T1_PROBE_ORACLE, T1_PROBE_LEAN):
        assert _awk_ticked_index(body) == 2, body  # real box, not the row (line 1)


def test_t1_python_wording_only_mutant_is_killed():
    """Loosen ONLY _CI_REQUIRE back to "ci green" (exclusions kept): must fail."""
    real = m._CI_REQUIRE
    m._CI_REQUIRE = ("ci green",)
    try:
        try:
            _assert_t1_rows_hold()
            killed = False
        except AssertionError:
            killed = True
    finally:
        m._CI_REQUIRE = real
    assert killed, "wording-only mutant survived the T1 rows"
    _assert_t1_rows_hold()


def test_t1_awk_wording_only_mutant_is_killed():
    """Revert the two narrowed awk clauses to /ci green/: it must tick the T1 row."""
    prog = _workflow_awk_program()
    a, b = "/ci green at the head sha/", "tolower(line) ~ /evidence box/"
    assert prog.count(a) == 1 and prog.count(b) == 1, prog
    mutant = prog.replace(a, "/ci green/").replace(b, "tolower(line) ~ /ci green/")
    assert mutant != prog and "head sha" not in mutant and "evidence box" not in mutant
    for body in (T1_PROBE_ORACLE, T1_PROBE_LEAN):
        assert _awk_ticked_index(body, mutant) == 1, body  # mutant ticks the WRONG row
        assert _awk_ticked_index(body) == 2, body  # real program ticks the real box


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
