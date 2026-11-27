#!/usr/bin/env python3
"""Tests for scripts/merge_blocking_check.py (#507 §7 required check — exit codes + output).

Run: python3 scripts/test_merge_blocking_check.py   (also pytest-collectable)
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import merge_blocking_check as c  # noqa: E402

SCRIPT = os.path.join(HERE, "merge_blocking_check.py")

ALL_TICKED = "## §I4 review\nSign-off required (merge-blocking):\n- [x] @a\n- [X] @b\n"
ONE_UNTICKED = (
    "Sign-off required (merge-blocking):\n- [ ] @qbp-architecture — coherence\n"
    "- [x] @cth-implementor — eval-side\nInformational readers (non-blocking):\n"
    "- [ ] @qbp-oppenheimer — theory shape\n"
)
ABSENT = "## Summary\nx\n\n## Test plan\n- [ ] CI green\n- [x] unit tests\n"
NILD = (
    "<!-- merge-blocking -->\n- [x] @a\n- [ ] ~~schema co-sign~~ ⊘ n/a\n"
    "- [ ] ⊘ two-axis\n<!-- /merge-blocking -->\n- [ ] informational\n"
)


def run(body, *flags):
    return subprocess.run(
        [sys.executable, SCRIPT, *flags], input=body, capture_output=True, text=True
    )


def test_all_ticked_passes():
    r = run(ALL_TICKED)
    assert r.returncode == 0, r.stdout
    assert r.stdout.startswith("unticked=0 ticked=2 nil=0 region=present"), r.stdout
    assert "::notice::" in r.stdout and "::error::" not in r.stdout, r.stdout


def test_one_unticked_fails_and_names_the_box():
    r = run(ONE_UNTICKED)
    assert r.returncode == 1, r.stdout
    assert "::error::unticked merge-blocking box: @qbp-architecture — coherence" in (
        r.stdout
    ), r.stdout
    assert "- [ ] @qbp-architecture — coherence" in r.stdout, r.stdout
    assert "@qbp-oppenheimer" not in r.stdout.split("::error::", 1)[1], r.stdout
    assert c.DOC_URL in r.stdout and "⊘-nil" in r.stdout, r.stdout


def test_absent_region_passes_with_warning():
    r = run(ABSENT)
    assert r.returncode == 0, r.stdout
    assert "region=absent" in r.stdout.splitlines()[0], r.stdout
    assert "::warning::" in r.stdout and "::error::" not in r.stdout, r.stdout
    assert "Sign-off required (merge-blocking):" in r.stdout, r.stdout
    assert "<!-- merge-blocking -->" in r.stdout, r.stdout


def test_absent_region_blocks_with_flip():
    r = run(ABSENT, "--absent-blocks")
    assert r.returncode == 1, r.stdout
    assert "::error::" in r.stdout and "::warning::" not in r.stdout, r.stdout


def test_nil_boxes_pass():
    r = run(NILD)
    assert r.returncode == 0, r.stdout
    assert r.stdout.startswith("unticked=0 ticked=1 nil=2 region=present"), r.stdout


def test_empty_body_is_absent_not_fail():
    assert run("").returncode == 0
    assert run("", "--absent-blocks").returncode == 1


def test_mixed_counts_every_unticked_box():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n- [x] @b\n- [ ] @c\n"
    r = run(body)
    assert r.returncode == 1
    assert r.stdout.count("::error::") == 2, r.stdout
    assert "unticked=2 ticked=1 nil=0 region=present" in r.stdout, r.stdout


def test_unticked_outside_region_does_not_fail():
    body = (
        "Sign-off required (merge-blocking):\n- [x] @a\n\n## Test plan\n- [ ] later\n"
    )
    assert run(body).returncode == 0


def test_annotations_are_single_line():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n"
    for line in run(body).stdout.splitlines():
        if line.startswith("::"):
            assert "\n" not in line and line.count("::") >= 2, line


def test_annotation_escapes_percent_and_newline():
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        c._annot("error", "100% done\r\nsecond line")
    assert buf.getvalue() == "::error::100%25 done%0D%0Asecond line\n", buf.getvalue()
    body = "Sign-off required (merge-blocking):\n- [ ] @a — 50% coverage\n"
    r = run(body)
    assert r.returncode == 1 and "50%25 coverage" in r.stdout, r.stdout
    assert "- [ ] @a — 50% coverage" in r.stdout, r.stdout  # human listing unescaped


def test_body_file_and_unreadable_file():
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(ONE_UNTICKED)
    try:
        assert run("", "--body-file", fh.name).returncode == 1
    finally:
        os.unlink(fh.name)
    r = run("", "--body-file", fh.name)  # now missing
    assert r.returncode == 2 and "::error::" in r.stdout, r.stdout


def test_check_function_parity_with_cli():
    import contextlib
    import io

    for body, want in ((ALL_TICKED, 0), (ONE_UNTICKED, 1), (ABSENT, 0), (NILD, 0)):
        with contextlib.redirect_stdout(io.StringIO()):
            assert c.check(body) == want == run(body).returncode, body


def test_never_edits_anything():
    src = open(SCRIPT, encoding="utf-8").read()
    assert "gh pr edit" not in src and "gh api" not in src
    # two reads only (#835 added the changed-file list); no write mode anywhere
    # three reads only (body, changed-file list, workflow files for the R2 lane
    # derivation); no write mode anywhere
    assert src.count("open(") == 3, src.count("open(")
    assert "open(args.body_file" in src and "open(args.changed_file" in src
    assert '"w"' not in src and "'w'" not in src


# ---- #835 beekeeper-box scope guard (ruling 2026-11-24, QBP#714 issuecomment-7147354671)

HK = ["housekeeping", "tier-2-review"]
HVR_NILD = (
    "Sign-off required (merge-blocking):\n- [x] Red Team review\n- [x] Gemini review\n"
    "- [ ] ~~Human Visual Review (beekeeper)~~ ⊘ pure housekeeping\n"
    "- [ ] ~~Merge authorized (beekeeper; QBP lane)~~ ⊘ pure housekeeping\n"
)
BK_TICKED = (
    "Sign-off required (merge-blocking):\n- [x] Red Team review\n- [x] Gemini review\n"
    "- [x] Human Visual Review (beekeeper)\n- [x] Merge authorized (beekeeper; QBP lane)\n"
)
OTHER_NILD = (
    "Sign-off required (merge-blocking):\n- [x] Red Team review\n"
    "- [ ] ~~schema co-sign~~ ⊘ n/a\n- [x] Human Visual Review (beekeeper)\n"
    "- [x] Merge authorized (beekeeper; QBP lane)\n"
)
NO_BK_BOXES = (
    "Sign-off required (merge-blocking):\n- [x] Red Team review\n- [x] Gemini review\n"
)


REPO = os.path.dirname(HERE)


def _scoped(body, labels, changed, head_root=None):
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write("\n".join(changed) + "\n")
        path = fh.name
    try:
        extra = [f"--head-root={head_root}"] if head_root else []
        return run(
            body, f"--labels={','.join(labels)}", f"--changed-file={path}", *extra
        )
    finally:
        os.unlink(path)


def test_hvr_nil_passes_on_pure_housekeeping():
    r = _scoped(HVR_NILD, HK, ["scripts/x.py", "docs/notes.md"])
    assert r.returncode == 0, r.stdout


def test_hvr_nil_fails_without_housekeeping_label():
    r = _scoped(HVR_NILD, ["tier-2-review"], ["scripts/x.py"])
    assert r.returncode == 1 and "no `housekeeping` label" in r.stdout, r.stdout
    assert r.stdout.count("::error::⊘-nil'd beekeeper box") == 2, r.stdout


def test_housekeeping_label_match_is_exact():
    # near-miss labels fail closed; surrounding whitespace is stripped
    assert _scoped(HVR_NILD, ["Housekeeping"], ["scripts/x.py"]).returncode == 1
    assert _scoped(HVR_NILD, ["housekeeping "], ["scripts/x.py"]).returncode == 0


def test_hvr_nil_fails_on_every_theory_path_even_if_housekeeping():
    for path in (
        "proofs/QBP/Foo.lean",
        "docs/foundations/a.md",
        "docs/theory/b.md",
        "paper/main.tex",
        "archive/cth-inventory/x.json",
    ):
        r = _scoped(HVR_NILD, ["housekeeping"], ["scripts/x.py", path])
        assert r.returncode == 1 and "theory-bearing" in r.stdout, (path, r.stdout)


def test_rename_out_of_proofs_counts_as_theory():
    # the workflow writes BOTH filename and previous_filename for a rename (F1)
    r = _scoped(HVR_NILD, ["housekeeping"], ["archive/X.lean", "proofs/QBP/X.lean"])
    assert r.returncode == 1 and "theory-bearing" in r.stdout, r.stdout


def test_hvr_nil_fails_on_tier3_label_case_folded():
    for lab in ("tier-3-review", "Tier-3-Review", " tier-3-review "):
        r = _scoped(HVR_NILD, ["housekeeping", lab], ["scripts/x.py"])
        assert r.returncode == 1 and "theory-bearing" in r.stdout, (lab, r.stdout)


def test_theory_status_never_depends_on_a_missing_label():
    # no tier-3 label yet (GITHUB_TOKEN auto-label race, F2): paths alone decide
    r = _scoped(HVR_NILD, ["housekeeping"], ["paper/a.tex"])
    assert r.returncode == 1, r.stdout


def test_lane_files_are_never_pure_housekeeping():
    for path in (
        "CONTRIBUTING.md",
        "docs/workflows/review_tiers.md",
        ".github/PULL_REQUEST_TEMPLATE/tier-2.md",
        ".github/workflows/merge-blocking-boxes.yml",
        ".github/workflows/tier-3-review-gate.yml",
        ".github/workflows/pr-check-status.yml",
        "scripts/merge_blocking_check.py",
        "scripts/pr_merge_blocking_boxes.py",
        "scripts/merge_blocking_verdict_source.py",
        "scripts/check_tier3_label.py",
        ".github/CODEOWNERS",
    ):
        r = _scoped(HVR_NILD, ["housekeeping"], [path])
        assert r.returncode == 1 and "merge-lane" in r.stdout, (path, r.stdout)
    # a similarly-named file that is not a lane file stays housekeeping
    assert _scoped(HVR_NILD, HK, ["docs/CONTRIBUTING-notes.md"]).returncode == 0


def test_pr_838_itself_cannot_nil_the_boxes():
    changed = [
        ".github/PULL_REQUEST_TEMPLATE/tier-2.md",
        ".github/workflows/merge-blocking-boxes.yml",
        "CONTRIBUTING.md",
        "docs/workflows/review_tiers.md",
        "scripts/merge_blocking_check.py",
    ]
    assert _scoped(HVR_NILD, HK, changed).returncode == 1


def test_hvr_nil_fails_closed_without_scope_inputs():
    r = run(HVR_NILD)
    assert r.returncode == 1 and "fail closed" in r.stdout, r.stdout


def test_nil_name_variants_are_all_caught():
    for box in (
        "HVR",
        "HVRs",
        "H.V.R.",
        "Human-Visual-Review",
        "Human​Visual Review",
        "ＨＶＲ",  # fullwidth → NFKC (kills a dropped normalize)
        "Mer\u200bge author\u200bised",  # zero-width inside words (kills a dropped _ZW_RE)
        "Visual review (beekeeper)",
        "Beekeeper review",
        "Merge authorised",
        "Merge approval (beekeeper)",
    ):
        # both canonical boxes ticked, so only the nil rule can turn this red
        body = BK_TICKED + f"- [ ] ~~{box}~~ ⊘ pure housekeeping\n"
        r = _scoped(body, ["tier-2-review"], ["scripts/x.py"])
        assert r.returncode == 1 and "⊘-nil'd beekeeper box" in r.stdout, (
            box,
            r.stdout,
        )
        assert "required beekeeper box missing" not in r.stdout, (box, r.stdout)


def test_ordinary_nils_stay_ordinary():
    # M4e: the wide nil match must not swallow unrelated nils
    for box in ("schema co-sign", "Red Team review", "Gemini review", "two-axis"):
        body = BK_TICKED + f"- [ ] ~~{box}~~ ⊘ n/a\n"
        r = _scoped(body, ["tier-2-review"], ["scripts/x.py"])
        assert r.returncode == 0, (box, r.stdout)


def test_other_nils_unaffected_by_guard():
    assert run(OTHER_NILD).returncode == 0
    assert _scoped(OTHER_NILD, ["tier-3-review"], ["proofs/a.lean"]).returncode == 0


def test_tier2_requires_ticked_bk_boxes_present():
    # F5: a deleted HVR / merge-authorized box cannot pass on a Tier 2+ PR
    r = _scoped(NO_BK_BOXES, ["tier-2-review"], ["scripts/x.py"])
    assert r.returncode == 1 and r.stdout.count("required beekeeper box missing") == 2
    assert _scoped(BK_TICKED, ["tier-2-review"], ["scripts/x.py"]).returncode == 0


def test_theory_pr_requires_ticked_bk_boxes_even_with_lookalike_nil():
    # a Cyrillic-а lookalike evades the name match, but the positive rule catches it
    body = NO_BK_BOXES + "- [ ] ~~Humаn Visuаl Rеviеw~~ ⊘ x\n"
    r = _scoped(body, ["tier-3-review"], ["proofs/a.lean"])
    assert r.returncode == 1 and "required beekeeper box missing" in r.stdout, r.stdout


def test_box_moved_out_of_region_is_missing():
    body = (
        NO_BK_BOXES
        + "\nSome prose.\n- [x] Human Visual Review\n- [x] Merge authorized\n"
    )
    assert _scoped(body, ["tier-2-review"], ["scripts/x.py"]).returncode == 1


def test_unticked_bk_box_reported_once_as_unticked():
    body = (
        NO_BK_BOXES + "- [ ] Human Visual Review (beekeeper)\n- [x] Merge authorized\n"
    )
    r = _scoped(body, ["tier-2-review"], ["scripts/x.py"])
    assert r.returncode == 1 and "unticked merge-blocking box: Human Visual" in r.stdout
    assert "required beekeeper box missing" not in r.stdout, r.stdout


def test_plain_tier1_and_pure_housekeeping_need_no_bk_boxes():
    assert _scoped(NO_BK_BOXES, ["tier-1-review"], ["docs/x.md"]).returncode == 0
    assert _scoped(NO_BK_BOXES, HK, ["scripts/x.py"]).returncode == 0
    # a tier-1 label cannot exempt theory or lane files
    assert _scoped(NO_BK_BOXES, ["tier-1-review"], ["paper/a.tex"]).returncode == 1
    assert _scoped(NO_BK_BOXES, ["tier-1-review"], ["CONTRIBUTING.md"]).returncode == 1


def test_label_starting_with_dash_is_parsed():
    r = _scoped(BK_TICKED, ["-x", "tier-2-review"], ["scripts/x.py"])
    assert r.returncode == 0, (r.returncode, r.stdout, r.stderr)


def test_theory_definition_is_superset_of_both_gates():
    import check_pr_prose_claims as lint
    import check_tier3_label as t3

    for p in lint.THEORY_PATHS:
        assert p.startswith(c.THEORY_PATHS), p
    assert c.THEORY_LABEL == lint.THEORY_LABEL == t3.TIER3_LABEL
    for g in t3.THEORY_GLOBS:
        prefix = g.split("*", 1)[0]
        assert prefix.startswith(c.THEORY_PATHS), g


def test_workflow_scope_wiring():
    """F6: pin the #835 wiring in merge-blocking-boxes.yml."""
    import yaml

    wf = yaml.safe_load(open(WORKFLOW, encoding="utf-8"))
    on = wf.get("on", wf.get(True))
    types = on["pull_request"]["types"]
    assert "labeled" in types and "unlabeled" in types, types
    steps = wf["jobs"]["merge-blocking-boxes"]["steps"]
    scope = [s for s in steps if s.get("id") == "scope"]
    assert len(scope) == 1, steps
    run_ = scope[0]["run"]
    assert "--paginate" in run_, run_
    assert (
        """--jq '.[] | [.filename, (.previous_filename // "")] | @tsv'""" in run_
    ), run_
    assert '[ "$n_api" != "$n_pr" ]' in run_, run_
    mism = run_.split('[ "$n_api" != "$n_pr" ]', 1)[1].split("\nfi", 1)[0]
    assert "exit 1" in mism, mism
    assert 'echo "proofs/__enumeration_incomplete__" >> /tmp/changed.txt' in run_, run_
    assert "-gt 3000" in run_, run_
    verdict = steps[-1]
    assert (
        '${SCOPE:+"--labels=$LABELS" --changed-file=/tmp/changed.txt --head-root=.}'
        in verdict["run"]
    ), verdict["run"]
    assert verdict["env"]["SCOPE"] == "${{ steps.scope.outputs.supported }}"
    assert verdict["env"]["LABELS"] == "${{ steps.scope.outputs.labels }}"


def test_tier3_gate_sees_both_sides_of_a_rename():
    wf = open(
        os.path.join(
            os.path.dirname(HERE), ".github", "workflows", "tier-3-review-gate.yml"
        ),
        encoding="utf-8",
    ).read()
    assert (
        "git diff --name-only --no-renames" in wf
    ), "tier-3 gate must list rename sources"


# ---- round 3 (delta Red Team at eaaaa86, PR #838)

PR828_BODY = (
    "## Follow-ups (not forced, not done here)\n\n- x\n\n## Review / merge\n\n"
    "- [ ] Security check (Thompson via deming) PASS\n"
    "- [x] Red Team review — APPROVE\n- [x] Gemini review (real API)\n"
    "- [ ] Human Visual Review (beekeeper)\n- [ ] merge authorized\n\n---\n*Tier 2*\n"
)
PR828_LABELS = ["housekeeping", "tier-2-review", "tier-3-review", "review-ready"]
PR828_FILES = [f"proofs/QBP/File{i}.lean" for i in range(16)]


def test_r1_pr828_shape_no_region_on_theory_pr_is_red():
    r = _scoped(PR828_BODY, PR828_LABELS, PR828_FILES)
    assert (
        r.returncode == 1 and "no §2.2 region on a theory / merge-lane PR" in r.stdout
    )
    # empty body, no labels, theory paths: still red
    assert _scoped("", [], PR828_FILES).returncode == 1


def test_r1_no_region_on_lane_pr_is_red():
    assert _scoped(ABSENT, ["housekeeping"], ["CONTRIBUTING.md"]).returncode == 1


def test_r1_no_region_elsewhere_stays_warn_only():
    for labels, changed in ((["tier-2-review"], ["src/x.py"]), (HK, ["docs/x.md"])):
        r = _scoped(ABSENT, labels, changed)
        assert r.returncode == 0 and "::warning::" in r.stdout, (labels, r.stdout)
    # unscoped (no inputs) keeps the #781 policy too
    assert run(ABSENT).returncode == 0


R2_FILES = (
    "scripts/notifier_review_state.py",
    ".github/workflows/pr-process-lints.yml",
    "scripts/check_pr_prose_claims.py",
    "scripts/check_notifier_workflow_list.py",
    ".github/workflows/closing-ac-guard.yml",
    ".github/workflows/reopen-falsely-closed.yml",
)
# the hand list as of round 2 + the six R2 names: the structural set must cover it
HAND_LIST = (
    "CONTRIBUTING.md",
    "docs/workflows/review_tiers.md",
    ".github/PULL_REQUEST_TEMPLATE/tier-2.md",
    ".github/CODEOWNERS",
    "CODEOWNERS",
    "docs/CODEOWNERS",
    ".github/workflows/merge-blocking-boxes.yml",
    ".github/workflows/tier-3-review-gate.yml",
    ".github/workflows/pr-check-status.yml",
    "scripts/merge_blocking_check.py",
    "scripts/pr_merge_blocking_boxes.py",
    "scripts/merge_blocking_verdict_source.py",
    "scripts/check_tier3_label.py",
    "scripts/pr_box_evidence.py",
) + R2_FILES


def test_r2_missing_gate_files_are_lane():
    # with the real head checkout, so the backstop's fail-closed default can't mask
    # a lane workflow that is lane only by NAME (no write grant of its own)
    for path in R2_FILES:
        for hr in (None, REPO):
            r = _scoped(HVR_NILD, ["housekeeping"], [path], head_root=hr)
            assert r.returncode == 1 and "merge-lane" in r.stdout, (path, hr, r.stdout)


def test_r2_structural_set_covers_the_hand_list():
    for path in HAND_LIST:
        assert c.touches_lane([path]), path
    derived = c.workflow_scripts()
    assert derived is not None and len(derived) > 20, derived
    for path in HAND_LIST:
        if path.startswith("scripts/"):
            assert path in derived, f"{path} not derived from any workflow"


def test_r4_fixed_lane_files_and_codeowners():
    for path in (
        ".github/PULL_REQUEST_TEMPLATE/tier-1.md",
        "CONTRIBUTING.md",
        "docs/workflows/review_tiers.md",
        ".github/CODEOWNERS",
        "sub/CODEOWNERS",
    ):
        assert c.touches_lane([path]), path
    # a script no lane workflow references stays housekeeping
    assert not c.touches_lane(["scripts/some_unreferenced_helper.py"])


def test_r4_narrow_set_is_the_lane_workflows_and_their_scripts():
    derived = c.workflow_scripts()
    assert derived is not None
    for s_ in (
        "scripts/audit_closed_acs.py",
        "scripts/check_closing_acs.py",
        "scripts/check_pending_upgrades.py",
        "scripts/check_job_display_names.py",
    ):
        assert s_ in derived, s_
    # ordinary CI / content-lint scripts are NOT in the narrow set
    for s_ in (
        "scripts/agda_forbidden_tokens.py",
        "scripts/tenancy_xref_linter.py",
        "scripts/root_audit.py",
        "scripts/list_numeric_anchors.py",
    ):
        assert s_ not in derived, s_


# PR #826 (Agda CI) and PR #778 (Lean CI): named housekeeping by the ruling
PR826_FILES = [
    ".github/workflows/agda-cubical.yml",
    ".github/workflows/agda-substrate.yml",
    "scripts/agda_forbidden_tokens.py",
    "scripts/test_agda_forbidden_tokens.py",
]
PR778_FILES = [".github/workflows/ci.yml", ".github/workflows/lean-foundations.yml"]


def test_r4_pr826_and_pr778_stay_pure_housekeeping():
    old, c._HEAD_ROOT = c._HEAD_ROOT, REPO
    try:
        for files in (PR826_FILES, PR778_FILES):
            assert not c.touches_lane(files), files
    finally:
        c._HEAD_ROOT = old
    for files in (PR826_FILES, PR778_FILES):
        r = _scoped(HVR_NILD, HK, files, head_root=REPO)
        assert r.returncode == 0, (files, r.stdout)


def test_r4_backstop_workflow_gaining_power_is_lane():
    import tempfile

    for grant in (
        "permissions:\n  pull-requests: write\n",
        "permissions:\n  issues: write\n",
        "permissions:\n  contents: write\n",
        "permissions: write-all\n",
        "run: gh pr merge 1 --squash\n",
        "run: gh pr edit 1 --add-label x\n",
        "run: gh pr close 1\n",
        "run: gh issue close 2\n",
        "run: gh issue reopen 2\n",
        "run: gh issue edit 2 --add-label y\n",
    ):
        with tempfile.TemporaryDirectory() as head:
            os.makedirs(os.path.join(head, ".github", "workflows"))
            with open(os.path.join(head, ".github", "workflows", "ci.yml"), "w") as fh:
                fh.write("name: CI\n" + grant)
            r = _scoped(HVR_NILD, HK, [".github/workflows/ci.yml"], head_root=head)
            assert r.returncode == 1 and "merge-lane" in r.stdout, (grant, r.stdout)
    # a read-only workflow edit stays housekeeping; a deleted workflow too
    with tempfile.TemporaryDirectory() as head:
        os.makedirs(os.path.join(head, ".github", "workflows"))
        with open(os.path.join(head, ".github", "workflows", "ci.yml"), "w") as fh:
            fh.write("name: CI\npermissions:\n  contents: read\n")
        assert (
            _scoped(
                HVR_NILD, HK, [".github/workflows/ci.yml"], head_root=head
            ).returncode
            == 0
        )
        assert (
            _scoped(
                HVR_NILD, HK, [".github/workflows/gone.yml"], head_root=head
            ).returncode
            == 0
        )


def test_r4_backstop_fails_closed_without_head_root():
    r = _scoped(HVR_NILD, HK, PR778_FILES)
    assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout


def test_r2_derivation_fails_closed_without_workflows():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        assert c.workflow_scripts(d) is None
        assert c.touches_lane(["scripts/some_unreferenced_helper.py"], root=d)
        assert c.touches_lane([".github/workflows/ci.yml"], root=d)
        assert not c.touches_lane(["docs/x.md"], root=d)
        # cannot derive → a read-only workflow edit is still lane (fails closed even
        # when the backstop, given a head copy, would say "no power")
        old, c._HEAD_ROOT = c._HEAD_ROOT, REPO
        try:
            assert c.touches_lane([".github/workflows/ci.yml"], root=d)
            assert not c.touches_lane([".github/workflows/ci.yml"])
        finally:
            c._HEAD_ROOT = old
        wf = os.path.join(d, ".github", "workflows")
        os.makedirs(wf)
        os.makedirs(os.path.join(d, "scripts"))
        # every lane workflow present but one → still None (partial read fails open)
        for n in c.LANE_WORKFLOWS[1:]:
            with open(os.path.join(wf, n), "w") as fh:
                fh.write("name: x\n")
        assert c.workflow_scripts(d) is None
        # all present, one references a gate script that imports a helper
        with open(os.path.join(wf, c.LANE_WORKFLOWS[0]), "w") as fh:
            fh.write('run: python3 "$SRC_DIR/scripts/gate_x.py"\n')
        with open(os.path.join(d, "scripts", "gate_x.py"), "w") as fh:
            fh.write("import helper_y\nimport os\n")
        with open(os.path.join(d, "scripts", "helper_y.py"), "w") as fh:
            fh.write("X = 1\n")
        assert c.workflow_scripts(d) == {"scripts/gate_x.py", "scripts/helper_y.py"}
        assert c.touches_lane(["scripts/helper_y.py"], root=d)
        assert not c.touches_lane(["scripts/other.py"], root=d)
        # a non-UTF-8 lane workflow → None, not a crash
        with open(os.path.join(wf, c.LANE_WORKFLOWS[1]), "wb") as fh:
            fh.write(b"\xff\xfe\x00bad")
        assert c.workflow_scripts(d) is None
        with open(os.path.join(wf, c.LANE_WORKFLOWS[1]), "w") as fh:
            fh.write("name: x\n")
        # an unparseable lane script → None
        with open(os.path.join(d, "scripts", "gate_x.py"), "w") as fh:
            fh.write("def (:\n")
        assert c.workflow_scripts(d) is None


def test_r3_n12_merge_blocking_box_is_not_merge_authorized():
    body = (
        NO_BK_BOXES
        + "- [x] Human Visual Review (beekeeper)\n- [x] Merge-blocking boxes green\n"
    )
    r = _scoped(body, ["tier-2-review"], ["src/x.py"])
    assert (
        r.returncode == 1 and "Merge authorized (beekeeper; QBP lane)" in r.stdout
    ), r.stdout


def test_r3_m4f_n9_nil_variants():
    for box in ("Merge approval", "Human_Visual_Review"):
        body = BK_TICKED + f"- [ ] ~~{box}~~ ⊘ pure housekeeping\n"
        r = _scoped(body, ["tier-2-review"], ["src/x.py"])
        assert r.returncode == 1 and "⊘-nil'd beekeeper box" in r.stdout, (
            box,
            r.stdout,
        )


def _head_with(rel, content, binary=False):
    import tempfile

    d = tempfile.mkdtemp()
    full = os.path.join(d, rel)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "wb" if binary else "w") as fh:
        fh.write(content)
    return d


def test_r5_f2_backstop_catches_every_write_form():
    import shutil

    for grant in (
        'permissions:\n  "pull-requests": write\n',
        'permissions:\n  pull-requests: "write"\n',
        "permissions:\n  'issues': 'write'\n",
        "permissions:\n  statuses: write\n",
        "permissions:\n  checks: write\n",
        "permissions:\n  actions: write\n",
        "permissions: {pull-requests: write}\n",
        "env:\n  GH_TOKEN: ${{ secrets.SIBLING_READ_TOKEN }}\n",
        "env:\n  T: ${{ secrets['OTHER_PAT'] }}\n",
        "jobs:\n  x:\n    uses: ./.github/workflows/y.yml\n    secrets: inherit\n",
    ):
        head = _head_with(".github/workflows/new.yml", "name: N\n" + grant)
        try:
            r = _scoped(HVR_NILD, HK, [".github/workflows/new.yml"], head_root=head)
            assert r.returncode == 1 and "merge-lane" in r.stdout, (grant, r.stdout)
        finally:
            shutil.rmtree(head)


def test_r5_f2_non_merge_scopes_and_github_token_are_not_power():
    import shutil

    for ok in (
        "permissions:\n  contents: read\n  security-events: write\n",
        "env:\n  GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n",
        "env:\n  GH_TOKEN: ${{ github.token }}\n",
    ):
        head = _head_with(".github/workflows/new.yml", "name: N\n" + ok)
        try:
            r = _scoped(HVR_NILD, HK, [".github/workflows/new.yml"], head_root=head)
            assert r.returncode == 0, (ok, r.stdout)
        finally:
            shutil.rmtree(head)


def test_r5_f3_composite_action_backstop():
    import shutil

    for name in ("action.yml", "action.yaml"):
        rel = f".github/actions/m/{name}"
        head = _head_with(
            rel, "runs:\n  using: composite\n  steps:\n    - run: gh pr merge 1\n"
        )
        try:
            r = _scoped(HVR_NILD, HK, [rel], head_root=head)
            assert r.returncode == 1 and "merge-lane" in r.stdout, (rel, r.stdout)
        finally:
            shutil.rmtree(head)
    head = _head_with(".github/actions/m/action.yml", "runs:\n  using: composite\n")
    try:
        r = _scoped(HVR_NILD, HK, [".github/actions/m/action.yml"], head_root=head)
        assert r.returncode == 0, r.stdout
    finally:
        shutil.rmtree(head)
    # no head copy → fail closed for actions too
    assert _scoped(HVR_NILD, HK, [".github/actions/m/action.yml"]).returncode == 1


def test_r5_f4_f6_symlink_and_unreadable_head_workflow_are_lane():
    import shutil
    import tempfile

    # F4: symlink → lane without reading (a /dev/zero target would hang a read)
    d = tempfile.mkdtemp()
    try:
        os.makedirs(os.path.join(d, ".github", "workflows"))
        os.symlink("/dev/zero", os.path.join(d, ".github", "workflows", "z.yml"))
        r = subprocess.run(
            [
                sys.executable,
                SCRIPT,
                "--labels=housekeeping",
                f"--changed-file={_write_tmp('.github/workflows/z.yml')}",
                f"--head-root={d}",
            ],
            input=HVR_NILD,
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout
    finally:
        shutil.rmtree(d)
    # F6 (kills B5): a non-UTF-8 head workflow counts as power
    head = _head_with(
        ".github/workflows/bad.yml", b"\xff\xfe\x00name: x\n", binary=True
    )
    try:
        r = _scoped(HVR_NILD, HK, [".github/workflows/bad.yml"], head_root=head)
        assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout
    finally:
        shutil.rmtree(head)


def _write_tmp(text):
    import tempfile

    fh = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
    fh.write(text + "\n")
    fh.close()
    return fh.name


def test_r5_f1_verdict_job_runs_no_head_code():
    """F1: no step in the verdict job executes a head-side file; head self-tests
    run in a separate job (another runner), so head code cannot rewrite base/."""
    import yaml

    wf = yaml.safe_load(open(WORKFLOW, encoding="utf-8"))
    jobs = wf["jobs"]
    verdict_job = jobs["merge-blocking-boxes"]
    assert verdict_job["name"] == "Merge-blocking boxes"
    for st in verdict_job["steps"]:
        run_ = st.get("run", "")
        # every python3 invocation must target the judging copy ($SRC_DIR or base/)
        for m in re.finditer(r"python3\s+(\S+)", run_):
            target = m.group(1).strip('"')
            assert target.startswith(("$SRC_DIR/", "base/", '"$SEL"', "$SEL", "-")), (
                st,
                target,
            )
        assert "SEL=scripts/" not in run_, st  # no head selector fallback
    sel = [st for st in verdict_job["steps"] if st.get("id") == "src"][0]["run"]
    assert "SEL=base/scripts/merge_blocking_verdict_source.py" in sel, sel
    # the head self-tests live in their own job with a distinct display name
    head_jobs = [
        (k, j)
        for k, j in jobs.items()
        if k != "merge-blocking-boxes"
        and any(
            "python3 scripts/test_merge_blocking_check.py" in s.get("run", "")
            for s in j["steps"]
        )
    ]
    assert len(head_jobs) == 1, list(jobs)
    k, j = head_jobs[0]
    assert j.get("name") != "Merge-blocking boxes" and "needs" not in j, (k, j)


def _power_rc(rel, content, binary=False):
    import shutil

    head = _head_with(rel, content, binary=binary)
    try:
        return _scoped(HVR_NILD, HK, [rel], head_root=head)
    finally:
        shutil.rmtree(head)


def test_r6_g2_yaml_bypasses_are_power():
    for body in (
        # anchor + alias
        "x-perm: &w write\npermissions:\n  pull-requests: *w\n",
        # folded / literal block scalars
        "permissions:\n  pull-requests: >-\n    write\n",
        "permissions:\n  pull-requests: |-\n    write\n",
        # double-quoted escape
        'permissions:\n  pull-requests: "\\x77rite"\n',
        # anchored mapping, escaped key, complex key, job level
        "x: &p\n  statuses: write\npermissions: *p\n",
        'permissions:\n  "pull\\x2drequests": write\n',
        "permissions:\n  ? pull-requests\n  : write\n",
        "jobs:\n  a:\n    runs-on: x\n    permissions:\n      checks: write\n",
        # explicit write-all (G6 / B4)
        "permissions: write-all\n",
        "jobs:\n  a:\n    permissions: write-all\n",
        # only the structural walk sees these (kills G2d / G2f): escaped write-all,
        # and an escaped grant nested at job level
        'permissions: "write\\x2dall"\n',
        'x-a: &a "write\\x2dall"\npermissions: *a\n',
        'jobs:\n  a:\n    runs-on: x\n    permissions:\n      checks: "\\x77rite"\n',
    ):
        r = _power_rc(".github/workflows/new.yml", "name: N\n" + body)
        assert r.returncode == 1 and "merge-lane" in r.stdout, (body, r.stdout)


def test_r6_g2_computed_secret_access_is_power():
    for body in (
        "env:\n  T: ${{ secrets[format('{0}', 'SIBLING_READ_TOKEN')] }}\n",
        "env:\n  T: ${{ toJSON(secrets) }}\n",
        "env:\n  T: ${{ secrets.GITHUB_TOKENX }}\n",
        'env:\n  T: ${{ secrets[ "X" ] }}\n',
    ):
        r = _power_rc(".github/workflows/new.yml", "name: N\n" + body)
        assert r.returncode == 1 and "merge-lane" in r.stdout, (body, r.stdout)
    for ok in (
        "env:\n  T: ${{ secrets.GITHUB_TOKEN }}\n",
        "env:\n  T: ${{ secrets['GITHUB_TOKEN'] }}\n",
    ):
        assert (
            _power_rc(".github/workflows/new.yml", "name: N\n" + ok).returncode == 0
        ), ok


def test_r6_g2_unparseable_yaml_is_power():
    r = _power_rc(".github/workflows/new.yml", "name: N\npermissions: [unclosed\n")
    assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout
    r = _power_rc(".github/workflows/new.yml", "- just\n- a list\n")
    assert r.returncode == 1, r.stdout


def test_r6_g3_only_security_events_is_exempt():
    for scope in ("id-token", "attestations"):
        r = _power_rc(
            ".github/workflows/new.yml", f"name: N\npermissions:\n  {scope}: write\n"
        )
        assert r.returncode == 1, (scope, r.stdout)
    ok = "name: N\npermissions:\n  contents: read\n  security-events: write\n"
    assert _power_rc(".github/workflows/new.yml", ok).returncode == 0
    assert c.NON_MERGE_WRITE_SCOPES == frozenset({"security-events"})
    # PR #778 (Lean CI; ci.yml grants security-events: write for CodeQL) stays housekeeping
    assert _scoped(HVR_NILD, HK, PR778_FILES, head_root=REPO).returncode == 0


def test_r6_g5_composite_helper_files():
    import shutil
    import tempfile

    d = tempfile.mkdtemp()
    try:
        os.makedirs(os.path.join(d, ".github", "actions", "m"))
        with open(os.path.join(d, ".github", "actions", "m", "action.yml"), "w") as fh:
            fh.write("runs:\n  using: composite\n  steps:\n    - run: ./run.sh\n")
        with open(os.path.join(d, ".github", "actions", "m", "run.sh"), "w") as fh:
            fh.write("echo hi\n")
        helper = [".github/actions/m/run.sh"]
        # plain action + plain helper → housekeeping
        assert _scoped(HVR_NILD, HK, helper, head_root=d).returncode == 0
        # helper itself gains a merge verb → lane
        with open(os.path.join(d, ".github", "actions", "m", "run.sh"), "w") as fh:
            fh.write("gh pr merge 1\n")
        assert _scoped(HVR_NILD, HK, helper, head_root=d).returncode == 1
        # helper plain again, but the enclosing action.yml is powerful → lane
        with open(os.path.join(d, ".github", "actions", "m", "run.sh"), "w") as fh:
            fh.write("echo hi\n")
        with open(os.path.join(d, ".github", "actions", "m", "action.yml"), "w") as fh:
            fh.write(
                "runs:\n  using: composite\n  steps:\n    - run: gh issue close 1\n"
            )
        assert _scoped(HVR_NILD, HK, helper, head_root=d).returncode == 1
        # a file under .github/actions/ with no enclosing action file → fail closed
        os.makedirs(os.path.join(d, ".github", "actions", "orphan"))
        with open(os.path.join(d, ".github", "actions", "orphan", "x.sh"), "w") as fh:
            fh.write("echo hi\n")
        orphan = [".github/actions/orphan/x.sh"]
        assert _scoped(HVR_NILD, HK, orphan, head_root=d).returncode == 1
    finally:
        shutil.rmtree(d)


def test_r6_g6_actions_fail_closed_when_derivation_fails():
    # kills F3b: derivation None → a changed composite action is lane even when
    # its head copy has no power
    import shutil
    import tempfile

    head = _head_with(".github/actions/x/action.yml", "runs:\n  using: composite\n")
    root = tempfile.mkdtemp()
    old, c._HEAD_ROOT = c._HEAD_ROOT, head
    try:
        assert c.workflow_scripts(root) is None
        assert c.touches_lane([".github/actions/x/action.yml"], root=root)
        assert not c.touches_lane([".github/actions/x/action.yml"])
    finally:
        c._HEAD_ROOT = old
        shutil.rmtree(head)
        shutil.rmtree(root)


def test_r7_read_is_bounded_and_oversize_fails_closed():
    """2026-11-26 host OOM: _read must never slurp a whole file. Over
    MAX_READ_BYTES → None (power / lane); at the limit → read normally."""
    import shutil
    import tempfile

    d = tempfile.mkdtemp()
    try:
        big = os.path.join(d, "big.yml")
        with open(big, "w") as fh:
            fh.write("# x\n" * (c.MAX_READ_BYTES // 4 + 8))
        assert c._read(big) is None
        ok = os.path.join(d, "ok.yml")
        with open(ok, "w") as fh:
            fh.write("a" * c.MAX_READ_BYTES)
        assert c._read(ok) == "a" * c.MAX_READ_BYTES
    finally:
        shutil.rmtree(d)
    # an oversized, otherwise harmless head workflow counts as lane
    body = "name: N\n" + "# padding\n" * (c.MAX_READ_BYTES // 10 + 8)
    r = _power_rc(".github/workflows/new.yml", body)
    assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout[:300]


def test_r7_symlink_to_harmless_file_is_still_lane():
    """Kills P7 without any endless device: a symlinked workflow is lane by the
    islink guard alone, even when its target is a small, powerless file."""
    import shutil
    import tempfile

    d = tempfile.mkdtemp()
    try:
        wf = os.path.join(d, ".github", "workflows")
        os.makedirs(wf)
        with open(os.path.join(d, "plain.yml"), "w") as fh:
            fh.write("name: plain\npermissions:\n  contents: read\n")
        os.symlink(os.path.join(d, "plain.yml"), os.path.join(wf, "z.yml"))
        r = _scoped(HVR_NILD, HK, [".github/workflows/z.yml"], head_root=d)
        assert r.returncode == 1 and "merge-lane" in r.stdout, r.stdout
    finally:
        shutil.rmtree(d)


# ---- verdict source: the judge is the BASE copy, never the PR head (arch §I4, PR #780)

import merge_blocking_verdict_source as vs  # noqa: E402

SELECTOR = os.path.join(HERE, "merge_blocking_verdict_source.py")
WORKFLOW = os.path.join(
    os.path.dirname(HERE), ".github", "workflows", "merge-blocking-boxes.yml"
)
TAMPERED_CHECK = (
    "#!/usr/bin/env python3\n"
    "import sys\n"
    "print('unticked=0 ticked=0 nil=0 region=present')\n"
    "sys.exit(0)  # a 'simplified' check that always passes\n"
)


def _tree(root, files):
    """Create `root/scripts/<name>` for each (name, text) pair."""
    os.makedirs(os.path.join(root, "scripts"), exist_ok=True)
    for name, text in files.items():
        with open(os.path.join(root, "scripts", name), "w", encoding="utf-8") as fh:
            fh.write(text)


def _real(name):
    return open(os.path.join(HERE, name), encoding="utf-8").read()


def _run_selector(base, head, env_extra=None):
    env = dict(os.environ)
    env.pop("GITHUB_OUTPUT", None)
    env.update(env_extra or {})
    return subprocess.run(
        [sys.executable, SELECTOR, "--base", base, "--head", head],
        capture_output=True,
        text=True,
        env=env,
    )


def test_verdict_source_prefers_base_when_both_exist():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        both = {
            n: _real(n)
            for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
        }
        _tree(base, both)
        _tree(head, both)
        assert vs.select(base, head) == ("base", base, [])
        out = os.path.join(d, "gh_out")
        r = _run_selector(base, head, {"GITHUB_OUTPUT": out})
        assert r.returncode == 0, r.stdout + r.stderr
        assert (
            "verdict-source=base" in r.stdout and "::warning::" not in r.stdout
        ), r.stdout
        assert open(out).read() == f"source=base\ndir={base}\n", open(out).read()


def test_verdict_source_bootstraps_to_head_only_when_base_lacks_a_script():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(base, {"pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py")})
        _tree(
            head,
            {
                n: _real(n)
                for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
            },
        )
        src, chosen, missing = vs.select(base, head)
        assert (src, chosen, missing) == (
            "head(bootstrap)",
            head,
            ["scripts/merge_blocking_check.py"],
        )
        r = _run_selector(base, head)
        assert (
            r.returncode == 0 and "verdict-source=head(bootstrap)" in r.stdout
        ), r.stdout
        assert (
            "::warning::" in r.stdout and "scripts/merge_blocking_check.py" in r.stdout
        ), r.stdout


def test_verdict_source_fails_closed_when_neither_can_judge():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(base, {})
        _tree(head, {"pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py")})
        r = _run_selector(base, head)
        assert r.returncode == 1 and "::error::" in r.stdout, r.stdout


def test_head_side_edit_cannot_flip_the_verdict():
    """A PR that 'simplifies' the check to always-pass is still judged by the base copy."""
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(
            base,
            {
                n: _real(n)
                for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
            },
        )
        _tree(
            head,
            {
                "merge_blocking_check.py": TAMPERED_CHECK,
                "pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py"),
            },
        )
        src, chosen, _ = vs.select(base, head)
        assert src == "base" and chosen == base
        judge = os.path.join(chosen, "scripts", "merge_blocking_check.py")
        r = subprocess.run(
            [sys.executable, judge], input=ONE_UNTICKED, capture_output=True, text=True
        )
        assert (
            r.returncode == 1 and "::error::unticked merge-blocking box" in r.stdout
        ), r.stdout
        # the tampered head copy WOULD have passed — which is exactly why it must not judge
        tampered = os.path.join(head, "scripts", "merge_blocking_check.py")
        t = subprocess.run(
            [sys.executable, tampered],
            input=ONE_UNTICKED,
            capture_output=True,
            text=True,
        )
        assert t.returncode == 0, t.stdout


def test_workflow_runs_the_verdict_from_the_base_checkout():
    """Wiring guard: the YAML checks out base.sha into base/ and the verdict uses the selected dir."""
    import yaml

    wf = yaml.safe_load(open(WORKFLOW, encoding="utf-8"))
    steps = wf["jobs"]["merge-blocking-boxes"]["steps"]
    base_co = [
        s
        for s in steps
        if s.get("uses", "").startswith("actions/checkout")
        and s.get("with", {}).get("path") == "base"
    ]
    assert len(base_co) == 1, steps
    assert (
        base_co[0]["with"]["ref"] == "${{ github.event.pull_request.base.sha }}"
    ), base_co
    sel = [s for s in steps if s.get("id") == "src"]
    assert len(sel) == 1 and "merge_blocking_verdict_source.py" in sel[0]["run"], steps
    verdict = steps[-1]
    assert "merge_blocking_check.py" in verdict["run"], verdict
    assert (
        verdict["run"]
        .strip()
        .startswith('python3 "$SRC_DIR/scripts/merge_blocking_check.py"')
    ), verdict
    assert verdict["env"]["SRC_DIR"] == "${{ steps.src.outputs.dir }}", verdict
    # no step runs the verdict from a bare head path
    for s in steps:
        run = s.get("run", "")
        assert "python3 scripts/merge_blocking_check.py" not in run, s


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
