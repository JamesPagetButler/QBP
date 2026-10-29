#!/usr/bin/env python3
"""Tests for scripts/pr_box_evidence.py (#507 AC4 — comment-evidence vs unticked box).

Run: python3 scripts/test_pr_box_evidence.py   (or pytest -q)
Fixtures mirror the real posts on PR #780 (2026-10-27/28).
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pr_box_evidence as m  # noqa: E402

SCRIPT = os.path.join(HERE, "pr_box_evidence.py")
HEAD = "cdda215a0000000000000000000000000000beef"

BODY = """## Summary
PR B.

## Sign-off required (merge-blocking):

- [x] Red Team (Knuth · Sabine · Grothendieck) — APPROVE ([comment](https://x/1))
- [ ] Gemini review (`mcp__gemini__review_document`) — owed
- [ ] §I4 @qbp-architecture — contract co-sign of the parse

Informational readers (non-blocking):
- [ ] @qbp-oppenheimer — theory shape
"""

URL = "https://github.com/JamesPagetButler/QBP/pull/780#issuecomment-"


def _c(body, login="JamesPagetButler", when="2026-10-28T00:00:00Z", n="1"):
    return {
        "author": {"login": login},
        "body": body,
        "createdAt": when,
        "url": URL + n,
    }


def _r(body, state, login="JamesPagetButler", when="2026-10-28T00:00:00Z", n="r1"):
    return {
        "author": {"login": login},
        "body": body,
        "state": state,
        "submittedAt": when,
        "url": URL + n,
    }


ARCH_APPROVE = _c(
    "**§I4 contract co-sign — @qbp-architecture: APPROVE at head `486ad51`.** Item 1 fixed.",
    when="2026-10-28T00:14:01Z",
    n="6457064279",
)
GEMINI_DISPO = _c(
    "<!-- reviewed-sha: a0ca5625ab2b806173fdb4866a17f41b4397ed44 -->\n"
    "**VERDICT: APPROVE**\n"
    "**Disposition (qbp-oppenheimer):** NIT 1 — no action.\n"
    "Both review boxes (Red Team, Gemini) are now tickable; §I4 @qbp-architecture "
    "contract co-sign remains open — the check stays RED until it lands.",
    when="2026-10-27T23:55:17Z",
    n="6456591436",
)
ARCH_CHANGES = _c(
    "**§I4 contract co-sign — @qbp-architecture: CHANGES REQUESTED on one item. "
    "Reviewed at head `a0ca562`. Box left unticked.**",
    when="2026-10-27T23:59:51Z",
    n="6456699519",
)
NOTIFIER = _c(
    "<!-- pr-check-status-notifier -->\n## 🟡 CI GREEN — 2 boxes unticked\n"
    "- ⏸ §I4 @qbp-architecture — contract co-sign\nIf a posted APPROVE covers a box, cite it.",
    login="github-actions",
    n="6456526919",
)


def _detect(comments=(), reviews=(), body=BODY, head=HEAD):
    return m.detect(body, {"comments": list(comments), "reviews": list(reviews)}, head)


# ── box → hand ─────────────────────────────────────────────────────────────


def test_box_hand_handle_role_none():
    assert m.box_hand("§I4 @qbp-architecture — co-sign") == (
        "handle",
        "qbp-architecture",
    )
    assert m.box_hand("Gemini review (real API)") == ("role", "gemini")
    assert m.box_hand("Red Team (Sabine/Grothendieck/Knuth)") == ("role", "red-team")
    assert m.box_hand("Human Visual Review (beekeeper)") == (None, None)


def test_only_unticked_boxes_are_assessed_via_the_shared_parser():
    r = _detect()
    assert [b["text"] for b in r["boxes"]] == [
        "Gemini review (`mcp__gemini__review_document`) — owed",
        "§I4 @qbp-architecture — contract co-sign of the parse",
    ], r
    assert r["region"] == "present"


# ── evidence detection ─────────────────────────────────────────────────────


def test_persona_approve_in_body_same_line_is_evidence_with_differing_sha():
    r = _detect([ARCH_APPROVE])
    arch = r["boxes"][1]
    assert arch["evidence"] is not None, arch
    assert arch["evidence"]["url"].endswith("6457064279")
    assert arch["evidence"]["sha"] == "486ad51"
    assert arch["evidence"]["sha_vs_head"] == "differs"
    assert r["with_evidence"] == 1


def test_approve_elsewhere_with_handle_on_another_line_is_not_evidence():
    # PR #780 Gemini disposition: APPROVE on one line, "@qbp-architecture ... remains
    # open" on another — must NOT be cited for the architect's box.
    r = _detect([GEMINI_DISPO])
    assert r["boxes"][1]["evidence"] is None, r["boxes"][1]


def test_changes_requested_is_not_evidence():
    r = _detect([ARCH_CHANGES])
    assert r["boxes"][1]["evidence"] is None


def test_negated_same_line_approve_is_not_evidence():
    c = _c("APPROVE pending — @qbp-architecture co-sign requested at head `486ad51`.")
    assert _detect([c])["boxes"][1]["evidence"] is None


def test_notifier_and_bot_posts_are_never_evidence():
    r = _detect(
        [NOTIFIER, _c("APPROVE @qbp-architecture", login="github-actions[bot]")]
    )
    assert all(b["evidence"] is None for b in r["boxes"]), r


def test_author_login_match_counts_anywhere_in_body():
    c = _c(
        "<!-- reviewed-sha: cdda215a0000000000000000000000000000beef -->\n"
        "Verdict: APPROVE-WITH-CONCERN (one NOTE).",
        login="qbp-architecture",
    )
    ev = _detect([c])["boxes"][1]["evidence"]
    assert ev and ev["sha_vs_head"] == "same" and ev["sha"] == HEAD


def test_review_state_approved_by_author_is_evidence_without_approve_text():
    rv = _r("looks right to me", "APPROVED", login="qbp-architecture")
    ev = _detect(reviews=[rv])["boxes"][1]["evidence"]
    assert ev and ev["kind"] == "review" and ev["sha_vs_head"] == "unknown"


def test_review_state_commented_is_not_evidence():
    rv = _r("@qbp-architecture APPROVE", "COMMENTED", login="JamesPagetButler")
    # state COMMENTED, but the body line itself carries handle + APPROVE → evidence
    # by the body rule; a review that neither is APPROVED nor says APPROVE is not.
    assert _detect(reviews=[rv])["boxes"][1]["evidence"] is not None
    rv2 = _r("@qbp-architecture looked, no verdict yet", "COMMENTED")
    assert _detect(reviews=[rv2])["boxes"][1]["evidence"] is None


def test_role_fallback_for_handleless_gemini_box_is_comment_level():
    # Tier-3 gate rule: signature (header line) + verdict in the SAME post.
    c = _c("## Gemini review (Furey/Feynman)\n\n**Verdict: APPROVE** at `cdda215`.")
    gem = _detect([c])["boxes"][0]
    assert gem["evidence"] and gem["evidence"]["sha_vs_head"] == "same"
    # a verdict with no role signature anywhere is not evidence for a role box
    assert (
        _detect([_c("**Verdict: APPROVE** at `cdda215`.")])["boxes"][0]["evidence"]
        is None
    )
    # the Red Team review does not count for the Gemini box
    rt = _c("## Red Team — PR #780 — round 1\n\n**Verdict: APPROVE**")
    assert _detect([rt])["boxes"][0]["evidence"] is None


def test_lead_line_hand_preferred_over_passing_mention():
    # PR #780 live case: the (newer) Gemini disposition says "Both review boxes
    # (Red Team, Gemini) are now tickable" + VERDICT: APPROVE, and both posts carry
    # the same reviewed-sha marker — the Red Team box must cite the Red Team review.
    red_team_body = "## Sign-off required (merge-blocking):\n- [ ] Red Team (Sabine/Grothendieck/Knuth)\n"
    rt = _c(
        "<!-- reviewed-sha: a0ca5625ab2b806173fdb4866a17f41b4397ed44 -->\n"
        "## Red Team — PR #780 (self-review) — round 1\n| S1 | Sabine | x | fixed |\n"
        "**Verdict: APPROVE-WITH-CONCERN → after `a0ca562`, APPROVE**",
        when="2026-10-27T23:54:18Z",
        n="6456570515",
    )
    gem = _c(
        "<!-- reviewed-sha: a0ca5625ab2b806173fdb4866a17f41b4397ed44 -->\n"
        "## Gemini review — PR #780\n**VERDICT: APPROVE**\n"
        "Both review boxes (Red Team, Gemini) are now tickable.",
        when="2026-10-27T23:55:17Z",
        n="6456591436",
    )
    box = _detect([gem, rt], body=red_team_body)["boxes"][0]
    assert box["posts"] == 2
    assert box["evidence"]["url"].endswith("6456570515"), box
    assert m._hand_in_lead_line(rt, "role", "red-team") is True
    assert m._hand_in_lead_line(gem, "role", "red-team") is False
    assert m._hand_in_lead_line(ARCH_APPROVE, "handle", "qbp-architecture") is True


def test_marked_review_preferred_over_newer_unmarked_summary():
    review = _c(
        "<!-- reviewed-sha: a0ca5625ab2b806173fdb4866a17f41b4397ed44 -->\n"
        "## Gemini review (Furey/Feynman)\n**VERDICT: APPROVE**",
        when="2026-10-27T23:55:17Z",
        n="review",
    )
    merge_note = _c(
        "Merge. Gate snapshot at head `cdda215`: Red Team + Gemini + arch §I4 APPROVE.",
        when="2026-10-28T07:07:56Z",
        n="merge",
    )
    gem = _detect([merge_note, review])["boxes"][0]
    assert gem["posts"] == 2
    assert gem["evidence"]["url"].endswith("review"), gem
    assert gem["evidence"]["sha"] == "a0ca5625ab2b806173fdb4866a17f41b4397ed44"


def test_newest_of_several_candidates_is_cited_and_counted():
    older = _c(
        "§I4 @qbp-architecture: APPROVE at `a0ca562`",
        when="2026-10-27T20:00:00Z",
        n="old",
    )
    r = _detect([older, ARCH_APPROVE])
    arch = r["boxes"][1]
    assert arch["posts"] == 2
    assert arch["evidence"]["url"].endswith("6457064279")
    assert arch["evidence"]["sha"] == "486ad51"


# ── sha extraction ─────────────────────────────────────────────────────────


def test_cited_sha_marker_beats_loose_and_loose_forms_work():
    p = {"body": "at `a0ca562` <!-- reviewed-sha: 486ad51f1085 -->"}
    assert m.cited_sha(p) == "486ad51f1085"
    assert m.cited_sha({"body": "APPROVE @ a0ca562 thanks"}) == "a0ca562"
    assert m.cited_sha({"body": "APPROVE at head sha cdda215."}) == "cdda215"
    assert m.cited_sha({"body": "APPROVE, no sha here"}) is None
    assert m.sha_vs_head("cdda215", HEAD) == "same"
    assert m.sha_vs_head("486ad51", HEAD) == "differs"
    assert m.sha_vs_head(None, HEAD) == "unknown"


# ── output shapes ──────────────────────────────────────────────────────────


def test_human_lines_keep_plain_nudge_line_when_no_evidence():
    r = _detect([ARCH_APPROVE])
    lines = m.human_lines(r)
    assert lines[0] == "- ⏸ Gemini review (`mcp__gemini__review_document`) — owed"
    assert lines[1].startswith(
        '- 🟡 box "§I4 @qbp-architecture" is UNTICKED but an APPROVE was posted ('
    )
    assert "reviewed-sha 486ad51 ≠ head cdda215" in lines[1]
    assert "re-reviews at head" in lines[1]
    assert "never auto-tick" in lines[1]


def test_human_line_same_sha_asks_only_for_the_tick():
    c = _c("§I4 @qbp-architecture: APPROVE at `cdda215`.")
    line = m.human_lines(_detect([c]))[1]
    assert "reviewed-sha cdda215 = head" in line and "re-reviews" not in line


def test_human_line_without_sha_says_so():
    c = _c("§I4 @qbp-architecture: APPROVE.")
    line = m.human_lines(_detect([c]))[1]
    assert "no reviewed-sha cited — confirm it covers head cdda215" in line


def test_machine_lines_contract():
    out = m.machine_lines(_detect([ARCH_APPROVE]))
    assert out[0] == f"boxes=2 with_evidence=1 head={HEAD}"
    assert out[1] == "NOEVIDENCE box=1 hand=gemini"
    assert out[2].startswith("EVIDENCE box=2 hand=@qbp-architecture url=")
    assert "sha=486ad51 sha_vs_head=differs posts=1" in out[2]


def test_no_unticked_boxes_or_absent_region_yield_empty_lists():
    r = _detect(body="## Sign-off required (merge-blocking):\n- [x] @a\n")
    assert r["boxes"] == [] and m.human_lines(r) == []
    r2 = _detect(body="no region at all\n- [ ] @qbp-architecture\n")
    assert r2["region"] == "absent" and r2["boxes"] == []


def test_box_label_shortens_long_box_text():
    long = "§I4 @qbp-architecture — " + "x" * 200
    assert m.box_label(long) == "§I4 @qbp-architecture"
    assert m.box_label("@a " + "y" * 100).endswith("…")
    assert len(m.box_label("@a " + "y" * 100)) <= m.BOX_LABEL_MAX


def test_bare_list_is_read_as_comments():
    r = m.detect(BODY, [ARCH_APPROVE], HEAD)
    assert r["boxes"][1]["evidence"] is not None


def test_cli_human_and_machine_modes():
    with tempfile.TemporaryDirectory() as d:
        bf, cf = os.path.join(d, "body.md"), os.path.join(d, "c.json")
        with open(bf, "w", encoding="utf-8") as fh:
            fh.write(BODY)
        with open(cf, "w", encoding="utf-8") as fh:
            json.dump({"comments": [ARCH_APPROVE, GEMINI_DISPO], "reviews": []}, fh)
        base = [sys.executable, SCRIPT, "--body", bf, "--comments", cf, "--head", HEAD]
        p = subprocess.run(base, capture_output=True, text=True)
        assert p.returncode == 0, p.stderr
        # GEMINI_DISPO is the Gemini verdict (role rule) and NOT the architect's
        # co-sign (same-line rule) → 2 boxes, both with evidence, different posts
        assert p.stdout.splitlines()[0] == f"boxes=2 with_evidence=2 head={HEAD}"
        assert "EVIDENCE box=1 hand=gemini url=" in p.stdout
        assert "6456591436 sha=a0ca5625" in p.stdout
        assert "EVIDENCE box=2 hand=@qbp-architecture url=" in p.stdout
        assert "6457064279 sha=486ad51" in p.stdout
        h = subprocess.run(base + ["--human"], capture_output=True, text=True)
        assert h.returncode == 0 and h.stdout.count("\n") == 2
        assert "- ⏸" not in h.stdout and h.stdout.count("🟡 box") == 2
        j = subprocess.run(base + ["--json"], capture_output=True, text=True)
        assert json.loads(j.stdout)["with_evidence"] == 2


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
