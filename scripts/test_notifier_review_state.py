#!/usr/bin/env python3
"""QBP#706 — tests for scripts/notifier_review_state.py.

Run: python3 -m pytest scripts/test_notifier_review_state.py -v

Uses the real COMMENT_BOUNDARY / NOTIFIER_MARKER from check_tier3_label (the workflow's
comment-boundary mechanism), and KILLS the two mutants named in the issue: "always unticked"
and "always ticked".
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import notifier_review_state as nrs  # noqa: E402
from check_tier3_label import COMMENT_BOUNDARY, NOTIFIER_MARKER  # noqa: E402


def _blob(*comments: str) -> str:
    return COMMENT_BOUNDARY.join(comments)


def test_both_detected():
    """AC1: Red Team + Gemini artifacts present ⇒ both rows tick."""
    blob = _blob(
        "## Red Team Review (Sabine · Grothendieck · Knuth)\n… Verdict: APPROVE-WITH-NOTES",
        "## Gemini review (Furey/Feynman, real API) — APPROVE",
    )
    assert nrs.detect(blob) == (True, True)


def test_none_detected():
    """AC1: no review artifacts ⇒ neither ticks (mutant 'always ticked' dies here)."""
    blob = _blob("just a normal discussion comment", "rebased onto master")
    assert nrs.detect(blob) == (False, False)


def test_verdict_without_signature_does_not_tick():
    """A bare verdict with no reviewer signature is not a review."""
    assert nrs.detect(_blob("I think we should APPROVE this later")) == (False, False)


def test_signature_without_verdict_does_not_tick():
    """FAULT-S4-003 anti-rubber-stamp: a named-but-unrendered review does not count."""
    assert nrs.detect(
        _blob("Red Team review (Sabine/Grothendieck/Knuth) — pending")
    ) == (
        False,
        False,
    )


def test_notifier_comment_cannot_self_tick():
    """The notifier's own checklist names the reviewers but is NOTIFIER_MARKER-tagged, so it
    must be skipped — otherwise it would tick itself (the FAULT-S4-003 shape)."""
    blob = _blob(
        f"{NOTIFIER_MARKER}\n- [ ] Red Team review (Sabine/Grothendieck/Knuth) APPROVE\n"
        f"- [ ] Gemini review (Furey/Feynman) APPROVE"
    )
    assert nrs.detect(blob) == (False, False)


def test_carried_review_counts_like_fresh():
    """The re-land case (PR #705): a carried review is an ordinary non-notifier comment, so
    it counts the same as a fresh one."""
    blob = _blob("Carried from #702 — Gemini review (Furey/Feynman): APPROVE")
    assert nrs.detect(blob) == (False, True)


def test_one_of_two():
    """Independent rows: Red Team present, Gemini absent ⇒ (True, False)."""
    blob = _blob("Red Team (Knuth): REQUEST CHANGES", "thanks, will fix")
    assert nrs.detect(blob) == (True, False)


def test_mutant_always_unticked_killed():
    """Mutant KILLED: a detector hardwired to (False, False) fails on real artifacts."""
    blob = _blob("Red Team (Grothendieck) APPROVE", "Gemini (Feynman) APPROVE")
    assert nrs.detect(blob) != (False, False)


def test_mutant_always_ticked_killed():
    """Mutant KILLED: a detector hardwired to (True, True) fails on an empty PR."""
    assert nrs.detect(_blob("no reviews here")) != (True, True)
