"""Tests for scripts/agda_forbidden_tokens.py (QBP#823 G1)."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agda_forbidden_tokens as aft  # noqa: E402


def test_self_test_clean():
    assert aft.self_test() == []


def test_let_postulate_is_flagged():
    assert aft.scan_text("f = let postulate p : ⊥ in p\n") == [(1, "postulate")]


def test_options_flag_seen_despite_double_dash():
    hits = aft.scan_text("{-# OPTIONS --cubical --safe --type-in-type #-}\n")
    assert (1, "--type-in-type") in hits


def test_comments_are_ignored():
    src = "-- postulate\n{- postulate {- TERMINATING -} -}\nx = tt\n"
    assert aft.scan_text(src) == []


def test_line_numbers_survive_block_comments():
    src = "{- one\ntwo -}\nf = primTrustMe\n"
    assert aft.scan_text(src) == [(3, "primTrustMe")]


def test_main_exit_codes(tmp_path):
    good = tmp_path / "Good.agda"
    good.write_text("{-# OPTIONS --cubical --safe #-}\nmodule Good where\n")
    assert aft.main(["x", str(tmp_path)]) == 0
    (tmp_path / "Bad.agda").write_text("module Bad where\npostulate p : Set\n")
    assert aft.main(["x", str(tmp_path)]) == 1
    assert aft.main(["x"]) == 2
