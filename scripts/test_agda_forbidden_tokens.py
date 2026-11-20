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


def test_red_team_bypasses_are_caught():
    b1 = 's = "{-"\nf = let postulate p : ⊥ in p\nt = "-}"\n'
    b2 = "f = let a--b = tt ; postulate p : ⊥ in p\n"
    assert (2, "postulate") in aft.scan_text(b1)
    assert (1, "postulate") in aft.scan_text(b2)


def test_raw_scan_flags_tokens_in_comments_too():
    assert aft.scan_text("-- postulate\n{- TERMINATING -}\n") == [
        (1, "postulate"),
        (2, "TERMINATING"),
    ]


def test_main_exit_codes(tmp_path):
    good = tmp_path / "Good.agda"
    good.write_text("{-# OPTIONS --cubical --safe #-}\nmodule Good where\n")
    assert aft.main(["x", str(tmp_path)]) == 0
    (tmp_path / "Bad.agda").write_text("module Bad where\npostulate p : Set\n")
    assert aft.main(["x", str(tmp_path)]) == 1
    assert aft.main(["x"]) == 2


def test_every_listed_token_has_a_per_token_self_test():
    listed = set(aft.WORD_TOKENS) | {"--" + f for f in aft.FLAG_TOKENS} | {"{!"}
    assert listed == set(aft.SELF_TEST_PER_TOKEN)


def test_dropping_a_token_fails_the_self_test(monkeypatch):
    # Mutation M5 from the PR #826 Red Team: remove one token from the list.
    import re

    words = [w for w in aft.WORD_TOKENS if w != "NO_POSITIVITY_CHECK"]
    monkeypatch.setattr(
        aft,
        "_WORD_RE",
        re.compile(r"(?<![\w'])(" + "|".join(words) + r")(?![\w'])"),
    )
    assert any("NO_POSITIVITY_CHECK" in e for e in aft.self_test())


def test_literate_and_build_dirs_are_scanned(tmp_path):
    # Gemini review on PR #826: literate Agda files and `_build/` sources
    # must not be skipped (both are importable).
    (tmp_path / "_build").mkdir()
    (tmp_path / "_build" / "Hidden.agda").write_text("x = primTrustMe\n")
    (tmp_path / "deep" / "er").mkdir(parents=True)
    (tmp_path / "deep" / "er" / "Lit.lagda.md").write_text(
        "```agda\npostulate p : Set\n```\n"
    )
    (tmp_path / "Old.lagda").write_text("\\begin{code}\nx = {! !}\n\\end{code}\n")
    (tmp_path / "Skip.agdai").write_text("postulate binary artefact")
    names = sorted(f.name for f in aft.collect_files([str(tmp_path)]))
    assert names == ["Hidden.agda", "Lit.lagda.md", "Old.lagda"]  # no .agda-lib here
    assert aft.main(["x", str(tmp_path)]) == 1


def test_agda_lib_include_outside_roots_is_flagged(tmp_path):
    root = tmp_path / "proofs"
    root.mkdir()
    (root / "ok.agda-lib").write_text("name: ok\ninclude: .\nflags: --cubical --safe\n")
    assert aft.main(["x", str(root)]) == 0
    (root / "bad.agda-lib").write_text("name: bad\ninclude: . ../elsewhere\n")
    assert aft.main(["x", str(root)]) == 1


def test_agda_lib_flags_are_scanned(tmp_path):
    (tmp_path / "f.agda-lib").write_text("name: f\ninclude: .\nflags: --type-in-type\n")
    assert aft.main(["x", str(tmp_path)]) == 1


def test_agda_lib_parser_matches_agda(tmp_path):
    # Gemini r2: spacing before the colon, comments and blank lines inside
    # a multi-line include must not hide entries.
    lib = tmp_path / "x.agda-lib"
    lib.write_text(
        "name: x\ninclude  : .\n  -- a comment\n\n  ../hidden\ndepend: cubical\n"
    )
    assert aft.agda_lib_includes(lib) == [".", "../hidden"]
    assert aft.include_escapes(lib, [tmp_path.resolve()]) == ["../hidden"]


def test_symlinks_under_gated_trees_are_forbidden(tmp_path):
    root = tmp_path / "proofs"
    root.mkdir()
    outside = tmp_path / "evil"
    outside.mkdir()
    (outside / "Hack.agda").write_text("x = primTrustMe\n")
    (root / "evil").symlink_to(outside, target_is_directory=True)
    assert aft.symlinks_under([str(root)]) == [root / "evil"]
    assert aft.main(["x", str(root)]) == 1
