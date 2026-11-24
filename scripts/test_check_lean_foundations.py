#!/usr/bin/env python3
"""Planted tests for the Lean foundations gate's lexer (QBP #827 AC1).

Each case writes a tiny .lean tree into a temp dir and runs `check_lean_foundations.py` on
it with a zero baseline. Cases that MUST be rejected are the escapes found in PR #824
(KL03 "/-" string trick, nested-comment exposure, interpolation desync); cases that MUST
pass are legitimate code the old regex mis-handled. Also unit-checks `lean_lexer` itself.
Exit 0 = all cases behave; 1 = a regression.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECKER = HERE / "check_lean_foundations.py"
sys.path.insert(0, str(HERE))
from lean_lexer import brace_in_string, code_only, strip_comments  # noqa: E402

# (name, source, must_reject, expected substring in the checker output or "")
CASES = [
    (
        "KL03 string trick: native_decide after a string containing a comment opener",
        'def opener : String := "/-"\n'
        "theorem t : (List.range 10).sum = 45 := by\n  native_decide\n"
        "/- a trailing comment -/\n",
        True,
        "HARD-BAN violated — native_decide",
    ),
    (
        "native_decide after a NESTED comment (old regex ended the comment early)",
        "/- outer /- inner -/ still comment -/\ntheorem t : 1 = 1 := by native_decide\n",
        True,
        "HARD-BAN violated — native_decide",
    ),
    (
        "interpolation desync: s! hole holding a comment opener, then native_decide",
        'def evil : String := s!" { " /- " } "\ntheorem t : 1 = 1 := by native_decide\n',
        True,
        "HARD-BAN violated — brace inside a string literal",
    ),
    (
        "sorry hidden after a char literal '\"' (must still be counted)",
        "def q : Char := '\"'\ntheorem t : 1 = 2 := by sorry\n",
        True,
        "RATCHET violated — sorry: 1 > baseline 0",
    ),
    (
        "native_decide INSIDE a nested comment is a comment (must pass)",
        "/- outer /- inner -/ native_decide still commented -/\ntheorem t : 1 = 1 := rfl\n",
        False,
        "",
    ),
    (
        "comment markers and words inside a plain string are not code (must pass)",
        'def s : String := "-- not a comment /- nor this"\ntheorem t : 1 = 1 := rfl\n',
        False,
        "",
    ),
    (
        "escaped brace via \\x7B is allowed (must pass)",
        'def s : String := "\\x7B\\"p\\": 1\\x7D"\ntheorem t : 1 = 1 := rfl\n',
        False,
        "",
    ),
]


FIXTURES = HERE / "lean_lexer_fixtures" / "LexFix"
VAC = "vacuous-`: True :=` theorem"
AMB = "comment opener `--`/`/-` glued to a symbol character (put a space before it)"
# PR #829 Gemini r1 findings 2/3 (+ the same desync class). Each file is real Lean (the Lean-side
# self-test `test_lean_axiom_audit.py` compiles it and checks that Lean sees `vac` as a
# declaration). Expected = (exit code, the EXACT non-zero hard-ban counts, the EXACT ratchet
# counts), never wording. Under the first lexer every must-fail file except CharEsc passed
# with vacuous count 0 — `vac` was hidden in a fake comment.
LEXER_FIXTURES = [
    ("Raw.lean", 1, {}, {VAC: 1, "sorry": 0}),
    ("RawHashes.lean", 1, {}, {VAC: 1, "sorry": 0}),
    ("CharPrime.lean", 1, {}, {VAC: 1, "sorry": 0}),
    ("CharEsc.lean", 1, {}, {VAC: 1, "sorry": 0}),
    ("Guillemet.lean", 1, {}, {VAC: 1, "sorry": 0}),
    # The lexer cannot know Lean's token table: `//-` is refused outright (and `vac` is not
    # counted, because to the lexer it IS inside the comment — the refusal is what fails it).
    ("Ambig.lean", 1, {AMB: 1}, {VAC: 0, "sorry": 0}),
    ("LegitRaw.lean", 0, {}, {VAC: 0, "sorry": 0}),
]


def run_fixture(name: str) -> tuple[int, dict, dict]:
    sys.path.insert(0, str(HERE))
    import check_lean_foundations as clf  # noqa: E402

    with tempfile.TemporaryDirectory() as d:
        (Path(d) / name).write_text(
            (FIXTURES / name).read_text(encoding="utf-8"), encoding="utf-8"
        )
        hard, ratchet, _ = clf.scan(d)
        rc, _ = run_case((FIXTURES / name).read_text(encoding="utf-8"))
    return rc, {k: v for k, v in hard.items() if v}, ratchet


def run_case(src: str) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "X.lean").write_text(src, encoding="utf-8")
        base = Path(d) / "zero.json"
        base.write_text(json.dumps({"sorry": 0, "vacuous-`: True :=` theorem": 0}))
        r = subprocess.run(
            [sys.executable, "-I", str(CHECKER), "--dir", d, "--baseline", str(base)],
            capture_output=True,
            text=True,
        )
        return r.returncode, r.stdout + r.stderr


def main() -> int:
    bad = 0
    # lexer unit checks: length/newlines preserved, nesting, strings, char literals
    src = (
        'a /- x /- y -/ #print axioms ghost -/ b\nc -- d\n"/- not" e\n\'"\' f /- z -/ g'
    )
    s = strip_comments(src)
    ok = (
        len(s) == len(src)
        and s.count("\n") == src.count("\n")
        and "ghost" not in s
        and '"/- not"' in s
        and "g" in s
    )
    ok = ok and "not" not in code_only(src) and brace_in_string('x := "{"') == [1]
    print(("ok  " if ok else "FAIL") + " lexer unit checks")
    bad += not ok
    for name, src, must_reject, want in CASES:
        rc, out = run_case(src)
        good = (rc == 1 and want in out) if must_reject else rc == 0
        print(("ok  " if good else "FAIL") + f" {name} (exit {rc})")
        if not good:
            print("     " + out.replace("\n", "\n     ")[:800])
            bad += 1
    for name, want_rc, want_hard, want_ratchet in LEXER_FIXTURES:
        rc, hard, ratchet = run_fixture(name)
        good = rc == want_rc and hard == want_hard and ratchet == want_ratchet
        print(
            ("ok  " if good else "FAIL")
            + f" lexer fixture {name}: exit {rc}, hard {hard}, ratchet {ratchet}"
        )
        bad += not good
    # unit checks of the token rules themselves (PR #829)
    units = [
        ('r#" " /- "# x', "x"),  # raw string closes at "#, x is code
        ('r##" "# -- "## x', "x"),
        ("x'\"'/-\" x2", "x2"),  # x' is an identifier, "'/-" a string
        ("«/-» x3", "x3"),
        ("'\\x22' \"/-\" x4", "x4"),
        ('2r"/-" x5', "x5"),  # number 2, then a raw string
    ]
    for src, word in units:
        good = word in strip_comments(src) and len(strip_comments(src)) == len(src)
        print(
            ("ok  " if good else "FAIL") + f" lexer unit {src!r} keeps {word!r} as code"
        )
        bad += not good
    print("lexer/gate planted tests " + ("PASSED" if not bad else f"FAILED ({bad})"))
    return 1 if bad else 0


if __name__ == "__main__":
    os.environ.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    sys.exit(main())
