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

NATIVE = "native_decide"
TD = "token-declaring command (notation/infix/prefix/postfix/syntax/macro/elab/…), lexer code (interim ban, #836)"
TDL = "token-declaring command at a line start, raw-text fallback (interim ban, #836)"
RAW = 'raw string literal r"…" / r#"…"# (lexer-approximated; write an ordinary string)'
CHR = "char literal (lexer-approximated; use a string or Char.ofNat)"
GLU = "identifier character, quote, « or ` glued directly after a number (put a space between)"
BRACE = "brace inside a string literal (possible interpolation; write \\x7B / \\x7D)"
_R0 = {"sorry": 0, "vacuous-`: True :=` theorem": 0}
# exact (exit, non-zero hard-ban counts, ratchet counts) for the original CASES, in order
CASE_COUNTS = [
    (1, {NATIVE: 1}, _R0),
    (1, {NATIVE: 1}, _R0),
    (1, {BRACE: 1}, _R0),
    (1, {CHR: 1}, {"sorry": 1, "vacuous-`: True :=` theorem": 0}),
    (0, {}, _R0),
    (0, {}, _R0),
    (0, {}, _R0),
]
# PR #829 Red Team: inline must-reject / must-pass cases with EXACT counts
# (name, source, exit, non-zero hard-ban counts, ratchet counts).
INLINE_CASES = [
    (
        'Red Team f1: raw string r#"a"/-"# then native_decide (verbatim repro)',
        'def s : String := r#"a"/-"#\ntheorem t : 1 = 1 := by native_decide\ndef u : String := "-/"\n',
        1,
        {NATIVE: 1, RAW: 1},
        {"sorry": 0},
    ),
    (
        "Red Team f2: guillemet idents «x/-» … «-/» around native_decide (verbatim repro)",
        "def «x/-» : Nat := 1\ntheorem t : 1 = 1 := by native_decide\ndef «-/» : Nat := 2\n",
        1,
        {NATIVE: 1},
        {"sorry": 0},
    ),
    (
        "M21: `-- /-` is a LINE comment, so native_decide on the next line is code",
        "-- /-\ntheorem t : 1 = 1 := by native_decide\n-- -/\n",
        1,
        {NATIVE: 1},
        {"sorry": 0},
    ),
    (
        "M19: char '\"' then a real block comment holding native_decide (lexed right: only the char is refused)",
        'def c : Char := \'"\'\n/- native_decide -/\ndef d : String := "x"\n',
        1,
        {CHR: 1},
        {"sorry": 0},
    ),
    (
        'Gemini r1 (3) verbatim class: char literal \'"\' then a string "/-" then native_decide',
        'def q : Char := \'"\'\ndef s : String := "/-"\ntheorem t : 1 = 1 := by native_decide\n'
        'def u : String := "-/"\n',
        1,
        {NATIVE: 1, CHR: 1},
        {"sorry": 0},
    ),
    (
        "field index `h.1.symm` is not a number: nothing glued, must pass",
        "theorem t (h : 1 = 1 ∧ 2 = 2) : 1 = 1 := h.1.symm.symm\n",
        0,
        {},
        {"sorry": 0},
    ),
    (
        "numbers of every Lean form, unglued: must pass",
        "def a : Nat := 0x1F + 0b101 + 0o17 + 1_000\ndef b : Float := 1.5e-3 + 2.0 + 3e2\n",
        0,
        {},
        {"sorry": 0},
    ),
    (
        "Red Team r5: every token-declaring form (attribute-prefixed, local, scoped, private) refused",
        '@[inherit_doc] local notation "q1" => (1 : Nat)\n'
        'scoped infixl:65 " +++ " => Nat.add\n'
        'private syntax "qq" : term\n'
        "macro_rules | `(qq) => `(1)\n"
        'elab "ee" : term => pure (Lean.mkNatLit 1)\n'
        "declare_syntax_cat qcat\n"
        'prefix:max "√√" => Nat.succ\n'
        'postfix:max "!!" => Nat.succ\n'
        'macro "mm" : term => `(2)\n',
        1,
        {TD: 9, TDL: 9},
        {"sorry": 0},
    ),
]


def run_src(src: str) -> tuple[int, dict, dict]:
    sys.path.insert(0, str(HERE))
    import check_lean_foundations as clf  # noqa: E402

    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "X.lean").write_text(src, encoding="utf-8")
        hard, ratchet, _ = clf.scan(d)
    rc, _ = run_case(src)
    return rc, {k: v for k, v in hard.items() if v}, ratchet


FIXTURES = HERE / "lean_lexer_fixtures" / "LexFix"
VAC = "vacuous-`: True :=` theorem"
AMB = "comment opener `--`/`/-` not at a line start or after whitespace (put a space before it)"
# PR #829 Gemini r1 findings 2/3 (+ the same desync class). Each file is real Lean (the Lean-side
# self-test `test_lean_axiom_audit.py` compiles it and checks that Lean sees `vac` as a
# declaration). Expected = (exit code, the EXACT non-zero hard-ban counts, the EXACT ratchet
# counts), never wording. Under the first lexer every must-fail file except CharEsc passed
# with vacuous count 0 — `vac` was hidden in a fake comment.
LEXER_FIXTURES = [
    ("Raw.lean", 1, {RAW: 1}, {VAC: 1, "sorry": 0}),
    ("RawHashes.lean", 1, {RAW: 1}, {VAC: 1, "sorry": 0}),
    ("CharPrime.lean", 1, {TD: 1, TDL: 1}, {VAC: 1, "sorry": 0}),
    ("CharEsc.lean", 1, {CHR: 7}, {VAC: 1, "sorry": 0}),
    ("Guillemet.lean", 1, {}, {VAC: 1, "sorry": 0}),
    # The lexer cannot know Lean's token table: `//-` is refused outright (and `vac` is not
    # counted, because to the lexer it IS inside the comment — the refusal is what fails it).
    ("Ambig.lean", 1, {AMB: 1}, {VAC: 0, "sorry": 0}),
    # Red Team r2 finding 5 (T5, T6): a token may START with `(` or U+00A0 — only Lean
    # whitespace and line starts are clean boundaries.
    ("GluedParen.lean", 1, {AMB: 1, TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
    ("GluedNbsp.lean", 1, {AMB: 1, TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
    # Raw strings and char literals are HARD-BANNED in the scanned tree since PR #829 Gemini r2
    # (0 in proofs/QBP/Foundations): LegitRaw is lexed correctly (no fake comment, nothing
    # counted) but refused for exactly its 2 raw strings and 1 char literal.
    ("LegitRaw.lean", 1, {RAW: 2, CHR: 1, TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
    # PR #829 Gemini r2 finding 1 (same lexer-gap class as PR #824 T89/T90): a raw string or
    # char literal glued after a hex / scientific number. Lexed per Lean's `numberFnAux`,
    # `vac` is code (counted), and the glued token and the literal are each refused.
    ("NumHexRaw.lean", 1, {RAW: 1, GLU: 1}, {VAC: 1, "sorry": 0}),
    ("NumHexChar.lean", 1, {CHR: 1, GLU: 1}, {VAC: 1, "sorry": 0}),
    ("NumSciRaw.lean", 1, {RAW: 1, GLU: 1}, {VAC: 1, "sorry": 0}),
    ("NumNotation.lean", 1, {RAW: 1, GLU: 1, TD: 1, TDL: 1}, {VAC: 1, "sorry": 0}),
    # PR #829 Red Team r5 finding 1: a file-declared token holding a quote. The lexer IS fooled
    # (`vac` hidden: vacuous count 0), which is exactly why the token-declaring command itself
    # is refused, by the lexer-code match AND by the raw-text fallback (1 each).
    ("A1TokQuote.lean", 1, {TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
    ("A1x22.lean", 1, {TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
    ("A2TokSym.lean", 1, {TD: 1, TDL: 1}, {VAC: 0, "sorry": 0}),
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
    # PR #829 Gemini r2 finding 7: these original cases now assert the EXACT exit code and
    # counts (the wording check is kept only as a readable second condition).
    for (name, src, must_reject, want), (w_rc, w_hard, w_ratchet) in zip(
        CASES, CASE_COUNTS
    ):
        rc, out = run_case(src)
        _, hard, ratchet = run_src(src)
        good = (
            rc == w_rc
            and rc == int(must_reject)
            and hard == w_hard
            and ratchet == w_ratchet
            and (want in out if must_reject else True)
        )
        print(("ok  " if good else "FAIL") + f" {name} (exit {rc}, hard {hard})")
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
    for name, src, want_rc, want_hard, want_ratchet in INLINE_CASES:
        rc, hard, ratchet = run_src(src)
        ratchet = {k: v for k, v in ratchet.items() if k in want_ratchet}
        good = rc == want_rc and hard == want_hard and ratchet == want_ratchet
        print(("ok  " if good else "FAIL") + f" {name}: exit {rc}, hard {hard}")
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
