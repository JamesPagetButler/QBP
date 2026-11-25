#!/usr/bin/env python3
"""Lean foundations gate — enforces the zero-sorry / no-vacuous-stub / no-native_decide
standard on proofs/QBP/Foundations/** (issue #481; policy: inter/lean-proof-best-practices.md
Rule 4 + docs/foundations/scope-deliberation-2026-05-31.md).

Two enforcement tiers:

  HARD-BAN (zero tolerance, any occurrence fails):
    - native_decide          — trusted-compiler escape; kernel `decide` only
    - `: True := by trivial`  — the vacuous-proof cardinal sin (the archive octonionMul
                                pattern: a named theorem that proves only True)
    - brace inside a string   — possible string interpolation, which the lexer does not
                                model (#827): banned so the lexer stays exact
    - `//-`, `<--`, …         — a comment opener glued to a symbol character, which Lean's
                                extensible symbol tokens may read as code (#829): banned

  RATCHET (baseline count in .lean-gate-baseline.json; must not INCREASE):
    - sorry                   — honest unproven placeholder; allowed in the skeleton but
                                may only go down (Phase-2..4 proofs replace stubs)
    - vacuous `: True :=` thm — a theorem typed `True` asserts nothing; the breakdown
                                ✗-cells must become real statements (scope-deliberation
                                exit gate), so this count must only go down

Comments are stripped before matching (doc-comments legitimately mention "sorry") by the
shared Lean lexer `scripts/lean_lexer.py` (#827 AC1, #829): a token walk following Lean's
tokenizer — nested block comments depth-counted; string, raw-string (`r#"…"#`) and char
literals and identifiers (incl. `x'`, `«…»`) skipped. Matching is TOKEN-level only — whether a theorem really
avoids `sorryAx` / native axioms is decided by the CI axiom audit (`gen_lean_axiom_audit.py` +
`check_lean_axiom_audit.py`), which asks Lean, not this script.

Usage: check_lean_foundations.py [--dir proofs/QBP/Foundations] [--baseline <path>] [--update-baseline]
Exit 0 = pass, 1 = violation.
"""

import argparse
import glob
import json
import os
import re
import sys

HARD_BAN = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "vacuous-proof `: True := by trivial`": re.compile(
        r":\s*True\s*:=\s*by\s+trivial\b"
    ),
}
RATCHET = {
    "sorry": re.compile(r"\bsorry\b"),
    "vacuous-`: True :=` theorem": re.compile(r":\s*True\s*:="),
}


# #827 AC1: comments are stripped by a real Lean lexer (nesting depth-counted, string and
# char literals skipped) shared with the axiom-audit script — NOT a regex. The old
# `re.sub(r"/-.*?-/", …)` ignored strings, so after a `"/-"` string it deleted everything up
# to the next `-/`, and a `native_decide` in that span passed the HARD-BAN (PR #824 KL03).
# `-I` (isolated) callers do not get this script's directory on sys.path, so add it here.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_lexer import (
    ambiguous_comment_openers,
    brace_in_string,
    code_only,
    literal_sites,
    strip_comments,
)  # noqa: E402  (after the sys.path fix)

# The lexer does not model string interpolation (`s!"…{e}…"`, `throwError "…{e}…"`): an
# interpolation hole can hold a string with a comment opener (`s!" { " /- " } "`) that would
# desynchronise it from Lean and hide the code after it. Every interpolation needs a brace in
# a string literal, so a brace inside a string is HARD-BANNED in the scanned tree (0 in
# proofs/QBP/Foundations on 2026-11-20): with it banned, the simple string rule is exact.
BRACE_IN_STRING = (
    "brace inside a string literal (possible interpolation; write \\x7B / \\x7D)"
)
# Lean checks for `--` / `/-` only at a token boundary, and the symbol-token table is extensible
# by any import, so a comment opener glued to a symbol character (`//-`, `<--`) may be code to
# Lean. Banned (0 in all of proofs/ on 2026-11-24) so the lexer never has to guess (PR #829).
# PR #829 Gemini r2 finding 1 (same lexer-gap class as PR #824's T89/T90): around raw strings,
# char literals and numbers a lexer can only approximate Lean's tokenizer. The scanned tree
# uses NONE of them (2026-11-25: 0 raw strings and 0 char literals in proofs/QBP/Foundations;
# across all 80 proofs/ files 0 raw strings, 5 char literals in the two Oracle files, 0 glued
# numbers), so they are HARD-BANNED there, as PR #824 r5 bans raw strings. The lasting fix is to
# run this gate on Lean's own parser (PR #824 r5 `LeanSubsetParse`), scheduled in the #836 build.
RAW_STRING = (
    'raw string literal r"…" / r#"…"# (lexer-approximated; write an ordinary string)'
)
CHAR_LITERAL = "char literal (lexer-approximated; use a string or Char.ofNat)"
GLUED_NUMBER = "identifier character, quote, « or ` glued directly after a number (put a space between)"
# PR #829 Red Team r5 (finding 1, reproduced on Lean 4.30): a file can DECLARE a token that
# contains a quote (`notation "zz\"" x => x`, a symbol atom `⟪\"`, or the escape `\x22`). Lean then
# reads `zz"` as one token while the lexer opens a string, desyncs into a fake comment and hides a
# vacuous theorem. INTERIM fix: HARD-BAN every token-declaring command in the scanned tree (0 in
# proofs/QBP/Foundations and 0 in all of proofs/ on 2026-11-25). Under the beekeeper's QBP#836
# ruling ("allow pure syntax macros", AC1b), PR A replaces this ban with the Lean-parser check,
# which permits pure notation and macros whose expansions stay in the subset; tokens declared by
# IMPORTED modules are an open case in that PR's scope. Matched twice: on the lexer's code (comments
# and strings blanked) AND on raw text per line, because the lexer is what such a file fools.
_TOKEN_KW = (
    r"(?:notation3?|infixl|infixr|infix|prefix|postfix|syntax|macro_rules|macro|"
    r"elab_rules|elab|declare_syntax_cat)"
)
TOKEN_DECL_CODE = re.compile(r"(?<![\w.'!?«])" + _TOKEN_KW + r"(?![\w'!?])")
TOKEN_DECL_RAW = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)?"
    r"(?:(?:local|scoped)\s+)?" + _TOKEN_KW + r"\b",
    re.MULTILINE,
)
TOKEN_DECL = "token-declaring command (notation/infix/prefix/postfix/syntax/macro/elab/…), lexer code (interim ban, #836)"
TOKEN_DECL_LINE = (
    "token-declaring command at a line start, raw-text fallback (interim ban, #836)"
)
AMBIGUOUS_OPENER = "comment opener `--`/`/-` not at a line start or after whitespace (put a space before it)"


def scan(lean_dir):
    hard = {k: 0 for k in HARD_BAN}
    hard[BRACE_IN_STRING] = 0
    hard[AMBIGUOUS_OPENER] = 0
    for k in (RAW_STRING, CHAR_LITERAL, GLUED_NUMBER, TOKEN_DECL, TOKEN_DECL_LINE):
        hard[k] = 0
    ratchet = {k: 0 for k in RATCHET}
    hard_hits = []
    for path in sorted(
        glob.glob(os.path.join(lean_dir, "**", "*.lean"), recursive=True)
    ):
        with open(path, encoding="utf-8") as f:
            raw = f.read()
        code = strip_comments(raw)
        for name, rx in HARD_BAN.items():
            n = len(rx.findall(code))
            hard[name] += n
            if n:
                hard_hits.append((path, name, n))
        for name, fn in (
            (BRACE_IN_STRING, brace_in_string),
            (AMBIGUOUS_OPENER, ambiguous_comment_openers),
            (RAW_STRING, lambda t: literal_sites(t)["raw"]),
            (CHAR_LITERAL, lambda t: literal_sites(t)["char"]),
            (GLUED_NUMBER, lambda t: literal_sites(t)["glued_number"]),
            (TOKEN_DECL, lambda t: TOKEN_DECL_CODE.findall(code_only(t))),
            (TOKEN_DECL_LINE, lambda t: TOKEN_DECL_RAW.findall(t)),
        ):
            nb = len(fn(raw))
            hard[name] += nb
            if nb:
                hard_hits.append((path, name, nb))
        for name, rx in RATCHET.items():
            ratchet[name] += len(rx.findall(code))
    return hard, ratchet, hard_hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="proofs/QBP/Foundations")
    ap.add_argument(
        "--baseline", default="proofs/QBP/Foundations/.lean-gate-baseline.json"
    )
    ap.add_argument(
        "--update-baseline",
        action="store_true",
        help="rewrite the baseline to current counts (use ONLY when intentionally reducing)",
    )
    args = ap.parse_args()

    hard, ratchet, hard_hits = scan(args.dir)

    if args.update_baseline:
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump(ratchet, f, indent=2, sort_keys=True)
            f.write("\n")
        print(f"baseline updated: {ratchet}")
        return 0

    failed = False

    # HARD bans
    for name, count in hard.items():
        if count:
            print(
                f"::error::HARD-BAN violated — {name}: {count} occurrence(s) in {args.dir}"
            )
            failed = True
    for path, name, n in hard_hits:
        print(f"::error file={path}::{n}× {name}")

    # RATCHET
    try:
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f)
    except FileNotFoundError:
        print(
            f"::error::baseline {args.baseline} missing — run with --update-baseline to create it"
        )
        return 1

    for name, count in ratchet.items():
        base = baseline.get(name, 0)
        if count > base:
            print(
                f"::error::RATCHET violated — {name}: {count} > baseline {base}. "
                f"New {name} is not allowed; the count may only decrease."
            )
            failed = True
        elif count < base:
            print(
                f"::warning::{name} decreased {base} → {count}. "
                f"Run check_lean_foundations.py --update-baseline and commit the lowered baseline."
            )
        else:
            print(f"ok: {name} at baseline ({count})")

    if failed:
        print(
            "\nLean foundations gate FAILED. Policy: inter/lean-proof-best-practices.md Rule 4."
        )
        return 1
    print("\nLean foundations gate PASSED.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
