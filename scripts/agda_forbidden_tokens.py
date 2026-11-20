#!/usr/bin/env python3
"""Fail CI if a gated Agda proof file contains a forbidden escape token.

Why (QBP#823, G1 from the PR #825 Red Team): `agda --safe` is the Agda
completeness gate, but the pinned Agda release accepts a `postulate` written
inside a `let` under `--safe` (agda/agda#8341). Until the pin moves past the
fix, this lexical check closes that gap in CI. It also backs up `--safe` for
the other escapes.

What it does:
- strips `{- ... -}` block comments (nested), but keeps `{-# ... #-}` pragmas;
- strips `--` line comments outside pragmas, so `{-# OPTIONS --type-in-type #-}`
  is still seen;
- reports every forbidden token with file:line.

A built-in must-hit self-test runs first, so a check that silently stopped
matching fails loudly instead of reporting "0 hits".

Usage: python3 scripts/agda_forbidden_tokens.py <dir-or-file> [...]
Exit: 0 clean, 1 forbidden token found, 2 self-test failed or bad usage.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# Keyword-like tokens matched as whole words.
WORD_TOKENS = [
    "postulate",
    "primTrustMe",
    "primEraseEquality",
    "REWRITE",
    "TERMINATING",
    "NON_TERMINATING",
    "NO_POSITIVITY_CHECK",
    "NO_UNIVERSE_CHECK",
    "NON_COVERING",
    "INJECTIVE",
]
# Flags matched as `--flag` (they only make sense inside OPTIONS pragmas).
FLAG_TOKENS = [
    "type-in-type",
    "rewriting",
    "allow-unsolved-metas",
    "allow-incomplete-matches",
    "no-positivity-check",
    "no-termination-check",
    "omega-in-omega",
]

_WORD_RE = re.compile(r"(?<![\w'])(" + "|".join(WORD_TOKENS) + r")(?![\w'])")
_FLAG_RE = re.compile(r"--(" + "|".join(FLAG_TOKENS) + r")\b")
_HOLE_RE = re.compile(r"\{!")


def strip_comments(text: str) -> str:
    """Remove comments, keeping pragmas and line structure (newlines kept)."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    in_pragma = False
    while i < n:
        two = text[i : i + 2]
        if depth == 0 and not in_pragma and text.startswith("{-#", i):
            in_pragma = True
            out.append("{-#")
            i += 3
            continue
        if in_pragma:
            if text.startswith("#-}", i):
                in_pragma = False
                out.append("#-}")
                i += 3
                continue
            out.append(text[i])
            i += 1
            continue
        if two == "{-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if two == "-}":
                depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if two == "--" and _is_line_comment(text, i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def _is_line_comment(text: str, i: int) -> bool:
    # In Agda, `--` starts a comment unless it is part of a longer operator
    # name; a run of dashes followed by a symbol char is an operator.
    j = i
    while j < len(text) and text[j] == "-":
        j += 1
    nxt = text[j] if j < len(text) else "\n"
    prev = text[i - 1] if i > 0 else " "
    symbol = set("!#$%&*+./<=>?@\\^|~:")
    return prev not in symbol and nxt not in symbol


def scan_text(text: str) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(strip_comments(text).splitlines(), 1):
        for rx in (_WORD_RE, _FLAG_RE, _HOLE_RE):
            for m in rx.finditer(line):
                hits.append((lineno, m.group(0)))
    return hits


SELF_TEST_MUST_HIT = {
    "let_postulate": "f : ⊥\nf = let postulate p : ⊥ in p\n",
    "options_flag": "{-# OPTIONS --cubical --safe --type-in-type #-}\nmodule X where\n",
    "pragma": "{-# TERMINATING #-}\nloop : ⊥\nloop = loop\n",
    "erase": "x = primEraseEquality\n",
    "hole": "x : ⊤\nx = {! !}\n",
}
SELF_TEST_MUST_PASS = {
    "line_comment": "-- postulate in a comment is fine\nx = tt\n",
    "block_comment": "{- a postulate {- nested -} here -}\nx = tt\n",
    "safe_options": "{-# OPTIONS --cubical --safe --guardedness #-}\nmodule X where\n",
    "identifier": "postulated-free = tt\nmy-postulate' = tt\n",
}


def self_test() -> list[str]:
    errors = []
    for name, src in SELF_TEST_MUST_HIT.items():
        if not scan_text(src):
            errors.append(f"self-test must-hit '{name}' was NOT flagged")
    for name, src in SELF_TEST_MUST_PASS.items():
        if scan_text(src):
            errors.append(f"self-test must-pass '{name}' was flagged: {scan_text(src)}")
    return errors


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    errors = self_test()
    if errors:
        for e in errors:
            print(f"SELF-TEST FAIL: {e}", file=sys.stderr)
        return 2
    print(
        f"self-test ok ({len(SELF_TEST_MUST_HIT)} must-hit, {len(SELF_TEST_MUST_PASS)} must-pass)"
    )
    files: list[Path] = []
    for arg in argv[1:]:
        p = Path(arg)
        files.extend(sorted(p.rglob("*.agda")) if p.is_dir() else [p])
    files = [f for f in files if "_build" not in f.parts]
    total = 0
    for f in files:
        for lineno, tok in scan_text(f.read_text(encoding="utf-8")):
            print(f"FORBIDDEN {f}:{lineno}: {tok}")
            total += 1
    print(f"scanned {len(files)} file(s): {total} forbidden token(s)")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
