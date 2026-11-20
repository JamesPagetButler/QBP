#!/usr/bin/env python3
"""Fail CI if a gated Agda proof file contains a forbidden escape token.

Why (QBP#823, G1 from the PR #825 Red Team): `agda --safe` is the Agda
completeness gate, but the pinned Agda release accepts a `postulate` written
inside a `let` under `--safe` (agda/agda#8341). Until the pin moves past the
fix, this lexical check closes that gap in CI. It also backs up `--safe` for
the other escapes.

What it does: scans the **raw** text, with no comment stripping. A
comment-aware scanner was bypassed twice in review (PR #826 Red Team: a
string literal opening a fake `{-`, and an identifier like `a--b` read as
a line comment). Raw scanning has no lexer to get wrong. The cost is one
convention: never write a forbidden token in a gated file, even in a
comment.

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


def scan_text(text: str) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(text.splitlines(), 1):
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
    # The two PR #826 Red Team bypasses of the old comment-aware scanner.
    "B1_string_fake_comment": 's = "{-"\nf = let postulate p : ⊥ in p\nt = "-}"\n',
    "B2_identifier_dashdash": "f = let a--b = tt ; postulate p : ⊥ in p\n",
    "in_comment": "-- postulate\nx = tt\n",
}
SELF_TEST_MUST_PASS = {
    "safe_options": "{-# OPTIONS --cubical --safe --guardedness #-}\nmodule X where\n",
    "identifier": "postulated-free = tt\n",
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
