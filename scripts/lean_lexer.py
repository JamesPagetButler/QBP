"""Lean 4 comment lexer shared by the Lean CI gate scripts (QBP issue #827, AC1).

`strip_comments(src)` blanks out Lean comments and returns a string of EXACTLY the same
length, with every newline kept, so line/column positions in the result equal those in the
source. Unlike a regex it follows Lean's lexical rules:

  * block comments `/- … -/` NEST (depth-counted): a non-greedy `/-.*?-/` would end the
    comment at its first inner closer and expose the rest as "code";
  * `--` starts a line comment;
  * string literals ("…", with backslash escapes) are skipped, so a `"/-"` or `"--"` inside
    a string neither opens a comment nor hides the code after it — the hole in #827: the old
    `re.sub(r"/-.*?-/", …)` deleted everything from a `"/-"` string to the next closer,
    so a `native_decide` in that span passed the HARD-BAN;
  * a char literal such as '"' is skipped (it does not open a string).

Provenance: a reviewed COPY of the lexer in `tools/lean-toolcheck/toolcheck.py` (PR #824,
Gemini (6) + r2 (c)); `lex`/`strip_comments`/`code_only`/`brace_in_string` are identical in
logic. It is copied, not shared, because PR #824 is not merged; once both land, the toolcheck
grader should import this module (one lexer, one place to fix).

SUPPORTED SUBSET: string interpolation (`s!"…{e}…"`, and the implicit interpolation of
`throwError "…{e}…"` / `m!` / `f!`) is not lexed. `brace_in_string` reports every string
literal containing a brace; the foundations checker HARD-BANs those (none exist in
proofs/QBP/Foundations, 2026-11-20), which makes the simple string rule exact there.
Out of scope (documented limit): raw string literals `r"…"`/`r#"…"#` are lexed as ordinary
strings; QBP uses none (grep, 2026-11-20).
"""

from __future__ import annotations


def lex(src: str) -> str:
    """Classify every character of a Lean source: 'c' code, 'm' comment, 's' string body.

    The returned string has the same length as `src` (one class letter per character).
    Rules (Gemini (6) and r2 (c) on PR #824):
      * `/- … -/` block comments NEST (depth-counted) — a non-greedy regex would end at the
        first inner closer and expose the rest as "code";
      * `--` runs to end of line;
      * "…" string literals with backslash escapes; the quotes themselves are 'c', the body
        is 's'; a char literal such as '"' or '\\"' does not open a string.
    SUPPORTED SUBSET: the lexer does NOT model string interpolation (`s!"…{e}…"`, and the
    implicit interpolation of `throwError "…{e}…"` / `m!` / `f!`). Instead `brace_in_string`
    reports any `{` or `}` inside a string body, and the grader REFUSES such a file — every
    interpolation needs a brace inside the first string segment, so refusing braces makes the
    simple string rule exact for every file the grader accepts (write a literal brace as
    "\\x7B" / "\\x7D"). See must-fail MF08.
    """
    cls: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if depth > 0:
            if two in ("/-", "-/"):
                depth += 1 if two == "/-" else -1
                cls.append("mm")
                i += 2
            else:
                cls.append("m")
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                cls.append("ss")
                i += 2
                continue
            if c == '"':
                in_str = False
                cls.append("c")
            else:
                cls.append("s")
            i += 1
        elif two == "/-":
            depth = 1
            cls.append("mm")
            i += 2
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            cls.append("m" * (j - i))
            i = j
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\\":
            cls.append("ccc")  # char literal such as '"' — not a string opener
            i += 3
        elif c == "'" and i + 3 < n and src[i + 1] == "\\" and src[i + 3] == "'":
            cls.append("cccc")  # escaped char literal such as '\\"'
            i += 4
        else:
            if c == '"':
                in_str = True
            cls.append("c")
            i += 1
    return "".join(cls)[:n]


def _render(src: str, keep: str) -> str:
    """Characters whose class is in `keep` are kept; others become spaces (newlines kept)."""
    k = lex(src)
    return "".join(ch if (cl in keep or ch == "\n") else " " for ch, cl in zip(src, k))


def strip_comments(src: str) -> str:
    """Comments blanked (strings kept), same length / lines / columns as the source."""
    return _render(src, "cs")


def code_only(src: str) -> str:
    """Comments AND string bodies blanked — used to find `#print axioms` sites, so a
    `"#print axioms x"` inside a string is never taken for a command."""
    return _render(src, "c")


def brace_in_string(src: str) -> list[int]:
    """1-based line numbers of string literals containing `{` or `}` (possible interpolation)."""
    k = lex(src)
    lines = set()
    for idx, (ch, cl) in enumerate(zip(src, k)):
        if cl == "s" and ch in "{}":
            lines.add(src.count("\n", 0, idx) + 1)
    return sorted(lines)
