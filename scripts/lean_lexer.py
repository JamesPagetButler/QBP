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

Provenance: this is a reviewed copy of the lexer in `tools/lean-toolcheck/toolcheck.py`
(PR #824, Gemini finding (6)); the two are byte-identical in logic. Once PR #824 merges, the
toolcheck grader should import this module instead of carrying its own copy (one lexer).
Out of scope (documented limit): raw string literals `r"…"`/`r#"…"#` are lexed as ordinary
strings; QBP uses none (grep, 2026-11-20).
"""

from __future__ import annotations


def strip_comments(src: str) -> str:
    """Blank out Lean comments, preserving length, newlines and columns."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                out.append(src[i : i + 2])
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append(c)
            i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\\":
            out.append(src[i : i + 3])  # char literal such as '"' — not a string opener
            i += 3
        elif c == "'" and i + 3 < n and src[i + 1] == "\\" and src[i + 3] == "'":
            out.append(src[i : i + 4])  # escaped char literal such as '\"' or '\n'
            i += 4
        else:
            if c == '"':
                in_str = True
            out.append(c)
            i += 1
    return "".join(out)
