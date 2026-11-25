"""Lean 4 comment lexer shared by the Lean CI gate scripts (QBP issue #827, AC1).

`strip_comments(src)` blanks out Lean comments and returns a string of EXACTLY the same
length, with every newline kept, so line/column positions in the result equal those in the
source. It walks the source TOKEN BY TOKEN, following Lean 4.30's own tokenizer
(`Lean.Parser.Basic.tokenFnAux` / `whitespace`), not a regex:

  * block comments `/- … -/` NEST (depth-counted): a non-greedy `/-.*?-/` would end the
    comment at its first inner closer and expose the rest as "code";
  * `--` starts a line comment;
  * string literals "…" (backslash escapes) are skipped, so a `"/-"` or `"--"` inside a string
    neither opens a comment nor hides the code after it — the hole in #827: the old
    `re.sub(r"/-.*?-/", …)` deleted everything from a `"/-"` string to the next closer;
  * RAW string literals `r"…"`, `r#"…"#`, `r##"…"##`, … (any number of `#`, no escapes; the
    literal ends at the first `"` followed by the same number of `#`) — PR #829 Gemini r1
    finding 2: lexed as ordinary strings, `r#" " /- "#` closed at the inner `"` and opened a
    fake comment that hid the code after it;
  * CHAR literals, as Lean decides them: at a token start, `'` not followed by `'` begins a
    char literal — one character or an escape (`\\\\ \\" \\' \\r \\n \\t`, `\\xHH`, `\\uHHHH`)
    then `'` (PR #829 Gemini r1 finding 3);
  * IDENTIFIERS are consumed whole, including `'`, `!`, `?` and subscripts in the name, dotted
    parts and `«…»` escapes. This is what makes the char rule exact: in `x'"'/-"` the `'`
    belongs to the identifier `x'` and `"'/-"` is a STRING (no comment) — the first lexer took
    `'"'` for a char literal and opened a comment at `/-`. `«…»` may hold any character,
    including `"` and `/-`; name literals `` `foo `` are identifiers too;
  * a number is its decimal digits (`2r"x"` is the number 2 then a raw string, as in Lean).

What the lexer does NOT model (both fail CLOSED in the foundations checker, which HARD-BANs
them so the simple rules above are exact for every file it accepts):
  * string interpolation (`s!"…{e}…"`, `throwError "…{e}…"`, `m!`, `f!`):
    `brace_in_string` reports every string literal containing a brace;
  * Lean's longest-match SYMBOL tokens. Lean checks for `--` / `/-` only at a token boundary,
    so inside a multi-character symbol token the two characters do not open a comment (e.g.
    `//-` can be the token `//` then `-`, and `<--` can be `<-` then `-`). The token table is
    extensible by any import, so `ambiguous_comment_openers` reports every `--` / `/-` that
    is not at a clean token boundary (file start, Lean whitespace, or right after a comment)
    and the checker refuses the file (Red Team r2 finding 5: `(` and U+00A0 can start a token).


Provenance: started as a reviewed copy of the lexer in `tools/lean-toolcheck/toolcheck.py`
(PR #824, Gemini (6) + r2 (c)); PR #829 replaced the character loop with the token walk
above. Once both land, the toolcheck grader should import this module (one lexer, one place
to fix).
"""

from __future__ import annotations

# Lean's own whitespace (`Lean.Parser.whitespace`): the only characters after which a `--` /
# `/-` is certainly a comment opener (Red Team r2 finding 5).
_LEAN_WHITESPACE = set(" \t\r\n")
_QUOTABLE = set("\\\"'rnt")
_HEX = set("0123456789abcdefABCDEF")


def _is_letter_like(c: str) -> bool:
    # Exactly Lean 4.30 `isLetterLike` (Init/Meta/Defs.lean).
    o = ord(c)
    return (
        (0x3B1 <= o <= 0x3C9 and o != 0x3BB)  # lower Greek but λ
        or (0x391 <= o <= 0x3A9 and o != 0x3A0 and o != 0x3A3)  # upper Greek but Π Σ
        or (0x3CA <= o <= 0x3FB)  # Coptic
        or (0x1F00 <= o <= 0x1FFE)  # polytonic Greek
        or (0x2100 <= o <= 0x214F)  # letter-like block
        or (0x1D49C <= o <= 0x1D59F)  # script, double-struck, Fraktur
        or (0x00C0 <= o <= 0x00FF and o != 0xD7 and o != 0xF7)  # Latin-1 letters
        or (0x0100 <= o <= 0x017F)  # Latin Extended-A
    )


def _is_sub_script_alnum(c: str) -> bool:
    # Exactly Lean 4.30 `isSubScriptAlnum`.
    o = ord(c)
    return (
        (0x2080 <= o <= 0x2089)
        or (0x2090 <= o <= 0x209C)
        or (0x1D62 <= o <= 0x1D6A)
        or o == 0x2C7C
    )


def _id_first(c: str) -> bool:
    return (c.isascii() and c.isalpha()) or c == "_" or _is_letter_like(c)


def _id_rest(c: str) -> bool:
    return (
        (c.isascii() and c.isalnum())
        or c in "_'!?"
        or _is_letter_like(c)
        or _is_sub_script_alnum(c)
    )


def _raw_start(src: str, i: int) -> int:
    """If src[i] == 'r' starts a raw string `r#…#"`, return the number of `#`; else -1."""
    j = i + 1
    while j < len(src) and src[j] == "#":
        j += 1
    return j - i - 1 if j < len(src) and src[j] == '"' else -1


def _char_lit_end(src: str, i: int) -> int:
    """src[i] == "'": end index (exclusive) of a char literal there, or -1 if none."""
    n = len(src)
    j = i + 1
    if j >= n:
        return -1
    if src[j] == "\\":
        j += 1
        if j >= n:
            return -1
        if src[j] in _QUOTABLE:
            j += 1
        elif (
            src[j] == "x" and all(c in _HEX for c in src[j + 1 : j + 3]) and j + 3 <= n
        ):
            j += 3
        elif (
            src[j] == "u" and all(c in _HEX for c in src[j + 1 : j + 5]) and j + 5 <= n
        ):
            j += 5
        else:
            return -1
    else:
        j += 1
    return j + 1 if j < n and src[j] == "'" else -1


def _ident_end(src: str, i: int) -> int:
    """End index (exclusive) of the identifier starting at i (`_id_first` or `«`)."""
    n = len(src)
    j = i
    while True:
        if j < n and src[j] == "«":
            k = src.find("»", j + 1)
            j = n if k < 0 else k + 1
        else:
            j += 1
            while j < n and _id_rest(src[j]):
                j += 1
        if j + 1 < n and src[j] == "." and (_id_first(src[j + 1]) or src[j + 1] == "«"):
            j += 1
            continue
        return j


def lex(src: str) -> str:
    """Classify every character of a Lean source: 'c' code, 'm' comment, 's' string body.

    The returned string has the same length as `src` (one class letter per character). String
    and raw-string delimiters (`"`, `r#"`, `"#`) are 'c', their bodies 's'. Char literals and
    identifiers (including `«…»`) are 'c' — they never contain a comment or a string.
    """
    n = len(src)
    cls = ["c"] * n
    i = 0
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if two == "/-":
            depth, j = 1, i + 2
            while j < n and depth:
                t = src[j : j + 2]
                if t == "/-":
                    depth, j = depth + 1, j + 2
                elif t == "-/":
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            j = min(j, n)
            cls[i:j] = "m" * (j - i)
            i = j
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            cls[i:j] = "m" * (j - i)
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j, n)
            cls[i + 1 : j] = "s" * (j - i - 1)
            i = j + 1
        elif c == "r" and _raw_start(src, i) >= 0:
            h = _raw_start(src, i)
            body = i + 2 + h
            close = src.find('"' + "#" * h, body)
            j = n if close < 0 else close
            cls[body:j] = "s" * (j - body)
            i = n if close < 0 else close + 1 + h
        elif c == "'" and src[i + 1 : i + 2] != "'" and _char_lit_end(src, i) > 0:
            i = _char_lit_end(src, i)
        elif c == "'":
            i += 2 if src[i + 1 : i + 2] == "'" else 1  # the symbol `''` / a lone `'`
        elif c == "`" and i + 1 < n and (_id_first(src[i + 1]) or src[i + 1] == "«"):
            i = _ident_end(
                src, i + 1
            )  # name literal `foo — an identifier, no raw-string check
        elif _id_first(c) or c == "«":
            i = _ident_end(src, i)
        elif c.isascii() and c.isdigit():
            while i < n and src[i].isascii() and src[i].isdigit():
                i += 1
        else:
            i += 1
    return "".join(cls)


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


def ambiguous_comment_openers(src: str) -> list[int]:
    """1-based line numbers of comment openers (`--`, `/-`) that are NOT at a clean token boundary.

    Lean's `whitespace` function treats `--` / `/-` as a comment only where it is looking for
    whitespace: at the start of the file, after Lean whitespace (space, tab, CR, LF) or right
    after another comment. Anywhere else the two characters may continue a SYMBOL TOKEN, and any
    import (or the file itself) can declare one: `macro "(/-" : term` makes `(/-` code, and so
    does an atom starting with U+00A0, which is not Lean whitespace (PR #829 Red Team r2
    finding 5, probes T5/T6). So only those boundaries are exempt; every other opener is
    reported and the foundations checker refuses the file.
    """
    k = lex(src)
    lines = set()
    for idx in range(len(src)):
        if k[idx] != "m" or src[idx : idx + 2] not in ("--", "/-"):
            continue
        if idx == 0 or k[idx - 1] == "m" or src[idx - 1] in _LEAN_WHITESPACE:
            continue
        lines.add(src.count("\n", 0, idx) + 1)
    return sorted(lines)
