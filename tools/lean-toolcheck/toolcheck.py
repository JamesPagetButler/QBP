#!/usr/bin/env python3
"""QBP Lean toolcheck — evaluator + helpers for run.sh (issue #823 W5).

Subcommands
  pins      --proofs DIR                  print toolchain, mathlib sha, sha7, manifest rev (shell-friendly)
  imports   --proofs DIR                  print the Mathlib modules QBP imports (comment-stripped, sorted)
  check-imports --proofs DIR --file F     exit 1 if F's import list != the live QBP Mathlib import set
  evaluate  --raw DIR --suite DIR --out-json F --out-md F [--meta F]
                                          grade every run against its TOOLCHECK-EXPECT lines

Expectation lines live in each .lean file's header comment:
  TOOLCHECK-EXPECT: pass                       VERDICT from the STRUCTURAL audit (`structural_audit`): no
                                               declaration of the freshly compiled .olean rests on an axiom
                                               outside the standard three. In addition (defense in depth):
                                               Lean exit 0, no error / sorry, every `#print axioms`
                                               result within {propext, Classical.choice, Quot.sound},
                                               EXACTLY one positioned axiom report per `#print axioms`
                                               site, no unpositioned axiom-like message, no non-Lean
                                               stdout line, the file inside the pass-file SUBSET, and
                                               the foundations checker accepts the file (fail-closed)
  TOOLCHECK-EXPECT: lean-ok                    Lean exit 0
  TOOLCHECK-EXPECT: lean-error <regex>         Lean exit != 0 and ONE error message, rendered
                                               `LINE:COL: error: TEXT`, matches <regex> (re.search
                                               on that single message — anchor with ^LINE:)
  TOOLCHECK-EXPECT: lean-output <regex>        ONE warning/information message, rendered
                                               `LINE:COL: warning: TEXT`, matches <regex>
  TOOLCHECK-EXPECT: axiom <thm> <axiom>        `#print axioms <thm>` lists <axiom>
  TOOLCHECK-EXPECT: axiom-nonstd <thm>         `#print axioms <thm>` lists at least one axiom outside
                                               {propext, Classical.choice, Quot.sound} (name-agnostic:
                                               the native-evaluation axiom's name changes in Lean v4.35.0)
  TOOLCHECK-EXPECT: checker-reject <regex>     check_lean_foundations.py (zero baseline) exits 1
                                               and ONE of its `::error::` lines matches <regex>
  TOOLCHECK-EXPECT: subset-refused             the file leaves the pass-file subset (subset_violations)
  TOOLCHECK-EXPECT: audit-nonstd <thm>         the STRUCTURAL audit (PR #829 auditor on a fresh .olean)
                                               reports a non-standard axiom on <thm>
  TOOLCHECK-EXPECT: audit-fails                the structural audit does not clear the file

  TOOLCHECK-EXPECT: known-limit checker-accepts            REPORT-ONLY: the checker exits 0 on the file
  TOOLCHECK-EXPECT: known-limit audit-clean <thm>          REPORT-ONLY: `#print axioms <thm>` is ⊆ std3
  TOOLCHECK-EXPECT: known-limit lean-error <regex>         REPORT-ONLY: Lean exits != 0 matching <regex>
      A known-limit row documents a gap the suite KNOWS it cannot catch (e.g. the vacuity
      check is syntactic). It is reported as "confirmed" or "changed" and never fails the
      suite; a "changed" row means the tool improved (or regressed) — read it at the bump.

A must-fail whose expected detection does not happen is a suite FAILURE. A Lean crash
(exit >= 128, e.g. 139 = SIGSEGV) is a FAILURE for every file and is never retried.
A toolcheck PASS is a statement about a SUPPORTED SUBSET of Lean, NOT an axiom certificate:
the sound audit is the out-of-process one (QBP#827 / PR #829). Lean is run with `--json`. An
axiom report counts only if it is an `information` message positioned exactly at a
`#print axioms <thm>` command for that <thm>, and reports merge worst-case (union), so printed
text (`#eval IO.println "'x' does not depend on any axioms"`) can neither add a clean report nor
clear a real one (MF06). Stdout is NOT a trusted channel: code the file defines or runs can write
to `/dev/stdout` and exit before Lean prints the real report (MF14-MF18). So a PASS file is
graded fail-closed: exactly one report per site, nothing unpositioned, nothing but Lean
messages, and the whole file inside the pass-file SUBSET (`subset_violations`: a top-level
command allowlist, `#print axioms` as the only `#` command, an attribute allowlist, and no
syntax-extension / handler / evaluation keyword anywhere). Sites are found ANYWHERE on a line (MF07) in source with
comments and string bodies blanked by a nesting-aware lexer (T19). Lines are counted Lean's
way — bytes read, only `\\r\\n` -> `\\n`, split at `\\n` only (MF10/MF11). COVERAGE: the audit covers
exactly the `#print axioms` sites this lexer finds; the suite convention is ONE site per
theorem. The lexer does not model string interpolation, so a file with a brace inside a string
literal is REFUSED (MF08; `TOOLCHECK-EXPECT: grader-refuses` marks a must-fail that expects
it). This script never treats `#eval` output as proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# [ \t] not \s: a `\s*` here would run across the newline and swallow the NEXT expectation
# line into this one's argument (caught on the first suite run: MF02's axiom check vanished).
EXPECT_RE = re.compile(r"^TOOLCHECK-EXPECT:[ \t]*(\S+)[ \t]*(.*?)[ \t]*$", re.MULTILINE)
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.DOTALL)
NOAXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
# Lean 4.30 prints "declaration uses `sorry`" (backticks); older toolchains used 'sorry' (quotes).
SORRY_WARN_RE = re.compile(r"declaration uses [`']sorry[`']")
# ---- the pass-file SUBSET: DEFENSE IN DEPTH, not the soundness boundary -----------------------
# Director ruling after Red Team r3 on PR #824: three rounds (T80-T85) show token rules cannot be
# closed, so a pass file's AXIOM VERDICT comes from the structural audit (`structural_audit`: the
# PR #829 auditor on an .olean compiled in a fresh process), never from the file's own output.
# The subset stays as a second, independent layer. It is checked on the code-only text
# (comments and string bodies blanked by `lex`, so neither can trigger or hide a rule), one
# `\n`-line at a time; every violation is tagged with its rule:
#   A. a code line that starts in COLUMN 0 starts a command: after any leading `@[...]` its first
#      word must be in SUBSET_COMMANDS; `noncomputable` must be `noncomputable def`.
#   H. EVERY command keyword at ANY position (indented, after a term, after `… in`) must be in
#      SUBSET_COMMANDS. The keyword set is Lean's own: the leading tokens of the `command` syntax
#      category with Lean + the T00 import surface loaded (`command_heads.json`, generated by
#      `gen_command_heads.py` and pinned to the toolchain and Mathlib sha).
#   I. an `open … in` / `set_option … in` combinator must be followed by an allowed command: on
#      the same line, or on the next code line, which must start in column 0.
#   B. a `#word` token ANYWHERE must be `#print axioms`.
#   C. every `@[...]` ANYWHERE must close on its line and list only SUBSET_ATTRIBUTES items,
#      each optionally prefixed by `scoped` (so no handler attribute, at any position).
#   D. no SUBSET_DENY_WORDS token ANYWHERE (syntax extension, handler registration, `attribute`,
#      `axiom`, simprocs, code-evaluating commands/tactics).
# The allowlists are the MINIMUM the 20 tool tests need. LIMIT: a text scan cannot see a
# command with no first token (`unindexed_command_parsers` in command_heads.json) or one that a
# module outside the T00 surface adds. A toolcheck PASS is NOT an axiom certificate on its own
# terms either: the sound audit is QBP#827 / PR #829, which this suite now calls.
SUBSET_COMMANDS = (
    "import",
    "namespace",
    "end",
    "open",
    "variable",
    "set_option",
    "theorem",
    "def",
    "noncomputable",
    "instance",
    "structure",
    "inductive",
    "#print",
)
SUBSET_ATTRIBUTES = (
    "simp",
    "ext",
)
SUBSET_DENY_WORDS = (
    "attribute",
    "macro",
    "macro_rules",
    "syntax",
    "declare_syntax_cat",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "elab",
    "elab_rules",
    "run_cmd",
    "run_elab",
    "run_meta",
    "run_tac",
    "by_elab",
    "initialize",
    "builtin_initialize",
    "implemented_by",
    "extern",
    "unsafe",
    "native_decide",
    "+native",
    "ofReduceBool",
    "reduceBool",
    "plausible",
    "slim_check",
    "axiom",
    "simproc",
    "dsimproc",
    "simproc_decl",
    "dsimproc_decl",
)
_ATTR_PREFIXES = ("scoped",)
_HEADS_FILE = Path(__file__).resolve().parent / "command_heads.json"


def load_command_heads() -> tuple[frozenset[str], dict]:
    """Lean's command keywords (rule H) and the pins they were generated under."""
    try:
        d = json.loads(_HEADS_FILE.read_text())
    except (OSError, ValueError):
        return frozenset(), {}
    return frozenset(d.get("word_heads", [])), d


COMMAND_HEADS, COMMAND_HEADS_META = load_command_heads()


def _blank_attr_lists(ln: str) -> str:
    """`@[...]` spans replaced by spaces (rule C checks them; their items are not commands)."""
    return re.sub(r"@\[[^\]]*\]", lambda m: " " * len(m.group(0)), ln)


_WORD = re.compile(r"#?[A-Za-z_][A-Za-z0-9_!?.']*")


def subset_violations(src: str) -> list[str]:
    """Every way `src` leaves the pass-file subset, each tagged `[A]`…`[H]`; empty = inside it."""
    out: list[str] = []
    lines = lean_lines(code_only(src))
    for i, ln in enumerate(lines, start=1):
        if ln and not ln[0].isspace():  # A: a top-level command starts here
            rest = ln
            while True:
                m = re.match(r"@\[[^\]]*\][ \t]*", rest)
                if not m:
                    break
                rest = rest[m.end() :]
            toks = rest.split()
            if toks:
                head, nxt = toks[0], (toks[1] if len(toks) > 1 else "")
                if head not in SUBSET_COMMANDS:
                    out.append(
                        f"[A] l.{i}: top-level `{head}` is not an allowed command"
                    )
                elif head == "noncomputable" and nxt != "def":
                    out.append(
                        f"[A] l.{i}: `noncomputable {nxt}` (only `noncomputable def`)"
                    )
            if toks and toks[0] in ("open", "set_option"):  # I
                k = rest.find(" in ") if " in " in rest else -1
                if rest.rstrip().endswith(" in"):
                    k = len(rest.rstrip()) - 3
                if k >= 0:
                    after = rest[k + 4 :].split()
                    if after:
                        if after[0] not in SUBSET_COMMANDS:
                            out.append(
                                f"[I] l.{i}: `… in {after[0]}`: not an allowed command"
                            )
                    else:
                        nxt_ln = next((x for x in lines[i:] if x.strip()), "")
                        if nxt_ln[:1].isspace():
                            out.append(
                                f"[I] l.{i}: `… in` must be followed by a command in column 0"
                            )
        toks = _WORD.findall(_blank_attr_lists(ln))  # H
        for j, t in enumerate(toks):
            if t not in COMMAND_HEADS or t in SUBSET_COMMANDS:
                continue
            if t == "scoped" and j > 0 and toks[j - 1] == "open":
                continue  # `open scoped X` is the allowed `open`
            if t == "deriving" and (j + 1 >= len(toks) or toks[j + 1] != "instance"):
                continue  # a `deriving C` clause of a structure/inductive, not the command
            out.append(f"[H] l.{i}: command keyword `{t}` is not an allowed command")
        for m in re.finditer(r"#(\w+)", ln):  # B
            if m.group(1) != "print" or not re.match(r"[ \t]+axioms\b", ln[m.end() :]):
                out.append(
                    f"[B] l.{i}: `{m.group(0)}` (the only allowed `#` command is `#print axioms`)"
                )
        for m in re.finditer(r"@\[", ln):  # C
            close = ln.find("]", m.end())
            if close < 0:
                out.append(f"[C] l.{i}: `@[` not closed on its line")
                continue
            for item in ln[m.end() : close].split(","):
                words = item.split()
                while words and words[0] in _ATTR_PREFIXES:
                    words = words[1:]
                if " ".join(words) not in SUBSET_ATTRIBUTES:
                    out.append(f"[C] l.{i}: attribute `{item.strip()}` is not allowed")
        for w in SUBSET_DENY_WORDS:  # D
            if re.search(r"(?<![\w.'])" + re.escape(w) + r"(?![\w'!?])", ln):
                out.append(f"[D] l.{i}: `{w}` is outside the pass-file subset")
    if not COMMAND_HEADS:
        out.append("[H] command_heads.json is missing or empty: rule H cannot run")
    return out


def read_lean_source(p: Path) -> str:
    """A .lean file's text EXACTLY as Lean numbers its lines (Gemini r4 (f) on PR #824).

    Lean's `FileMap.ofString` starts a new line ONLY at `\\n`; the frontend first rewrites
    `\\r\\n` to `\\n` (`String.crlfToLf`, `mkInputContext` default) and nothing else. A lone
    `\\r`, `\\f`, `\\v`, `\\x1c`-`\\x1e`, `\\x85`, U+2028 or U+2029 is NOT a line break to Lean
    (probe on v4.30.0 recorded in `must-fail/MF10_LineBreakDesync`). So: read bytes (Python's
    text mode would apply universal newlines and turn a lone `\\r` into a line break), decode,
    apply exactly Lean's `\\r\\n` -> `\\n`, and split only with `lean_lines` — never
    `str.splitlines()`, which also breaks at every character listed above."""
    return p.read_bytes().decode("utf-8").replace("\r\n", "\n")


def lean_lines(text: str) -> list[str]:
    """Split at `\\n` only, as Lean's `FileMap` does. Line k (1-based) is `lean_lines(t)[k - 1]`."""
    return text.split("\n")


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


# ---------------------------------------------------------------- pins


def read_pins(proofs: Path) -> dict:
    toolchain = (proofs / "lean-toolchain").read_text().strip()
    lake = (proofs / "lakefile.lean").read_text()
    m = re.search(
        r'require\s+mathlib\s+from\s+git\s+"[^"]+"\s*@\s*"([0-9a-f]{40})"', lake
    )
    if not m:
        raise SystemExit("toolcheck: cannot find the Mathlib sha in lakefile.lean")
    sha = m.group(1)
    manifest_rev = ""
    mf = proofs / "lake-manifest.json"
    if mf.exists():
        for pkg in json.loads(mf.read_text()).get("packages", []):
            if pkg.get("name") == "mathlib":
                manifest_rev = pkg.get("rev", "")
    version = toolchain.split(":", 1)[-1]
    return {
        "toolchain": toolchain,
        "version": version,
        "mathlib_sha": sha,
        "mathlib_sha7": sha[:7],
        "manifest_mathlib_rev": manifest_rev,
    }


def cmd_pins(a: argparse.Namespace) -> int:
    p = read_pins(Path(a.proofs))
    for k, v in p.items():
        print(f"{k.upper()}={v}")
    return 0


# ---------------------------------------------------------------- imports


def qbp_mathlib_imports(proofs: Path) -> list[str]:
    mods: set[str] = set()
    for f in proofs.rglob("*.lean"):
        parts = f.relative_to(proofs).parts
        if parts[0] in (".lake", "lean-toolcheck"):
            continue
        code = strip_comments(f.read_text(encoding="utf-8", errors="replace"))
        mods.update(re.findall(r"^[ \t]*import\s+(Mathlib[\w.]*)", code, re.MULTILINE))
    return sorted(mods)


def cmd_imports(a: argparse.Namespace) -> int:
    for m in qbp_mathlib_imports(Path(a.proofs)):
        print(m)
    return 0


def cmd_check_imports(a: argparse.Namespace) -> int:
    live = set(qbp_mathlib_imports(Path(a.proofs)))
    code = strip_comments(Path(a.file).read_text())
    have = set(re.findall(r"^[ \t]*import\s+(Mathlib[\w.]*)", code, re.MULTILINE))
    missing, extra = sorted(live - have), sorted(have - live)
    if missing or extra:
        print(f"toolcheck: import surface STALE — {a.file}")
        for m in missing:
            print(f"  missing (QBP imports it, the surface file does not): {m}")
        for m in extra:
            print(f"  extra (no QBP file imports it any more): {m}")
        print(
            "  regenerate: python3 tools/lean-toolcheck/toolcheck.py imports --proofs proofs  (from the repo root)"
        )
        return 1
    print(f"toolcheck: import surface current ({len(live)} Mathlib modules)")
    return 0


# ---------------------------------------------------------------- evaluate


def lean_messages(log: str) -> tuple[list[dict], int]:
    """Lean's own message stream from `lean --json` output: one JSON object per line.

    Returns (messages, n_untrusted) — each message is {sev, line, col, text}; any other
    stdout line (e.g. from `#eval IO.println`) is UNTRUSTED and only counted.
    """
    msgs: list[dict] = []
    untrusted = 0
    # `lean --json` writes one object per `\n`-terminated line; a raw U+2028/`\x85` inside a
    # JSON string must not split a message (str.splitlines would — Gemini r4 (f)).
    for raw in log.split("\n"):
        raw = raw.strip()
        if not raw:
            continue
        try:
            m = json.loads(raw) if raw.startswith("{") else None
        except json.JSONDecodeError:
            m = None
        if not isinstance(m, dict) or "severity" not in m or "data" not in m:
            untrusted += 1
            continue
        pos = m.get("pos") or {}
        msgs.append(
            {
                "sev": m["severity"],
                "line": pos.get("line"),
                "col": pos.get("column"),
                "text": str(m["data"]),
            }
        )
    return msgs, untrusted


def render(m: dict) -> str:
    """One message as `L:C: severity: text` — the unit every expectation regex is matched against."""
    return f"{m['line']}:{m['col']}: {m['sev']}: {m['text']}"


# Lean's `--json` `pos.column` unit, PINNED by probe (Gemini r3 (e) on PR #824, 2026-11-20,
# v4.30.0): for `def αβγ : Nat := 1 #print axioms dirty` Lean reported column 19 = the
# CODEPOINT offset of `#` (its UTF-8 byte offset is 22). `selftest_grader.py` re-checks this pin
# on MF09's real Lean output every run, so a toolchain that switched to bytes would fail loudly.
LEAN_COLUMN_UNIT = "codepoint"


def lean_column(source_line: str, char_index: int) -> int:
    """Column of `source_line[char_index]` in Lean's unit, computed from the ORIGINAL source line."""
    prefix = source_line[:char_index]
    if LEAN_COLUMN_UNIT == "codepoint":
        return len(prefix)  # Python str indices are codepoints
    return len(prefix.encode("utf-8"))


def print_axioms_sites(src: str) -> dict[tuple[int, int], str]:
    """(line, column) of EVERY `#print axioms <thm>` command — anywhere on a line, not just at
    its start (Gemini r2 (b)). Matches are found in code-only text (comments and string bodies
    blanked; same length as the source), and the column is then computed in Lean's unit from
    the ORIGINAL source line (Gemini r3 (e))."""
    sites: dict[tuple[int, int], str] = {}
    # `\n`-only on both sides (Gemini r4 (f)): `_render` keeps exactly `\n`, so the code-only
    # text and the original have the same line count by construction — checked, not assumed.
    orig_lines = lean_lines(src)
    code_lines = lean_lines(code_only(src))
    if len(code_lines) != len(orig_lines):
        raise SystemExit("toolcheck: internal error — code_only changed the line count")
    for ln, line in enumerate(code_lines, start=1):
        for m in re.finditer(r"#print\s+axioms\s+(\S+)", line):
            sites[(ln, lean_column(orig_lines[ln - 1], m.start()))] = m.group(1)
    return sites


def parse_axioms(
    msgs: list[dict], sites: dict[tuple[int, int], str]
) -> tuple[dict[str, list[str]], int, list[tuple[int, int]]]:
    """Axiom audit, spoof-resistant (Gemini (2) on PR #824).

    (a) A report counts only if it is an `information` message from Lean's message stream
        positioned EXACTLY at a `#print axioms <thm>` command for that same <thm>; text
        printed by `#eval IO.println`, `run_cmd logInfo …` or anything else is ignored.
    (b) Merge is worst-case: reports for one theorem are UNIONED, so a later "does not
        depend on any axioms" can never clear a non-standard axiom already reported.
    Returns (axioms per theorem, number of axiom-like messages rejected as unpositioned,
    sites that received MORE than one report). Lean emits exactly one report per site, so in a
    pass file a rejected message or a duplicate is a FAILURE (Red Team 1(b) fail-closed rule).
    """
    res: dict[str, set[str]] = {}
    rejected = 0
    per_site: dict[tuple[int, int], int] = {}
    for m in msgs:
        text = m["text"]
        dep = AXIOMS_RE.search(text)
        nodep = NOAXIOMS_RE.search(text)
        if not (dep or nodep):
            continue
        thm = (dep or nodep).group(1)  # type: ignore[union-attr]
        if m["sev"] != "information" or sites.get((m["line"], m["col"])) != thm:
            rejected += 1
            continue
        per_site[(m["line"], m["col"])] = per_site.get((m["line"], m["col"]), 0) + 1
        acc = res.setdefault(thm, set())
        if dep:
            acc.update(
                x.strip()
                for x in dep.group(2).replace("\n", " ").split(",")
                if x.strip()
            )
    dups = sorted(k for k, n in per_site.items() if n > 1)
    return {k: sorted(v) for k, v in res.items()}, rejected, dups


AUDIT_MARK = "AXIOM-AUDIT-827"


def _audit_checker(run_meta: dict):
    """PR #829's checker module (for `std_mismatch`), loaded from beside the auditor. Nothing is
    vendored: the pins live in `scripts/check_lean_axiom_audit.py` (STD_PINS)."""
    chk = (run_meta.get("auditor") or {}).get("checker")
    if not chk or not Path(chk).is_file():
        return None
    spec = importlib.util.spec_from_file_location("qbp_check_lean_axiom_audit", chk)
    if spec is None or spec.loader is None:
        return None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod if hasattr(mod, "std_mismatch") else None


def structural_audit(
    raw: Path, stem: str, fmeta: dict, run_meta: dict
) -> tuple[list[str], dict[str, list[str]]]:
    """The AXIOM VERDICT for a file (director ruling after Red Team r3 on PR #824).

    run.sh compiled the file to an .olean in a fresh process and ran the PR #829 auditor
    (`scripts/LeanAxiomAudit.lean`) on it: `lean --run`, LEAN_PATH unset, the toolchain library
    first, `importModules (loadExts := false)`, no initializers, so no code of the file runs and
    nothing it printed is read. Returns (problems that make the audit unusable, non-standard
    axioms per declaration). Fail-closed: no .olean, no auditor, not exactly one result line,
    a wrong nonce/root/scope, a non-empty `missing`/`unresolved`/`shadowed`, standard axioms that
    are not the toolchain's, or zero declarations is a problem."""
    a = fmeta.get("audit")
    if not isinstance(a, dict):
        return [
            "no structural-audit record for this file (run.sh did not audit it)"
        ], {}
    if not a.get("olean"):
        return [
            f"the fresh compile produced no .olean (exit {a.get('compile_exit')}): nothing to "
            f"audit (a file that exits early fails closed here)"
        ], {}
    chk = _audit_checker(run_meta)
    if chk is None:
        return [
            "PR #829 auditor/checker unavailable (run meta has no usable `auditor`)"
        ], {}
    out = raw / f"{stem}.audit.out"
    text = out.read_bytes().decode("utf-8", "replace") if out.exists() else ""
    res = []
    for ln in text.split("\n"):
        try:
            d = json.loads(ln)
        except ValueError:
            continue
        if isinstance(d, dict) and d.get("mark") == AUDIT_MARK:
            res.append(d)
    if len(res) != 1:
        return [
            f"auditor printed {len(res)} result lines, exactly 1 required "
            f"(auditor exit {a.get('auditor_exit')})"
        ], {}
    d = res[0]
    probs: list[str] = []
    mod = f"ToolcheckAudit.{stem}"
    if d.get("nonce") != a.get("nonce"):
        probs.append("auditor result carries the wrong nonce")
    if d.get("root") != stem:
        probs.append(f"auditor result is for root {d.get('root')!r}, not {stem!r}")
    if d.get("scope") != [mod]:
        probs.append(f"audit scope {d.get('scope')} is not [{mod}]")
    for k in ("missing", "unresolved", "shadowed"):
        if d.get(k) != []:
            probs.append(f"auditor `{k}` = {d.get(k)} (must be [])")
    bad_std = chk.std_mismatch(d.get("std"))
    if bad_std:
        probs.append(f"standard axioms are not the toolchain's: {bad_std}")
    if not isinstance(d.get("declarations"), int) or d["declarations"] < 1:
        probs.append(
            f"auditor enumerated {d.get('declarations')} declarations (need >= 1)"
        )
    nonstd: dict[str, list[str]] = {}
    if not isinstance(d.get("nonstd"), list):
        probs.append("auditor `nonstd` is not a list")
    else:
        for b in d["nonstd"]:
            nonstd[str(b.get("decl"))] = sorted(
                str(x.get("name")) for x in b.get("axioms", []) if isinstance(x, dict)
            )
    return probs, nonstd


def file_kind(rel: str) -> str:
    if rel.startswith("must-fail/"):
        return "must-fail"
    if rel.startswith("known-limits/"):
        return "known-limit"
    return "tool"


def grade(src_path: Path, raw: Path, suite: Path, run_meta: dict) -> dict:
    rel = src_path.relative_to(suite).as_posix()
    stem = src_path.stem
    src = read_lean_source(src_path)  # Lean's line numbering, never universal newlines
    expects = EXPECT_RE.findall(src)
    meta_p = raw / f"{stem}.meta.json"
    if not meta_p.exists():
        return {
            "file": rel,
            "kind": file_kind(rel),
            "expect": [f"{k} {a}".strip() for k, a in expects],
            "lean_exit": None,
            "wall_s": None,
            "maxrss_mb": None,
            "axioms": {},
            "detections": [],
            "failures": [
                "not run (no raw result) — the suite was interrupted or skipped it"
            ],
            "result": "FAIL",
        }
    log = (raw / f"{stem}.log").read_bytes().decode("utf-8", errors="replace")
    meta = json.loads(meta_p.read_text())
    chk_out_p = raw / f"{stem}.checker.log"
    chk_out = chk_out_p.read_text() if chk_out_p.exists() else ""
    chk_exit = meta.get("checker_exit")
    msgs, n_untrusted = lean_messages(log)
    # Sites from code with comments AND string bodies blanked; anywhere on a line.
    sites = print_axioms_sites(src)
    axioms, n_rejected, dup_sites = parse_axioms(msgs, sites)
    audit_probs, audit_nonstd = structural_audit(raw, stem, meta, run_meta)
    subset = subset_violations(src)
    # Supported subset: no brace inside a string literal (interpolation is not lexed).
    braces = brace_in_string(src)
    if braces:
        # The lexer cannot be trusted on this file, so neither can its site list: audit EVERY
        # information-level axiom report Lean emitted (still worst-case merged). The file
        # fails anyway unless it is a must-fail that expects the refusal (MF08).
        every = {(m["line"], m["col"]): "" for m in msgs if m["sev"] == "information"}
        for m in msgs:
            hit = AXIOMS_RE.search(m["text"]) or NOAXIOMS_RE.search(m["text"])
            if m["sev"] == "information" and hit:
                every[(m["line"], m["col"])] = hit.group(1)
        axioms, n_rejected, dup_sites = parse_axioms(
            msgs, {k: v for k, v in every.items() if v}
        )
    refusal = (
        f"grader REFUSES the file: brace inside a string literal at line(s) {braces} — "
        f"possible interpolation, which the lexer does not model (write a literal brace as \\x7B)"
        if braces
        else ""
    )
    errors = [render(m) for m in msgs if m["sev"] == "error"]
    warn_info = [render(m) for m in msgs if m["sev"] in ("warning", "information")]
    # checker-reject regexes are matched per `::error::` line, never against the whole output
    chk_errors = [ln for ln in chk_out.splitlines() if ln.startswith("::error")]
    lean_exit = meta.get("lean_exit")
    failures: list[str] = []
    detections: list[str] = []
    if n_rejected:
        detections.append(
            f"axiom audit ignored {n_rejected} axiom-like message(s) not positioned at a "
            f"`#print axioms` command (spoof guard)"
        )

    subset_note = (
        f"file leaves the pass-file subset ({len(subset)}: {'; '.join(subset[:6])}"
        f"{' …' if len(subset) > 6 else ''}) — code it defines or runs could forge or suppress "
        f"Lean's stdout, so no audit of it is trusted"
        if subset
        else ""
    )
    if "subset-refused" in [k for k, _ in expects]:
        if subset:
            detections.append(subset_note)
        else:
            failures.append(
                "expected the file to leave the pass-file subset, but it does not"
            )

    def any_match(rx: str, lines: list[str]) -> bool:
        return any(re.search(rx, ln) for ln in lines)

    known: list[str] = []
    kind_is_kl = file_kind(rel) == "known-limit"
    if lean_exit in (75, 86, 87, 124):
        failures.append(
            f"boxrun aborted the run (exit {lean_exit}: 75 busy / 86 thermal / 87 mem / 124 timeout)"
        )
    elif isinstance(lean_exit, int) and lean_exit >= 128:
        failures.append(
            f"Lean CRASHED (exit {lean_exit} = signal {lean_exit - 128}; "
            f"wall {meta.get('wall_s')} s, RSS {meta.get('maxrss_mb')} MB) — not retried"
        )

    kinds = [k for k, _ in expects]
    if refusal:
        if "grader-refuses" in kinds:
            detections.append(refusal)
        else:
            failures.append(refusal)
    elif "grader-refuses" in kinds:
        failures.append(
            "expected the grader to REFUSE this file (brace in a string), but it did not"
        )
    if not expects:
        failures.append("no TOOLCHECK-EXPECT line in the file header")

    for kind, arg in expects:
        if kind == "pass":
            # THE VERDICT: the structural audit (PR #829 auditor on a fresh .olean).
            for pr in audit_probs:
                failures.append(f"structural audit: {pr}")
            for decl, axs in sorted(audit_nonstd.items()):
                failures.append(
                    f"structural audit: {decl} rests on non-standard axioms {axs}"
                )
            heads_tc = COMMAND_HEADS_META.get("toolchain")
            if heads_tc != run_meta.get("toolchain") or COMMAND_HEADS_META.get(
                "mathlib_sha"
            ) != run_meta.get("mathlib_sha"):
                failures.append(
                    "command_heads.json was generated for another toolchain/Mathlib "
                    "(re-run gen_command_heads.py)"
                )
            # Fail-closed (Red Team 1(b) on PR #824): Lean's stdout is writable by any code the
            # file runs, so a pass file must run none, print nothing but Lean's own messages,
            # and get exactly one positioned report per `#print axioms` site.
            if subset:
                failures.append(subset_note)
            if n_rejected:
                failures.append(
                    f"{n_rejected} axiom-like message(s) NOT at a `#print axioms` site — "
                    f"a pass file must have none (possible forgery or line/column desync)"
                )
            if dup_sites:
                failures.append(
                    f"more than one axiom report at site(s) {dup_sites} — Lean emits one"
                )
            if n_untrusted:
                failures.append(
                    f"{n_untrusted} stdout line(s) that are not Lean messages — a pass file prints none"
                )
            if lean_exit != 0:
                failures.append(f"Lean exit {lean_exit} (expected 0)")
            if errors:
                failures.append("Lean reported an error")
            if any(SORRY_WARN_RE.search(w) for w in warn_info):
                failures.append("Lean reported a sorry")
            wanted = list(sites.values())
            for thm in wanted:
                if thm not in axioms:
                    failures.append(f"no axiom report for {thm}")
            for thm, ax in axioms.items():
                extra = set(ax) - STANDARD_AXIOMS
                if extra:
                    failures.append(f"{thm}: non-standard axioms {sorted(extra)}")
            if not wanted:
                failures.append("a pass file must end with at least one #print axioms")
            if chk_exit != 0:
                failures.append(
                    f"foundations checker rejected a pass file (exit {chk_exit})"
                )
        elif kind == "lean-ok":
            if lean_exit != 0:
                failures.append(
                    f"Lean exit {lean_exit} (expected 0 — Lean should accept)"
                )
        elif kind == "lean-error":
            if lean_exit == 0:
                failures.append(
                    f"Lean ACCEPTED a must-fail file (expected error /{arg}/)"
                )
            elif not any_match(arg, errors):
                failures.append(f"Lean failed but without the expected message /{arg}/")
            else:
                detections.append(f"Lean rejected: /{arg}/")
        elif kind == "lean-output":
            if any_match(arg, warn_info):
                detections.append(f"Lean output: /{arg}/")
            else:
                failures.append(f"expected Lean output /{arg}/ not found")
        elif kind == "axiom":
            thm, ax = arg.split()
            if thm not in axioms:
                failures.append(f"no axiom report for {thm}")
            elif ax not in axioms[thm]:
                failures.append(f"axiom audit MISSED {ax} on {thm} (got {axioms[thm]})")
            else:
                detections.append(f"axiom audit: {thm} ⊇ {ax}")
        elif kind == "axiom-nonstd":
            thm = arg.strip()
            if thm not in axioms:
                failures.append(f"no axiom report for {thm}")
            else:
                nonstd = sorted(set(axioms[thm]) - STANDARD_AXIOMS)
                if nonstd:
                    detections.append(f"axiom audit: {thm} has non-standard {nonstd}")
                else:
                    failures.append(
                        f"axiom audit MISSED: {thm} shows only standard axioms {axioms[thm]}"
                    )
        elif kind == "checker-reject":
            if chk_exit != 1:
                failures.append(f"foundations checker did not reject (exit {chk_exit})")
            elif not any_match(arg, chk_errors):
                failures.append(
                    f"checker rejected but without the expected message /{arg}/"
                )
            else:
                detections.append(f"checker: /{arg}/")
        elif kind == "audit-nonstd":
            thm = arg.strip()
            if audit_probs:
                failures.append(f"structural audit unusable: {'; '.join(audit_probs)}")
            elif not audit_nonstd.get(thm):
                failures.append(
                    f"structural audit did NOT report a non-standard axiom on {thm}"
                )
            else:
                detections.append(
                    f"structural audit: {thm} rests on {audit_nonstd[thm]}"
                )
        elif kind == "audit-fails":
            if audit_probs or audit_nonstd:
                detections.append(
                    "structural audit does not clear the file: "
                    + "; ".join(
                        audit_probs
                        or [f"{k} {v}" for k, v in sorted(audit_nonstd.items())]
                    )
                )
            else:
                failures.append(
                    "expected the structural audit to fail, but it is clean"
                )
        elif kind in ("grader-refuses", "subset-refused"):
            pass  # handled above, before the per-expectation loop
        elif kind == "known-limit":
            check, _, rest = arg.partition(" ")
            if check == "checker-accepts":
                hold = chk_exit == 0
                what = f"foundations checker accepts the file (exit {chk_exit})"
            elif check == "audit-clean":
                thm = rest.strip()
                ax = axioms.get(thm)
                hold = ax is not None and not (set(ax) - STANDARD_AXIOMS)
                what = f"`#print axioms {thm}` is clean ({ax})"
            elif check == "lean-error":
                hold = lean_exit not in (0, None) and any_match(rest, errors)
                what = f"Lean still rejects with /{rest}/"
            else:
                failures.append(f"unknown known-limit check {check!r}")
                continue
            known.append(
                (
                    "KNOWN-LIMIT confirmed: "
                    if hold
                    else "KNOWN-LIMIT CHANGED (re-read): "
                )
                + what
            )
        else:
            failures.append(f"unknown expectation kind {kind!r}")

    # Non-pass files: any non-standard axiom must be EXPECTED (an unexpected one is a failure).
    if "pass" not in kinds:
        expected_ax = {tuple(a.split()) for k, a in expects if k == "axiom"}
        any_ok = {a.strip() for k, a in expects if k == "axiom-nonstd"}
        for thm, ax in axioms.items():
            if thm in any_ok:
                continue
            for x in set(ax) - STANDARD_AXIOMS:
                if (thm, x) not in expected_ax:
                    failures.append(f"{thm}: unexpected non-standard axiom {x}")

    return {
        "file": rel,
        "kind": file_kind(rel),
        "expect": [f"{k} {a}".strip() for k, a in expects],
        "lean_exit": lean_exit,
        "wall_s": meta.get("wall_s"),
        "maxrss_mb": meta.get("maxrss_mb"),
        "tctl_start_c": meta.get("tctl_start_c"),
        "tctl_end_c": meta.get("tctl_end_c"),
        "max_tctl_c": meta.get("max_tctl_c"),
        "guard_pauses": meta.get("pauses"),
        "checker_exit": chk_exit,
        "axioms": axioms,
        "structural_audit": {"problems": audit_probs, "nonstd": audit_nonstd},
        "detections": detections,
        "failures": failures,
        "known_limits": known,
        "result": "FAIL" if failures else ("KNOWN-LIMIT" if kind_is_kl else "PASS"),
    }


def axiom_summary(axioms: dict[str, list[str]]) -> str:
    sets = {tuple(v) for v in axioms.values()}
    extra = sorted({x for v in axioms.values() for x in v} - STANDARD_AXIOMS)
    if not axioms:
        return "—"
    if not extra:
        return f"{len(axioms)} thm ⊆ std3"
    return f"{len(axioms)} thm; non-std: {', '.join(extra)}" + ("" if len(sets) else "")


def cmd_evaluate(a: argparse.Namespace) -> int:
    raw, suite = Path(a.raw), Path(a.suite)
    meta = json.loads(Path(a.meta).read_text()) if a.meta else {}
    files = (
        sorted((suite / "tests").glob("*.lean"))
        + sorted((suite / "must-fail").glob("*/*.lean"))
        + sorted((suite / "known-limits").glob("*/*.lean"))
    )
    if a.only_present:
        files = [f for f in files if (raw / f"{f.stem}.meta.json").exists()]
    rows = [grade(f, raw, suite, meta) for f in files]
    # An empty suite (or an emptied layer) must be RED, never a vacuous GREEN (Gemini on PR #824).
    empty: list[str] = []
    if not rows:
        empty.append("no suite files graded — an empty suite is RED")
    elif not a.only_present:
        for layer in ("tool", "must-fail", "known-limit"):
            if not any(r["kind"] == layer for r in rows):
                empty.append(f"the {layer} layer has zero files — RED")
    meta.setdefault("preflight_failures", [])
    meta["preflight_failures"] = list(meta["preflight_failures"]) + empty
    ok = all(r["result"] in ("PASS", "KNOWN-LIMIT") for r in rows) and not meta.get(
        "preflight_failures"
    )
    doc = {
        "suite": "qbp-lean-toolcheck",
        "schema": 1,
        **meta,
        "files": rows,
        "summary": {
            "files": len(rows),
            "pass": sum(r["result"] in ("PASS", "KNOWN-LIMIT") for r in rows),
            "fail": sum(r["result"] == "FAIL" for r in rows),
            "tool_files": sum(r["kind"] == "tool" for r in rows),
            "must_fail_files": sum(r["kind"] == "must-fail" for r in rows),
            "known_limit_files": sum(r["kind"] == "known-limit" for r in rows),
            "theorems_audited": sum(len(r["axioms"]) for r in rows),
            "overall": "GREEN" if ok else "RED",
        },
    }
    Path(a.out_json).write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")

    lines = [
        f"# Lean toolcheck results — {meta.get('toolchain', '?')} / Mathlib {meta.get('mathlib_sha7', '?')}",
        "",
        f"Run {meta.get('run_id', '?')} · {meta.get('date_utc', '?')} · overall **{doc['summary']['overall']}** "
        f"({doc['summary']['pass']}/{doc['summary']['files']} as expected)",
        "",
        "| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for r in rows:
        det = (
            "; ".join(r["failures"] or (r["detections"] + r.get("known_limits", [])))
            or "—"
        )
        lines.append(
            f"| `{r['file']}` | {r['kind']} | { {'PASS': '✅', 'KNOWN-LIMIT': '🟡'}.get(r['result'], '❌') } {r['result']} | "
            f"{r['lean_exit']} | {r['wall_s']} | {r['maxrss_mb']} | {r.get('tctl_start_c')}→{r.get('tctl_end_c')} | "
            f"{axiom_summary(r['axioms'])} | {det} |"
        )
    for pf in meta.get("preflight_failures", []):
        lines.append(f"\n**Preflight failure:** {pf}")
    Path(a.out_md).write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pins")
    p.add_argument("--proofs", required=True)
    p.set_defaults(fn=cmd_pins)
    p = sub.add_parser("imports")
    p.add_argument("--proofs", required=True)
    p.set_defaults(fn=cmd_imports)
    p = sub.add_parser("check-imports")
    p.add_argument("--proofs", required=True)
    p.add_argument("--file", required=True)
    p.set_defaults(fn=cmd_check_imports)
    p = sub.add_parser("evaluate")
    p.add_argument("--raw", required=True)
    p.add_argument("--suite", required=True)
    p.add_argument("--out-json", required=True)
    p.add_argument("--out-md", required=True)
    p.add_argument("--meta")
    p.add_argument(
        "--only-present",
        action="store_true",
        help="grade only files that were run (subset runs)",
    )
    p.set_defaults(fn=cmd_evaluate)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
