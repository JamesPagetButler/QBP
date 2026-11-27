#!/usr/bin/env python3
"""Enumerate the leading tokens of Lean's `command` syntax category, AS LEAN SEES THEM, for the
pass-file subset's rule H (Red Team r3 on PR #824).

The list is not hand-written. A generated driver imports `Lean` plus every module of the T00
import surface (all the Mathlib modules QBP imports). It reads
`(parserExtension.getState env).categories["command"].tables.leadingTable`, which is the parser's
own first-token index, and prints its keys as one JSON line. EVERY leading token is written to
`command_heads.json` (`heads`; Red Team r4: the non-word ones such as `simproc_pattern%` matter
too), with the toolchain, Mathlib and import-list pins. The grader
refuses a file whose pins differ, so a toolchain bump must regenerate the list. The number of
UNINDEXED command parsers (`leadingParsers`, which have no first token) is recorded too. Those are
a stated limit of a text scan.

This is a GENERATOR, not a test: the driver runs our own `#eval`. Run it from the repo root:
  boxrun --gpu --mem-mb 8000 --timeout 900 --label cmdheads -- \\
    python3 -I tools/lean-toolcheck/gen_command_heads.py
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
PROOFS = REPO / "proofs"
sys.path.insert(0, str(HERE))
import toolcheck  # noqa: E402

DRIVER = """import Lean
{imports}

open Lean Parser in
#eval show CoreM Unit from do
  let env ← getEnv
  let some cat := (parserExtension.getState env).categories.find? `command
    | throwError "no command category"
  let keys := cat.tables.leadingTable.toList.map (fun p => p.1.toString)
  IO.println (Json.compress (Json.mkObj [("mark", "QBP-CMD-HEADS"),
    ("leading", toJson keys), ("unindexed", toJson cat.tables.leadingParsers.length)]))
"""


def main() -> int:
    t00 = toolcheck.read_lean_source(HERE / "tests" / "T00_ImportSurface.lean")
    mods = re.findall(
        r"^[ \t]*import\s+(\S+)", toolcheck.strip_comments(t00), re.MULTILINE
    )
    gen = HERE / "results" / "runs" / "_gen_command_heads"  # gitignored
    gen.mkdir(parents=True, exist_ok=True)
    drv = gen / "CommandHeadsDriver.lean"
    drv.write_text(DRIVER.format(imports="\n".join(f"import {m}" for m in mods)))
    r = subprocess.run(
        ["lake", "env", "lean", str(drv)], cwd=PROOFS, capture_output=True, text=True
    )
    line = next(
        (
            l
            for l in r.stdout.split("\n")
            if l.startswith('{"leading"') or "QBP-CMD-HEADS" in l
        ),
        None,
    )
    if r.returncode != 0 or line is None:
        print(r.stdout[-2000:], r.stderr[-2000:], file=sys.stderr)
        print("gen_command_heads: the driver failed", file=sys.stderr)
        return 1
    d = json.loads(line)
    # `Name.toString` escapes non-identifier tokens as «…»; the token itself is inside.
    d["leading"] = [
        t[1:-1] if t.startswith("«") and t.endswith("»") else t for t in d["leading"]
    ]
    words = sorted(
        {t for t in d["leading"] if re.fullmatch(r"#?[A-Za-z_][A-Za-z0-9_!?]*", t)}
    )
    pins = toolcheck.read_pins(PROOFS)
    out = {
        "generator": "tools/lean-toolcheck/gen_command_heads.py",
        "toolchain": pins["toolchain"],
        "mathlib_sha": pins["mathlib_sha"],
        "imports": ["Lean"] + mods,
        "leading_tokens_total": len(d["leading"]),
        "unindexed_command_parsers": d["unindexed"],
        "heads": sorted(d["leading"]),
        "word_heads": words,
    }
    (HERE / "command_heads.json").write_text(json.dumps(out, indent=1) + "\n")
    print(
        f"gen_command_heads: {len(words)} word heads of {len(d['leading'])} leading tokens; "
        f"{d['unindexed']} unindexed command parsers"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
