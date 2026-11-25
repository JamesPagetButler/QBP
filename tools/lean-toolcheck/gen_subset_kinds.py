#!/usr/bin/env python3
"""Generate `subset_kinds.json`: the Lean-parser allowlist of the pass-file subset (Red Team r5 /
director decision on PR #824).

It runs `LeanSubsetParse.lean` (`lean --run`, parse only: the files' own code never runs) on
every PASS-labelled tool test in `tests/`. It writes the UNION of what they use: top-level
command kinds, every syntax-node kind, nested command kinds, attributes, `set_option` keys and
tactic-config names. It also writes the pins (toolchain, Mathlib sha, T00 import list,
sha256 of `LeanSubsetParse.lean`). The grader refuses a stale file.

The allowlist is closed-world: a pass file may use only constructs some reviewed tool test
already uses. Generation REFUSES (exit 1) if a tool test uses a top-level command outside
TOP_ALLOWED or any kind matching DENY_KIND. So a new tool test cannot quietly widen the subset to
code-running constructs; that would need a reviewed edit of this file.

Run it from the repo root, under boxrun (one Lean process at a time, ~2–5 GB RSS each):
  boxrun --gpu --mem-mb 7000 --timeout 900 --wait --label subsetkinds -- \\
    python3 -I tools/lean-toolcheck/gen_subset_kinds.py
"""

from __future__ import annotations

import json
import os
import re
import secrets
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
PROOFS = REPO / "proofs"
sys.path.insert(0, str(HERE))
import toolcheck  # noqa: E402

# Top-level commands a pass file may ever have (the scope commands, declarations, the axiom
# report). A tool test outside this list must be a non-pass file (T20).
TOP_ALLOWED = {
    "Lean.Parser.Command.declaration",
    "Lean.Parser.Command.end",
    "Lean.Parser.Command.in",
    "Lean.Parser.Command.namespace",
    "Lean.Parser.Command.section",
    "Lean.Parser.Command.open",
    "Lean.Parser.Command.printAxioms",
    "Lean.Parser.Command.variable",
    "Lean.Parser.Command.set_option",
}
# Kinds that can run code at elaboration time, extend the syntax, or register handlers. A tool
# test using one is a generation error, never an allowlist entry.
DENY_KIND = re.compile(
    r"(?:^|\.)(?:eval\w*|Eval\w*|runTac|runElab|runCmd|runMeta|byElab|nativeDecide|native_decide|"
    r"simproc\w*|Simproc\w*|dsimproc\w*|initialize|Initialize|implementedBy|extern|unsafe|axiom|"
    r"quot|Quot|antiquot|elabAs\w*)(?:$|\.)"
    r"|Command\.(?:notation|mixfix|syntax\w*|macro\w*|elab\w*|attribute|declare\w*|initialize|"
    r"addDeclDoc|genInjective\w*|compileDef|compileInductive)"
)


def main() -> int:
    pins = toolcheck.read_pins(PROOFS)
    lp = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=PROOFS,
        capture_output=True,
        text=True,
    ).stdout.strip()
    env = {k: v for k, v in os.environ.items() if k != "LEAN_PATH"}
    env["QBP_SUBSET_LEAN_PATH"] = ":".join(
        x for x in lp.split(":") if "/.lake/packages/" in x
    )
    union: dict[str, set[str]] = {
        f: set()
        for f in ("top_kinds", "kinds", "nested", "attrs", "set_option", "config")
    }
    used = []
    for f in sorted((HERE / "tests").glob("*.lean")):
        src = toolcheck.read_lean_source(f)
        if "pass" not in [k for k, _ in toolcheck.EXPECT_RE.findall(src)]:
            continue
        nonce = secrets.token_hex(16)
        r = subprocess.run(
            ["lean", "--run", str(HERE / "LeanSubsetParse.lean"), nonce, str(f)],
            cwd=PROOFS,
            env=env,
            capture_output=True,
            text=True,
        )
        recs = [json.loads(ln) for ln in r.stdout.splitlines() if ln.strip()]
        if r.returncode != 0 or not recs or recs[-1].get("done") is not True:
            print(
                f"gen_subset_kinds: {f.name}: parse failed\n{r.stderr[-1500:]}",
                file=sys.stderr,
            )
            return 1
        if any(x.get("nonce") != nonce for x in recs):
            print(f"gen_subset_kinds: {f.name}: nonce mismatch", file=sys.stderr)
            return 1
        for c in recs[1:-1]:
            if c.get("parse_error") or c.get("scope_error"):
                print(
                    f"gen_subset_kinds: {f.name} l.{c.get('line')}: parse/scope error",
                    file=sys.stderr,
                )
                return 1
            union["top_kinds"].add(c["kind"])
            for fld in ("kinds", "nested", "attrs", "set_option", "config"):
                union[fld] |= set(c.get(fld, []))
        used.append(f.name)
    bad_top = union["top_kinds"] - TOP_ALLOWED
    bad = sorted(
        k
        for fld in ("kinds", "nested", "attrs")
        for k in union[fld]
        if DENY_KIND.search(k)
    )
    if bad_top or bad:
        print(
            f"gen_subset_kinds: REFUSED: top {sorted(bad_top)}, denied kinds {bad}",
            file=sys.stderr,
        )
        return 1
    out = {
        "toolchain": pins["toolchain"],
        "mathlib_sha": pins["mathlib_sha"],
        "imports": toolcheck.t00_imports(),
        "parser_sha256": toolcheck._sha256(HERE / "LeanSubsetParse.lean"),
        "generated_from": used,
        **{k: sorted(v) for k, v in union.items()},
    }
    (HERE / "subset_kinds.json").write_text(
        json.dumps(out, indent=1, ensure_ascii=False) + "\n"
    )
    print(
        f"gen_subset_kinds: {len(used)} pass files; {len(out['top_kinds'])} top kinds, "
        f"{len(out['kinds'])} node kinds, attrs {out['attrs']}, options {out['set_option']}, "
        f"configs {out['config']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
