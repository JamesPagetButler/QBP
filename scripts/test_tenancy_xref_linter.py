#!/usr/bin/env python3
"""Tests for the tenancy cross-reference linter (scripts/tenancy_xref_linter.py).

Covers the #738 `expected-on-sibling` contract — verify a federation ref when the
sibling checkout is present, INFO (never a silent pass) when it is absent — plus the
pre-existing in-repo contract. Each case builds a throwaway repo root, doc and
sibling root and drives the linter as a subprocess.
Run: python3 scripts/test_tenancy_xref_linter.py
"""

import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "tenancy_xref_linter.py")
WORKFLOW = os.path.join(HERE, "..", ".github", "workflows", "tenancy-xref-lint.yml")

CTX_REF = "`~/Documents/Contextus/doc/contextus-tenancy-pattern.md`"
CTX_ANN = "<!-- expected-on-sibling: Contextus doc/contextus-tenancy-pattern.md -->"


def run(doc_text, repo_files=(), siblings=(), sibling_root=True, env=None):
    """Run the linter on `doc_text`.

    repo_files: in-repo relative paths to create under the temp repo root.
    siblings:   (repo, relpath-or-None) — creates <sibling_root>/<repo>[/<relpath>].
    sibling_root: False → point the linter at an EMPTY sibling root (all absent).
    env:        extra environment (e.g. QBP_SIBLING_ROOT); when it carries
                QBP_SIBLING_ROOT the --sibling-root flag is omitted.
    Returns (exit code, stdout).
    """
    with tempfile.TemporaryDirectory() as d:
        repo = os.path.join(d, "repo")
        os.makedirs(os.path.join(repo, "docs"))
        for rel in repo_files:
            p = os.path.join(repo, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, "w").write("x")
        doc = os.path.join(repo, "docs", "qbp-federation-tenancy.md")
        open(doc, "w").write(doc_text)

        sroot = os.path.join(d, "siblings")
        os.makedirs(sroot)
        for repo_name, rel in siblings:
            os.makedirs(os.path.join(sroot, repo_name), exist_ok=True)
            if rel:
                p = os.path.join(sroot, repo_name, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, "w").write("x")

        cmd = [sys.executable, SCRIPT, "--doc", doc, "--repo-root", repo]
        full_env = dict(os.environ)
        full_env.pop("QBP_SIBLING_ROOT", None)
        if env:
            full_env.update({k: v.replace("{sroot}", sroot) for k, v in env.items()})
        if "QBP_SIBLING_ROOT" not in (env or {}):
            cmd += ["--sibling-root", sroot if sibling_root else os.path.join(d, "no")]
        r = subprocess.run(cmd, capture_output=True, text=True, env=full_env)
        return r.returncode, r.stdout + r.stderr


CASES = [
    # (name, doc_text, repo_files, siblings, sibling_root, env, expected_exit, must_contain, must_not_contain)
    (
        "annotated (same line) + sibling present + path exists → VERIFIED, exit 0",
        f"Pattern: {CTX_REF} {CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        0,
        ["VERIFIED on sibling Contextus", "annotated: 1, verified: 1, unverifiable: 0"],
        ["not verified", "FAIL"],
    ),
    (
        "annotated (next line) + sibling present + path exists → VERIFIED, exit 0",
        f"Pattern: {CTX_REF}\n{CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        0,
        ["VERIFIED on sibling Contextus"],
        ["ORPHAN"],
    ),
    (
        "annotated + sibling present + path MISSING → BROKEN SIBLING REF, exit 1",
        f"Pattern: {CTX_REF} {CTX_ANN}\n",
        (),
        (("Contextus", None),),
        True,
        None,
        1,
        ["BROKEN SIBLING REF", "FAIL:"],
        ["VERIFIED"],
    ),
    (
        "annotated + sibling ABSENT → INFO not verifiable here, exit 0 (never silent)",
        f"Pattern: {CTX_REF} {CTX_ANN}\n",
        (),
        (),
        False,
        None,
        0,
        ["not verifiable here", "annotated: 1, verified: 0, unverifiable: 1"],
        ["VERIFIED", "BROKEN"],
    ),
    (
        "unannotated federation ref → INFO (unchanged behaviour), exit 0",
        f"Pattern: {CTX_REF}\n",
        (),
        (("Contextus", None),),  # sibling present but no annotation → still INFO
        True,
        None,
        0,
        ["FEDERATION (not verified)", "annotated: 0, verified: 0, unverifiable: 0"],
        ["VERIFIED", "BROKEN"],
    ),
    (
        "in-repo missing path → BROKEN REF, exit 1 (pre-existing contract)",
        "See `docs/does-not-exist.md`.\n",
        (),
        (),
        True,
        None,
        1,
        ["BROKEN REF: docs/does-not-exist.md"],
        [],
    ),
    (
        "in-repo existing path → exit 0 and counted (in-repo: 2 checked)",
        "See `docs/a.md` and `scripts/b.py`.\n",
        ("docs/a.md", "scripts/b.py"),
        (),
        True,
        None,
        0,
        ["in-repo: 2 checked"],
        ["BROKEN"],
    ),
    (
        "in-repo FAIL + verified sibling → exit 1 (in-repo FAIL still wins)",
        f"See `docs/missing.md`. {CTX_REF} {CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        1,
        ["BROKEN REF: docs/missing.md", "VERIFIED on sibling Contextus"],
        [],
    ),
    (
        "orphan annotation (declares a path that is not the ref) → exit 1",
        f"Pattern: {CTX_REF} <!-- expected-on-sibling: Contextus doc/other.md -->\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        1,
        ["ORPHAN ANNOTATION"],
        ["VERIFIED"],
    ),
    (
        "orphan annotation two lines below the ref → exit 1 (adjacency is strict)",
        f"Pattern: {CTX_REF}\n\n{CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        1,
        ["ORPHAN ANNOTATION"],
        [],
    ),
    (
        "malformed annotation (`..` in path) → exit 1",
        "`~/Documents/Contextus/../etc/passwd` "
        "<!-- expected-on-sibling: Contextus ../etc/passwd -->\n",
        (),
        (("Contextus", None),),
        True,
        None,
        1,
        ["MALFORMED ANNOTATION"],
        ["VERIFIED"],
    ),
    (
        "malformed annotation (repo with slash) → exit 1",
        "`~/Documents/a/b/c.md` <!-- expected-on-sibling: a/b c.md -->\n",
        (),
        (),
        True,
        None,
        1,
        ["MALFORMED ANNOTATION"],
        [],
    ),
    (
        "annotation inside a code fence is ignored → ref stays INFO, exit 0",
        f"```\n{CTX_REF} {CTX_ANN}\n```\nOutside: {CTX_REF}\n",
        (),
        (("Contextus", None),),
        True,
        None,
        0,
        ["FEDERATION (not verified)", "annotated: 0"],
        ["VERIFIED", "BROKEN", "ORPHAN"],
    ),
    (
        "code fence does not break line adjacency (annotation after fence binds)",
        f"```\nnoise\nmore noise\n```\n{CTX_REF}\n{CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        0,
        ["VERIFIED on sibling Contextus"],
        ["ORPHAN"],
    ),
    (
        "ref with § anchor still binds to its annotation",
        f"See `~/Documents/Contextus/doc/contextus-tenancy-pattern.md §3.4` {CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        0,
        ["VERIFIED on sibling Contextus"],
        ["ORPHAN"],
    ),
    (
        "QBP_SIBLING_ROOT env override is honoured (no --sibling-root flag)",
        f"Pattern: {CTX_REF} {CTX_ANN}\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        {"QBP_SIBLING_ROOT": "{sroot}"},
        0,
        ["VERIFIED on sibling Contextus"],
        ["not verifiable"],
    ),
    (
        "same path twice, annotated once → counted once, VERIFIED",
        f"A: {CTX_REF} {CTX_ANN}\n\nTable row | {CTX_REF} | exists\n",
        (),
        (("Contextus", "doc/contextus-tenancy-pattern.md"),),
        True,
        None,
        0,
        ["federation: 1 total — annotated: 1, verified: 1"],
        ["not verified"],
    ),
]


def main():
    failures = 0
    for name, doc, files, sibs, sroot, env, exp, must, must_not in CASES:
        got, out = run(doc, files, sibs, sroot, env)
        ok = got == exp
        missing = [s for s in must if s not in out]
        present = [s for s in must_not if s in out]
        ok = ok and not missing and not present
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        if missing:
            print(f"         missing from output: {missing}")
        if present:
            print(f"         unexpectedly in output: {present}")
        if not ok and (missing or present):
            print("         --- output ---")
            for ln in out.rstrip().split("\n"):
                print(f"         {ln}")
        failures += not ok

    # The CI workflow must run this test file alongside the linter so the
    # contract above is enforced, not just documented.
    wf = open(WORKFLOW).read()
    wf_ok = "scripts/test_tenancy_xref_linter.py" in wf
    print(
        f"  [{'PASS' if wf_ok else 'FAIL'}] workflow runs test_tenancy_xref_linter.py"
    )
    failures += not wf_ok

    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print(f"\nAll {len(CASES) + 1} tenancy xref linter tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
