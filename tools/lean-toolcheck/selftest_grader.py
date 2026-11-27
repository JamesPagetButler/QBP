"""Grader self-test: planted negative controls (PR #824 Red Team + Gemini rounds).

Takes the raw results of a real GREEN run, plants one defect per COPY, and runs the grader
on each copy; every plant must be caught (or, for spoofs, neutralised). Optionally also runs
an OLD grader (e.g. the toolcheck.py of commit de19998) to show the defect it missed.

usage: selftest_grader.py SUITE RAW_DIR WORK_DIR [OLD_TOOLCHECK]
  RAW_DIR = results/runs/<run-id>/raw of a full GREEN run; WORK_DIR is wiped and reused.
Exit 0 iff the unplanted run is GREEN and every plant behaved as required.
"""

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

suite, raw, work = map(Path, sys.argv[1:4])
old_tc = Path(sys.argv[4]) if len(sys.argv) > 4 else None
new_tc = suite / "toolcheck.py"
LSIG = (
    "def lean_parse_subset(src: str, raw: Path, stem: str, fmeta: dict) -> list[str]:\n"
)
if work.exists():
    shutil.rmtree(work)
work.mkdir(parents=True)


class _NoRows(dict):
    """Rows of a grader run that produced no output: every lookup is a failed row."""

    def __missing__(self, key):
        return {
            "file": key,
            "result": "NO-OUTPUT",
            "failures": ["grader produced no output"],
            "detections": [],
            "structural_audit": None,
        }


NO_OUTPUT: list[str] = []
ok = True


def evaluate(
    tc: Path, rawdir: Path, suitedir: Path, tag: str, recheck: bool = False
) -> dict:
    out_j, out_m = work / f"{tag}.json", work / f"{tag}.md"
    r = subprocess.run(
        [
            "python3",
            "-I",
            str(tc),
            "evaluate",
            "--raw",
            str(rawdir),
            "--suite",
            str(suitedir),
            "--meta",
            str(rawdir / "meta.json"),
            "--out-json",
            str(out_j),
            "--out-md",
            str(out_m),
        ]
        + (
            []
            if recheck or "--skip-input-recheck" not in tc.read_text()
            else ["--skip-input-recheck"]
        ),  # older graders (OLD replays) have no such flag
        capture_output=True,
        text=True,
    )
    if not out_j.exists():
        global ok, NO_OUTPUT
        ok = False
        NO_OUTPUT.append(
            f"{tag}: grader exit {r.returncode}, no output ({r.stderr.strip()[-160:]})"
        )
        return {
            "exit": r.returncode,
            "rows": _NoRows(),
            "overall": "NO-OUTPUT",
            "pre": ["grader produced no output"],
        }
    d = json.loads(out_j.read_text())
    return {
        "exit": r.returncode,
        "rows": {f["file"].split("/")[-1]: f for f in d["files"]},
        "overall": d["summary"]["overall"],
        "pre": d.get("preflight_failures", []),
    }


def row(res, name):
    f = res["rows"][name]
    return f"{f['result']}: " + "; ".join(f["failures"] or f["detections"])[:230]


results = []
# 0. baseline: the real run, new grader
base = evaluate(new_tc, raw, suite, "base")
results.append(("real run, NEW grader", base["overall"], f"exit {base['exit']}"))

ok = ok and base["overall"] == "GREEN"
# 1. optionally demonstrate the bugs with an OLD grader on the same raw logs
old = evaluate(old_tc, raw, suite, "old") if old_tc is not None else None
for n in ("MF06_SpoofedAudit.lean", "T19_NestedComments.lean"):
    if old is not None:
        results.append((f"OLD grader on {n}", row(old, n), ""))
    results.append((f"NEW grader on {n}", row(base, n), ""))
    ok = ok and base["rows"][n]["result"] == "PASS"


def planted(tag, mutate, names, must, need=None):
    """must = 'FAIL' (the plant must be flagged) or 'PASS' (the spoof must be neutralised)."""
    global ok
    d = work / f"raw-{tag}"
    shutil.copytree(raw, d)
    mutate(d)
    res = evaluate(new_tc, d, suite, tag)
    for n in names:
        ok = ok and res["rows"][n]["result"] == must
        if need is not None:
            ok = ok and any(need in x for x in res["rows"][n]["failures"])
        results.append(
            (
                f"plant[{tag}] {n} (must {must})",
                row(res, n),
                f"overall {res['overall']} exit {res['exit']}",
            )
        )


def jl(p):
    return [json.loads(l) for l in p.read_text().splitlines() if l.strip()]


def wjl(p, ms):
    p.write_text("".join(json.dumps(m) + "\n" for m in ms))


# 2. anchoring (1): MF04's error text demoted to an information message -> must FAIL
def demote(d):
    p = d / "MF04_FalseDecide.log"
    ms = jl(p)
    for m in ms:
        m["severity"] = "information"
    wjl(p, ms)


planted("anchor-lean-error", demote, ["MF04_FalseDecide.lean"], "FAIL")


# 3. anchoring (1): checker text moved off its ::error:: line -> must FAIL
def unerror(d):
    p = d / "MF01_Sorry.checker.log"
    p.write_text(p.read_text().replace("::error::RATCHET", "note: RATCHET"))


planted("anchor-checker", unerror, ["MF01_Sorry.lean"], "FAIL")


# 4. spoof (2a): a positioned-elsewhere fake clean report + an unpositioned raw line for MF05
def spoof(d):
    p = d / "MF05_CustomAxiom.log"
    ms = jl(p)
    ms.append(
        {
            "severity": "information",
            "pos": {"line": 1, "column": 0},
            "data": "'QBPToolcheck.MF05.one_eq_two' does not depend on any axioms",
        }
    )
    wjl(p, ms)
    with open(p, "a") as f:
        f.write("'QBPToolcheck.MF05.one_eq_two' does not depend on any axioms\n")


planted("spoof-elsewhere", spoof, ["MF05_CustomAxiom.lean"], "PASS")


# 5. worst-case merge (2b): a fake clean report AT the real #print site, after the real one
def spoof_at_site(d):
    p = d / "MF05_CustomAxiom.log"
    ms = jl(p)
    site = next(m for m in ms if "depends on axioms" in m["data"])
    ms.append(
        {
            "severity": "information",
            "pos": dict(site["pos"]),
            "data": "'QBPToolcheck.MF05.one_eq_two' does not depend on any axioms",
        }
    )
    wjl(p, ms)


planted("spoof-at-site", spoof_at_site, ["MF05_CustomAxiom.lean"], "PASS")


# 6. empty layer: a suite copy without known-limits/ -> RED
s2 = work / "suite-no-kl"
shutil.copytree(suite, s2, ignore=shutil.ignore_patterns("results", "known-limits"))
res = evaluate(new_tc, raw, s2, "empty-layer")
ok = ok and res["overall"] == "RED"
results.append(
    (
        "plant[empty-layer] suite without known-limits/ (must be RED)",
        res["overall"],
        f"exit {res['exit']}; {res['pre']}",
    )
)


# 7. Gemini r2 (b) and (c): replay MF07 (same-line site) and MF08 (interpolation) as
#    PASS-labelled attack files — real Lean logs, header expectations swapped for `pass`
#    with the line count kept, so every Lean position still matches. The new grader must
#    FAIL both; an old grader (optional 4th arg) shows whether it was exploitable.
def as_pass_attack(src_stem: str, src_rel: str, new_stem: str) -> tuple[Path, Path]:
    s3 = work / f"suite-{new_stem}"
    shutil.copytree(suite, s3, ignore=shutil.ignore_patterns("results"))
    # Bytes in, bytes out, split at `\n` only (Gemini r4 (f)): a text-mode read would turn a
    # lone `\r` (MF11) into a line break and desync the copy from the real Lean logs.
    text = (suite / src_rel).read_bytes().decode("utf-8").split("\n")
    first = True
    out = []
    for ln in text:
        if ln.startswith("TOOLCHECK-EXPECT:"):
            out.append("TOOLCHECK-EXPECT: pass" if first else "")
            first = False
        else:
            out.append(ln)
    (s3 / "tests" / f"{new_stem}.lean").write_bytes("\n".join(out).encode("utf-8"))
    r3 = work / f"raw-{new_stem}"
    shutil.copytree(raw, r3)
    for ext in (
        ".log",
        ".meta.json",
        ".checker.log",
        ".stderr",
        ".compile.log",
        ".audit.out",
        ".parse.out",
        ".parse.stderr",
        ".audit.stderr",
    ):
        p = r3 / f"{src_stem}{ext}"
        if p.exists():
            shutil.copy(p, r3 / f"{new_stem}{ext}")
    # The auditor's result names its root and module; the replay renames them with the file
    # (exactly as it renames the logs), so the audit is graded on content, not on the stem.
    a = r3 / f"{new_stem}.audit.out"
    if a.exists():
        a.write_text(
            a.read_text()
            .replace(f'"root":"{src_stem}"', f'"root":"{new_stem}"')
            .replace(f"ToolcheckAudit.{src_stem}", f"ToolcheckAudit.{new_stem}")
        )
    return s3, r3


for src_stem, src_rel, new_stem in (
    (
        "MF07_SameLineSite",
        "must-fail/MF07_SameLineSite/MF07_SameLineSite.lean",
        "T90_AttackSameLine",
    ),
    (
        "MF08_InterpolationLexer",
        "must-fail/MF08_InterpolationLexer/MF08_InterpolationLexer.lean",
        "T91_AttackInterpolation",
    ),
    (
        "MF09_NonAsciiColumn",
        "must-fail/MF09_NonAsciiColumn/MF09_NonAsciiColumn.lean",
        "T92_AttackNonAsciiColumn",
    ),
    (
        "MF10_FormFeedLineDesync",
        "must-fail/MF10_FormFeedLineDesync/MF10_FormFeedLineDesync.lean",
        "T93_AttackFormFeedLines",
    ),
    (
        "MF11_LoneCRLineDesync",
        "must-fail/MF11_LoneCRLineDesync/MF11_LoneCRLineDesync.lean",
        "T94_AttackLoneCRLines",
    ),
    (
        "MF14_ExecForgesStdout",
        "must-fail/MF14_ExecForgesStdout/MF14_ExecForgesStdout.lean",
        "T98_AttackExecForge",
    ),
    (
        "MF13_CleanBraceRefused",
        "must-fail/MF13_CleanBraceRefused/MF13_CleanBraceRefused.lean",
        "T97_AttackCleanBrace",
    ),
    (
        "MF15_SyntaxAttributeHandler",
        "must-fail/MF15_SyntaxAttributeHandler/MF15_SyntaxAttributeHandler.lean",
        "T80_AttackSyntaxAttribute",
    ),
    (
        "MF16_HandlerNotFirstAttr",
        "must-fail/MF16_HandlerNotFirstAttr/MF16_HandlerNotFirstAttr.lean",
        "T81_AttackHandlerNotFirst",
    ),
    (
        "MF17_MacroBuildsEval",
        "must-fail/MF17_MacroBuildsEval/MF17_MacroBuildsEval.lean",
        "T82_AttackMacroEval",
    ),
    (
        "MF18_TermElabHandler",
        "must-fail/MF18_TermElabHandler/MF18_TermElabHandler.lean",
        "T83_AttackTermElab",
    ),
    (
        "MF19_IndentedSimprocForge",
        "must-fail/MF19_IndentedSimprocForge/MF19_IndentedSimprocForge.lean",
        "T84_AttackIndentedSimproc",
    ),
    (
        "MF20_OpenInSimprocForge",
        "must-fail/MF20_OpenInSimprocForge/MF20_OpenInSimprocForge.lean",
        "T85_AttackOpenInSimproc",
    ),
    (
        "MF21_SimprocPatternForgesOlean",
        "must-fail/MF21_SimprocPatternForgesOlean/MF21_SimprocPatternForgesOlean.lean",
        "T88_AttackSimprocPatternOlean",
    ),
    (
        "MF23_RawStringLexDesync",
        "must-fail/MF23_RawStringLexDesync/MF23_RawStringLexDesync.lean",
        "T89_AttackRawStringDesync",
    ),
    (
        "MF24_GuillemetLexDesync",
        "must-fail/MF24_GuillemetLexDesync/MF24_GuillemetLexDesync.lean",
        "T90_AttackGuillemetDesync",
    ),
):
    s3, r3 = as_pass_attack(src_stem, src_rel, new_stem)
    res = evaluate(new_tc, r3, s3, new_stem)
    got = res["rows"][f"{new_stem}.lean"]["result"]
    ok = ok and got == "FAIL"
    results.append(
        (
            f"plant[{new_stem}] pass-labelled attack, NEW grader (must FAIL)",
            row(res, f"{new_stem}.lean"),
            "",
        )
    )
    if old_tc is not None:
        res_old = evaluate(old_tc, r3, s3, new_stem + "-old")
        results.append(
            (
                f"plant[{new_stem}] pass-labelled attack, OLD grader",
                row(res_old, f"{new_stem}.lean"),
                "",
            )
        )


# 7b. Red Team on PR #824 (19bbbd4): plants whose outcome DEPENDS on each guard, so a mutant
#     that drops the guard is killed (the union merge alone absorbed every earlier spoof).
def drop_real_and_forge(sev, at_site):
    def mut(p):
        ms = jl(p)
        real = next(m for m in ms if "depends on axioms" in m["data"])
        thm = real["data"].split("'")[1]
        ms = [m for m in ms if m is not real]
        ms.append(
            {
                "severity": sev,
                "pos": dict(real["pos"]) if at_site else {"line": 1, "column": 0},
                "data": f"'{thm}' does not depend on any axioms",
            }
        )
        wjl(p, ms)

    return mut


# The real report of one T01 theorem is removed and a forged clean report put elsewhere. T01 is
# inside the pass-file subset, so ONLY the position / severity guard can fail it.
def t01_guard(sev, at_site):
    def mut(d):
        drop_real_and_forge(sev, at_site)(d / "T01_DecideFin.log")

    return mut


for tag, mut, what in (
    # M10: the real report is absent; a forged clean `information` report sits OFF the site.
    ("T96-forged-offsite", t01_guard("information", False), "position"),
    # M11: the real report is absent; a forged clean report sits AT the site as a `warning`.
    ("T96b-forged-warning-at-site", t01_guard("warning", True), "severity"),
):
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")


# M19: MF13 with the brace replaced in the SOURCE copy (same length, so Lean's positions still
# match): it still expects `grader-refuses`, the grader no longer refuses -> must FAIL.
def unbrace_mf13(s4):
    f = s4 / "must-fail/MF13_CleanBraceRefused/MF13_CleanBraceRefused.lean"
    f.write_bytes(f.read_bytes().replace(b'"a { b"', b'"a x b"'))


# M15: MF01's checker regex UNANCHORED in the suite copy, and the matching checker text moved
# onto a `note:` line: only the "`::error` lines only" filter can still fail it.
def unanchor_mf01(s4):
    f = s4 / "must-fail/MF01_Sorry/MF01_Sorry.lean"
    f.write_bytes(
        f.read_bytes().replace(
            b"checker-reject ^::error::RATCHET", b"checker-reject RATCHET"
        )
    )


def note_mf01(d):
    p = d / "MF01_Sorry.checker.log"
    p.write_text(p.read_text().replace("::error::RATCHET", "note: RATCHET"))


for tag, suite_mut, raw_mut, name in (
    ("refuse-expected-not-refused", unbrace_mf13, None, "MF13_CleanBraceRefused.lean"),
    ("checker-unanchored", unanchor_mf01, note_mf01, "MF01_Sorry.lean"),
):
    s4 = work / f"suite-{tag}"
    shutil.copytree(suite, s4, ignore=shutil.ignore_patterns("results"))
    suite_mut(s4)
    r4 = work / f"raw-{tag}"
    shutil.copytree(raw, r4)
    if raw_mut is not None:
        raw_mut(r4)
    res = evaluate(new_tc, r4, s4, tag)
    ok = ok and res["rows"][name]["result"] == "FAIL"
    results.append((f"plant[{tag}] {name} (must FAIL)", row(res, name), ""))


# M34: a `subset-refused` file that is in fact INSIDE the subset must FAIL. T20's three refused
# lines are commented out in a suite copy (line count unchanged; T20 has no `#print axioms`).
s7 = work / "suite-subset-refused-unmet"
shutil.copytree(suite, s7, ignore=shutil.ignore_patterns("results"))
t20 = s7 / "tests" / "T20_SubsetRefusedFeatures.lean"
body = t20.read_bytes().decode("utf-8")
for bad in (
    'local notation "⇄" p => Pair.swap p',
    "section LocalSimp",
    "attribute [local simp] double",
):
    assert body.count(bad) == 1
    body = body.replace(bad, "-- " + bad)
t20.write_bytes(body.encode("utf-8"))
# The source is edited AFTER the run, so T20's real Lean-parser record no longer matches it; this
# plant tests the `subset-refused` expectation logic, so its grader copy has the Lean layer off.
tc7 = s7 / "toolcheck.py"
t7 = tc7.read_text()
assert t7.count(LSIG) == 1
tc7.write_text(
    t7.replace(LSIG, LSIG + "    return []  # SELFTEST: source edited after the run\n")
)
res = evaluate(tc7, raw, s7, "subset-refused-unmet")
ok = ok and res["rows"]["T20_SubsetRefusedFeatures.lean"]["result"] == "FAIL"
results.append(
    (
        "plant[subset-refused-unmet] T20 with its refused lines commented out (must FAIL)",
        row(res, "T20_SubsetRefusedFeatures.lean"),
        "",
    )
)


# Fail-closed rules on a CLEAN pass file (T01): each plant alone must turn it FAIL.
def t01_dup(d):
    p = d / "T01_DecideFin.log"
    ms = jl(p)
    wjl(p, ms + [dict(next(m for m in ms if "axioms" in m["data"]))])


def t01_offsite(d):
    p = d / "T01_DecideFin.log"
    ms = jl(p)
    site = next(m for m in ms if "axioms" in m["data"])
    wjl(p, ms + [{**site, "pos": {"line": 1, "column": 0}}])


def t01_untrusted(d):
    p = d / "T01_DecideFin.log"
    p.write_text(p.read_text() + "printed by code, not a Lean message\n")


for tag, mut in (
    ("pass-duplicate-at-site", t01_dup),
    ("pass-forged-offsite", t01_offsite),
    ("pass-untrusted-stdout", t01_untrusted),
):
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")


# M18: a JSON line WITHOUT `severity` at a real site, replacing the real report: only Lean's
# message shape (severity + data) may be trusted, so this must FAIL.
def t01_no_severity(d):
    p = d / "T01_DecideFin.log"
    ms = jl(p)
    real = next(m for m in ms if "axioms" in m["data"])
    thm = real["data"].split("'")[1]
    forged = {
        "pos": dict(real["pos"]),
        "data": f"'{thm}' does not depend on any axioms",
    }
    wjl(p, [m for m in ms if m is not real] + [forged])


planted("pass-json-without-severity", t01_no_severity, ["T01_DecideFin.lean"], "FAIL")

# M16: a `#print axioms` INSIDE a string literal is not a command. T19's string body is replaced
# (same length, so Lean's positions still match) by a fake site; the grader must ignore it and
# the file must still PASS (a grader that kept strings would demand a report for it).
s5 = work / "suite-site-in-string"
shutil.copytree(suite, s5, ignore=shutil.ignore_patterns("results"))
t19 = s5 / "tests" / "T19_NestedComments.lean"
body = "/- not a comment -- nor this"
fake = "#print axioms QBPToolcheck.X"
assert len(fake) == len(body)
t19.write_bytes(t19.read_bytes().replace(body.encode(), fake.encode()))
res = evaluate(new_tc, raw, s5, "site-in-string")
ok = ok and res["rows"]["T19_NestedComments.lean"]["result"] == "PASS"
results.append(
    (
        "plant[site-in-string] T19 with `#print axioms` inside a string (must PASS)",
        row(res, "T19_NestedComments.lean"),
        "",
    )
)


SUBSET_PLANTS = [
    # rule D: each refused keyword, mid-line
    *[
        ("D", f"  x {w} y")
        for w in (
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
            "ofReduceBool",
            "reduceBool",
            "plausible",
            "slim_check",
        )
    ],
    ("D", "  decide +native"),
    # rule B: `#` commands other than `#print axioms`, mid-line
    ("B", "  #eval 1"),
    ("B", "  #guard true"),
    ("B", "  #sample Nat"),
    ("B", "  #check 1"),
    ("B", "  #print foo"),
    # rule C: attribute lists, mid-line (handler not first; unknown attribute; unclosed)
    ("C", "  @[simp, command_elab foo] def x := 1"),
    ("C", "  @[inline] def x := 1"),
    ("C", "  @[local simp] def x := 1"),
    ("C", "  @[simp"),
    # rule A: column-0 commands outside the allowlist, and its two sub-checks
    ("A", "alias foo := bar"),
    ("A", "qbp_custom_command"),
    ("A", "noncomputable instance : Inhabited Nat := ⟨0⟩"),
    ("A", "#print foo"),
]


def subset_plant(tag, line):
    s6 = work / f"suite-subset-{tag}"
    shutil.copytree(suite, s6, ignore=shutil.ignore_patterns("results"))
    f = s6 / "tests" / "T01_DecideFin.lean"
    body = f.read_bytes().decode("utf-8")
    f.write_bytes((body.rstrip("\n") + "\n" + line + "\n").encode("utf-8"))
    return s6


n_subset = 0
for k, (rule_id, line) in enumerate(SUBSET_PLANTS):
    s6 = subset_plant(f"{k:02d}", line)
    res = evaluate(new_tc, raw, s6, f"subset-{k:02d}")
    got = res["rows"]["T01_DecideFin.lean"]["result"]
    good = got == "FAIL"
    ok = ok and good
    n_subset += good
    if not good:
        results.append(
            (f"plant[subset {rule_id}] T01 + `{line.strip()}` (must FAIL)", got, "")
        )
results.append(
    (
        f"plant[subset] {len(SUBSET_PLANTS)} refused constructs appended to clean T01 (each must FAIL)",
        f"{n_subset}/{len(SUBSET_PLANTS)} FAIL",
        "",
    )
)


# 7c. Red Team r3 / director ruling: the STRUCTURAL audit alone (scope of the claim, Red Team r4:
#     MF05 is a real axiom the auditor sees; the five forge files exit BEFORE any .olean exists,
#     so they fail closed. A file that writes its own .olean is NOT caught by the audit alone:
#     see the S1 row below). A grader copy whose
#     `subset_violations` always returns [] (every subset rule off) grades the pass-labelled
#     replays of the forge files and of MF05 (a plain user axiom): each must still FAIL, and
#     the failure must come from the structural audit (PR #829 auditor on a fresh .olean).
s8 = work / "suite-subset-off"
shutil.copytree(suite, s8, ignore=shutil.ignore_patterns("results"))
tc8 = s8 / "toolcheck.py"
t8 = tc8.read_text()
sig = "def subset_violations(src: str) -> list[str]:\n"
assert t8.count(sig) == 1
assert t8.count(LSIG) == 1
tc8.write_text(
    t8.replace(sig, sig + "    return []  # SELFTEST: every subset rule off\n").replace(
        LSIG, LSIG + "    return []  # SELFTEST: the Lean-parser layer off too\n"
    )
)
for src_stem, new_stem in (
    ("MF05_CustomAxiom", "T76_StructuralOnlyAxiom"),
    ("MF14_ExecForgesStdout", "T77_StructuralOnlyEval"),
    ("MF15_SyntaxAttributeHandler", "T78_StructuralOnlyHandler"),
    ("MF17_MacroBuildsEval", "T79_StructuralOnlyMacro"),
    ("MF19_IndentedSimprocForge", "T84s_StructuralOnlyIndented"),
    ("MF20_OpenInSimprocForge", "T85s_StructuralOnlyOpenIn"),
):
    s9, r9 = as_pass_attack(src_stem, f"must-fail/{src_stem}/{src_stem}.lean", new_stem)
    shutil.copy(tc8, s9 / "toolcheck.py")
    res = evaluate(s9 / "toolcheck.py", r9, s9, new_stem)
    f = res["rows"][f"{new_stem}.lean"]
    by_audit = any(x.startswith("structural audit") for x in f["failures"])
    good = f["result"] == "FAIL" and by_audit
    ok = ok and good
    results.append(
        (
            f"structural-only[{new_stem}] subset rules OFF (must FAIL by the structural audit)",
            ("FAIL by audit: " if good else "NOT CAUGHT BY AUDIT: ")
            + "; ".join(x for x in f["failures"] if x.startswith("structural audit"))[
                :200
            ],
            "",
        )
    )


# S1 (PR #829's stated limit, QBP#836; Red Team r4 T86/T88): with every subset rule off, a file
# that writes a clean .olean of its own module name to the compile's -o path is EXPECTED to PASS
# the structural audit. MF21 (T88: `simproc_pattern%`) and MF22 (T86: a REAL `axiom cheat` plus
# an `#eval`) both do. These rows document that the subset is the PRECONDITION for the structural
# verdict (the earlier "auditor alone" rows above only cover files that exit before any .olean
# exists). If one ever FAILs, the limit changed: re-read the README layering.
for src_stem, new_stem, what in (
    ("MF21_SimprocPatternForgesOlean", "T88s_StructuralOnlyS1", "MF21 (T88)"),
    (
        "MF22_AxiomEvalForgesOlean",
        "T86s_StructuralOnlyS1Axiom",
        "MF22 (T86, real axiom)",
    ),
):
    s12, r12 = as_pass_attack(
        src_stem, f"must-fail/{src_stem}/{src_stem}.lean", new_stem
    )
    shutil.copy(tc8, s12 / "toolcheck.py")
    res = evaluate(s12 / "toolcheck.py", r12, s12, new_stem)
    f12 = res["rows"][f"{new_stem}.lean"]
    # S1 is a statement about the STRUCTURAL AUDIT: with the subset off it must report the forged
    # .olean as clean. Other, independent layers may still catch the file (since master a44ff37 the
    # foundations checker hard-bans the forge's incidental char literal); those are reported, not
    # required, because a forge could avoid them.
    audit_fails = [x for x in f12["failures"] if x.startswith("structural audit")]
    other = [x for x in f12["failures"] if not x.startswith("structural audit")]
    s1_ok = not audit_fails and bool(f12.get("structural_audit") is not None)
    ok = ok and s1_ok
    results.append(
        (
            f"S1-limit[{new_stem}] {what} with every subset rule OFF (EXPECTED to PASS the audit: the compile wrote a forged .olean)",
            (
                "audit fooled as documented (S1 holds)"
                + (
                    f"; other layers still catch it: {'; '.join(other)[:120]}"
                    if other
                    else ""
                )
                if s1_ok
                else "CHANGED — re-read the S1 limit: " + "; ".join(audit_fails)[:150]
            ),
            "",
        )
    )


# 7d. The structural audit's own guards, on the clean pass file T01's REAL auditor output:
#     each tampering must turn T01 FAIL.
def t01_audit(fn):
    def mut(d):
        p = d / "T01_DecideFin.audit.out"
        lines = [l for l in p.read_text().split("\n") if l.strip()]
        res_i = next(i for i, l in enumerate(lines) if '"AXIOM-AUDIT-827"' in l)
        r = json.loads(lines[res_i])
        out = fn(r, lines, res_i)
        p.write_text(out)

    return mut


def _emit(r, lines, i):
    return "\n".join(lines[:i] + [json.dumps(r)] + lines[i + 1 :]) + "\n"


def _meta_mut(fn):
    def mut(d):
        p = d / "T01_DecideFin.meta.json"
        m = json.loads(p.read_text())
        fn(m)
        p.write_text(json.dumps(m))

    return mut


AUDIT_PLANTS = [
    (
        "audit-nonstd",
        t01_audit(
            lambda r, l, i: _emit(
                {
                    **r,
                    "nonstd": [
                        {
                            "decl": "QBPToolcheck.T01.x",
                            "module": "ToolcheckAudit.T01_DecideFin",
                            "axioms": [
                                {"name": "QBPToolcheck.T01.cheat", "module": ""}
                            ],
                        }
                    ],
                },
                l,
                i,
            )
        ),
    ),
    (
        "audit-wrong-nonce",
        t01_audit(lambda r, l, i: _emit({**r, "nonce": "0" * 32}, l, i)),
    ),
    (
        "audit-wrong-root",
        t01_audit(lambda r, l, i: _emit({**r, "root": "Other"}, l, i)),
    ),
    ("audit-wrong-scope", t01_audit(lambda r, l, i: _emit({**r, "scope": []}, l, i))),
    ("audit-missing", t01_audit(lambda r, l, i: _emit({**r, "missing": ["X"]}, l, i))),
    (
        "audit-unresolved",
        t01_audit(lambda r, l, i: _emit({**r, "unresolved": ["X"]}, l, i)),
    ),
    (
        "audit-shadowed",
        t01_audit(lambda r, l, i: _emit({**r, "shadowed": ["Init.Core"]}, l, i)),
    ),
    (
        "audit-std-forged",
        t01_audit(
            lambda r, l, i: _emit(
                {**r, "std": [{**x, "fp": "forged"} for x in r["std"]]}, l, i
            )
        ),
    ),
    (
        "audit-zero-decls",
        t01_audit(lambda r, l, i: _emit({**r, "declarations": 0}, l, i)),
    ),
    ("audit-two-results", t01_audit(lambda r, l, i: "\n".join(l + [l[i]]) + "\n")),
    (
        "audit-no-result",
        t01_audit(lambda r, l, i: "\n".join(l[:i] + l[i + 1 :]) + "\n"),
    ),
    ("audit-no-olean", _meta_mut(lambda m: m["audit"].update(olean=False))),
    (
        "audit-dangling",
        t01_audit(
            lambda r, l, i: _emit({**r, "dangling": ["QBPToolcheck.T01.ghost"]}, l, i)
        ),
    ),
    (
        "audit-extra-scope",
        t01_audit(
            lambda r, l, i: _emit(
                {**r, "scope": r["scope"] + ["ToolcheckAudit.Extra"]}, l, i
            )
        ),
    ),
    ("audit-auditor-exit-1", _meta_mut(lambda m: m["audit"].update(auditor_exit=1))),
    ("audit-compile-exit-1", _meta_mut(lambda m: m["audit"].update(compile_exit=1))),
    ("audit-no-record", _meta_mut(lambda m: m.pop("audit"))),
]
for tag, mut in AUDIT_PLANTS:
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")


# 7e. Red Team r5 / director decision: the Lean-parser layer (`lean_parse_subset`, rules L/P) on
#     T01's REAL LeanSubsetParse output. Each tampering must turn T01 FAIL.
def t01_parse(fn):
    def mut(d):
        p = d / "T01_DecideFin.parse.out"
        recs = [json.loads(l) for l in p.read_text().split("\n") if l.strip()]
        out = fn(recs)
        p.write_text(
            out
            if isinstance(out, str)
            else "\n".join(json.dumps(r) for r in out) + "\n"
        )

    return mut


def _first_cmd(recs, **kw):
    recs[1].update(kw)
    return recs


def _cmd_add(field, val):
    def f(recs):
        recs[1][field] = list(recs[1].get(field, [])) + [val]
        return recs

    return f


PARSE_PLANTS = [
    (
        "parse-wrong-nonce",
        t01_parse(lambda r: [r[0], {**r[1], "nonce": "0" * 32}] + r[2:]),
    ),
    (
        "parse-kind-not-allowed",
        t01_parse(lambda r: _first_cmd(r, kind="Lean.Parser.Command.eval")),
    ),
    (
        "parse-node-kind-not-allowed",
        t01_parse(_cmd_add("kinds", "Lean.Parser.Command.simprocPattern")),
    ),
    (
        "parse-nested-not-allowed",
        t01_parse(_cmd_add("nested", "Lean.Parser.Command.eval")),
    ),
    ("parse-attr-not-allowed", t01_parse(_cmd_add("attrs", "simple:implemented_by"))),
    (
        "parse-option-not-allowed",
        t01_parse(_cmd_add("set_option", "debug.skipKernelTC")),
    ),
    ("parse-config-native", t01_parse(_cmd_add("config", "native"))),
    ("parse-error", t01_parse(lambda r: _first_cmd(r, parse_error=True))),
    ("parse-scope-error", t01_parse(lambda r: _first_cmd(r, scope_error=True))),
    ("parse-head-col", t01_parse(lambda r: _first_cmd(r, head_col=2))),
    (
        "parse-head-line",
        t01_parse(lambda r: _first_cmd(r, head_line=r[1]["head_line"] + 1)),
    ),
    ("parse-no-done", t01_parse(lambda r: r[:-1])),
    ("parse-done-false", t01_parse(lambda r: r[:-1] + [{**r[-1], "done": False}])),
    ("parse-count-mismatch", t01_parse(lambda r: r[:-1] + [{**r[-1], "commands": 99}])),
    ("parse-dropped-command", t01_parse(lambda r: [r[0]] + r[2:])),
    (
        "parse-not-json",
        t01_parse(lambda r: "\n".join(json.dumps(x) for x in r) + "\nnot json\n"),
    ),
    (
        "parse-import-outside",
        t01_parse(
            lambda r: [{**r[0], "imports": r[0]["imports"] + ["QBP.Foo"]}] + r[1:]
        ),
    ),
    (
        "parse-header-error",
        t01_parse(lambda r: [{**r[0], "parse_error": True}] + r[1:]),
    ),
    ("parse-exit-1", _meta_mut(lambda m: m["subset_parse"].update(exit=1))),
    ("parse-no-record", _meta_mut(lambda m: m.pop("subset_parse"))),
    (
        "auditor-pin-mismatch",
        _meta_mut(
            lambda m: (
                m.update(auditor={**m["auditor"], "sha256": "0" * 64})
                if "auditor" in m
                else None
            )
        ),
    ),
]


def _run_meta_mut(fn):
    def mut(d):
        p = d / "meta.json"
        m = json.loads(p.read_text())
        fn(m)
        p.write_text(json.dumps(m))

    return mut


# The auditor pin lives in the RUN meta (run.sh records the sha256s); per-file meta has none.
PARSE_PLANTS[-1] = (
    "auditor-pin-mismatch",
    _run_meta_mut(lambda m: m["auditor"].update(sha256="0" * 64)),
)
PARSE_PLANTS.append(
    (
        "checker-pin-mismatch",
        _run_meta_mut(lambda m: m["auditor"].update(checker_sha256="0" * 64)),
    )
)
for tag, mut in PARSE_PLANTS:
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")


# 7f. Red Team r6 concern 2: every Lean-parser record field is REQUIRED and typed. Each field of
#     the header, the first command and the done line is deleted in turn, and three are given the
#     wrong type: T01 must FAIL every time.
FIELD_PLANTS = []
for where, idx, fields in (
    ("header", 0, ["nonce", "header", "imports", "parse_error"]),
    (
        "command",
        1,
        [
            "nonce",
            "i",
            "line",
            "col",
            "head_line",
            "head_col",
            "kind",
            "nested",
            "nested_heads",
            "kinds",
            "attrs",
            "set_option",
            "config",
            "parse_error",
            "scope_error",
        ],
    ),
    ("done", -1, ["nonce", "done", "commands", "parse_errors", "scope_errors"]),
):
    for fld in fields:

        def _drop(recs, idx=idx, fld=fld):
            recs[idx].pop(fld, None)
            return recs

        # The structural fields are caught by earlier checks (nonce, header … done, `i`); every
        # other field must be reported AS MISSING (Red Team r8: so the shape check is killable).
        FIELD_PLANTS.append(
            (
                f"field-missing-{where}-{fld}",
                t01_parse(_drop),
                (
                    None
                    if fld in ("nonce", "header", "done", "i")
                    else f"field `{fld}` is missing"
                ),
            )
        )
for tag, idx, fld, val in (
    ("field-type-command-kinds", 1, "kinds", "Lean.Parser.Command.declaration"),
    ("field-type-header-imports", 0, "imports", "Mathlib"),
    ("field-type-command-nested_heads", 1, "nested_heads", [[1]]),
    ("field-type-command-head_line", 1, "head_line", "21"),
    ("field-type-done-commands", -1, "commands", True),
):

    def _retype(recs, idx=idx, fld=fld, val=val):
        recs[idx][fld] = val
        return recs

    FIELD_PLANTS.append((tag, t01_parse(_retype), f"field `{fld}` has the wrong type"))
for tag, mut, need in FIELD_PLANTS:
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL", need)


# 7g. Red Team r6 concern 1(b): writes into the THROWAWAY suite copy, attributed per file.
def _mf25_meta(fn):
    def mut(d):
        q = d / "MF25_WritesSuiteInput.meta.json"
        m = json.loads(q.read_text())
        fn(m)
        q.write_text(json.dumps(m))

    return mut


for tag, mut, name in (
    (
        "writes-unexpected",
        _meta_mut(lambda m: m.update(suite_copy_writes=["toolcheck.py"])),
        "T01_DecideFin.lean",
    ),
    (
        "writes-record-missing",
        _meta_mut(lambda m: m.pop("suite_copy_writes")),
        "T01_DecideFin.lean",
    ),
    (
        "writes-record-wrong-type",
        _meta_mut(lambda m: m.update(suite_copy_writes="toolcheck.py")),
        "T01_DecideFin.lean",
    ),
    (
        "writes-expected-unmet",
        _mf25_meta(lambda m: m.update(suite_copy_writes=[])),
        "MF25_WritesSuiteInput.lean",
    ),
):
    planted(tag, mut, [name], "FAIL")

# The real run: MF25's write was attributed to MF25 (and only to it), and the run's own input
# verification passed, so the REAL tree was unchanged after every file had run.
m25 = json.loads((raw / "MF25_WritesSuiteInput.meta.json").read_text())
others = [
    q.name
    for q in raw.glob("*.meta.json")
    if q.name
    not in ("MF25_WritesSuiteInput.meta.json", "MF91_DetachedSurvivor.meta.json")
    and json.loads(q.read_text()).get("suite_copy_writes")
]
ver = json.loads((raw / "inputs.verify.json").read_text())
real_ok = (
    m25.get("suite_copy_writes") == ["subset_kinds.json"]
    and not others
    and ver.get("ok") is True
)
ok = ok and real_ok
results.append(
    (
        "real-run[MF25] write attributed to MF25 only; real tree unchanged (inputs.verify ok)",
        f"MF25 writes {m25.get('suite_copy_writes')}; other writers {others}; verify ok={ver.get('ok')}",
        "",
    )
)


# 7g'. Red Team r7 (MF91): the per-file SURVIVOR check (`late_writes`).
for tag, mut in (
    (
        "late-writes-present",
        _meta_mut(lambda m: m.update(late_writes=["suite-copy/.mf91-alive"])),
    ),
    ("late-writes-record-missing", _meta_mut(lambda m: m.pop("late_writes"))),
    ("late-writes-record-wrong-type", _meta_mut(lambda m: m.update(late_writes="x"))),
):
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")
# The real run: MF91's daemon wrote heartbeats while its --json run was alive (attributed to
# MF91), and NOTHING was written after any file's Lean processes ended (no survivor), because
# the PID namespace killed it.
m91 = json.loads((raw / "MF91_DetachedSurvivor.meta.json").read_text())
late_any = [
    q.name
    for q in raw.glob("*.meta.json")
    if json.loads(q.read_text()).get("late_writes")
]
r91 = (
    ".mf91-alive" in " ".join(m91.get("suite_copy_writes", []))
    and m91.get("late_writes") == []
    and not late_any
)
ok = ok and r91
results.append(
    (
        "real-run[MF91] detached daemon wrote only while its Lean process lived; no survivor anywhere",
        f"MF91 writes {m91.get('suite_copy_writes')}; MF91 late {m91.get('late_writes')}; files with late writes {late_any}",
        "",
    )
)


# 7i. Red Team r8 (MF93): the raw-record SEAL.
def _seal_edit(fn):
    def mut(d):
        q = d / "seal.verify.json"
        m = json.loads(q.read_text())
        fn(m)
        q.write_text(json.dumps(m))

    return mut


for tag, mut, name in (
    (
        "seal-tampered-T01",
        _seal_edit(lambda m: m["tampered"].append("T01_DecideFin")),
        "T01_DecideFin.lean",
    ),
    (
        "seal-decoy-held",
        _seal_edit(
            lambda m: m.update(
                tampered=[x for x in m["tampered"] if x != "MF93a_SealDecoy"]
            )
        ),
        "MF93a_SealDecoy.lean",
    ),
    (
        "seal-record-missing",
        lambda d: (d / "seal.verify.json").unlink(),
        "T01_DecideFin.lean",
    ),
    # Red Team r9 Q4: with NO seal record, the decoy must not be accepted either.
    (
        "seal-record-missing-decoy",
        lambda d: (d / "seal.verify.json").unlink(),
        "MF93a_SealDecoy.lean",
    ),
    (
        "seal-record-mistyped",
        _seal_edit(lambda m: m.update(tampered="T01_DecideFin")),
        "T01_DecideFin.lean",
    ),
):
    planted(tag, mut, [name], "FAIL")
# Red Team r9 Q3: a broken RUN-LEVEL seal (`__global`) must make the run RED.
dG = work / "raw-seal-global-tampered"
shutil.copytree(raw, dG)
_sg = json.loads((dG / "seal.verify.json").read_text())
_sg["tampered"] = sorted(set(_sg["tampered"]) | {"__global"})
(dG / "seal.verify.json").write_text(json.dumps(_sg))
res = evaluate(new_tc, dG, suite, "seal-global-tampered")
good = res["overall"] == "RED" and any("run-level raw records" in x for x in res["pre"])
ok = ok and good
results.append(
    (
        "plant[seal-global-tampered] __global seal broken (run must be RED by the run-level check)",
        f"overall {res['overall']}; {res['pre'][:1]}",
        "",
    )
)
shutil.rmtree(dG, ignore_errors=True)

# Red Team r9 Q5: a raw record that makes grade() RAISE must become a FAIL row naming the
# exception (T01's per-file meta replaced by a JSON list).
planted(
    "grade-raises",
    lambda d: (d / "T01_DecideFin.meta.json").write_text("[]"),
    ["T01_DecideFin.lean"],
    "FAIL",
    "grader error while grading this file",
)

# Red Team r9 finding 1 (T96 + MF95): a PASS-labelled file listing `records-tampered`, whose
# records a later file rewrote, must FAIL (never be exempt). Grader-level regression: the real
# run's tampered decoy records are replayed as tests/T96s (pass + records-tampered); the real-Lean
# demonstration is demos/T96_MF95/run_demo.sh.
sT = work / "suite-t96s"
shutil.copytree(suite, sT, ignore=shutil.ignore_patterns("results"))
_src = (suite / "must-fail/MF93a_SealDecoy/MF93a_SealDecoy.lean").read_text()
(sT / "tests" / "T96s_PassDecoyReplay.lean").write_text(
    _src.replace(
        "TOOLCHECK-EXPECT: records-tampered",
        "TOOLCHECK-EXPECT: pass\nTOOLCHECK-EXPECT: records-tampered",
    )
)
rT = work / "raw-t96s"
shutil.copytree(raw, rT)
for q in list(rT.glob("MF93a_SealDecoy.*")):
    shutil.copy(q, rT / q.name.replace("MF93a_SealDecoy", "T96s_PassDecoyReplay"))
_st = json.loads((rT / "seal.verify.json").read_text())
_st["tampered"] = sorted(set(_st["tampered"]) | {"T96s_PassDecoyReplay"})
(rT / "seal.verify.json").write_text(json.dumps(_st))
res = evaluate(sT / "toolcheck.py", rT, sT, "t96s")
fT = res["rows"]["T96s_PassDecoyReplay.lean"]
good = fT["result"] == "FAIL" and any(
    "allowed only for a must-fail decoy" in x for x in fT["failures"]
)
ok = ok and good
results.append(
    (
        "plant[T96s] pass-labelled file + records-tampered, records rewritten (must FAIL, never exempt)",
        row(res, "T96s_PassDecoyReplay.lean"),
        f"overall {res['overall']}",
    )
)
shutil.rmtree(sT, ignore_errors=True)
shutil.rmtree(rT, ignore_errors=True)

seal = json.loads((raw / "seal.verify.json").read_text())
r93 = seal.get("tampered") == ["MF93a_SealDecoy"]
ok = ok and r93
results.append(
    (
        "real-run[MF93] MF93b rewrote the decoy MF93a's records; the seal caught exactly that",
        f"tampered {seal.get('tampered')}; seals checked {seal.get('checked')}",
        "",
    )
)


# 7h. Red Team r6 concern 1(a): the run-level input manifest.
def _verify_fail(d):
    q = d / "inputs.verify.json"
    q.write_text(
        json.dumps(
            {
                "ok": False,
                "problems": ["suite input changed during the run: toolcheck.py"],
            }
        )
    )


for tag, mut in (
    ("inputs-verify-failed", _verify_fail),
    ("inputs-manifest-missing", lambda d: (d / "inputs.json").unlink()),
    ("inputs-verify-missing", lambda d: (d / "inputs.verify.json").unlink()),
):
    dI = work / f"raw-{tag}"
    shutil.copytree(raw, dI)
    mut(dI)
    res = evaluate(new_tc, dI, suite, tag)
    good = res["overall"] == "RED" and res["exit"] != 0
    ok = ok and good
    results.append(
        (
            f"plant[{tag}] run must be RED",
            f"overall {res['overall']} exit {res['exit']}; {res['pre'][:2]}",
            "",
        )
    )
    shutil.rmtree(dI, ignore_errors=True)


# Grade-time recheck ON. This tests the recheck LOGIC, not that the suite under test is the very
# commit the run used (run.sh's own in-memory verification does that; a mutant suite copy differs
# from the run by construction). So the run's manifest is re-synthesised from the suite under
# test (same rule as run.sh: no results/, __pycache__ or .md): unchanged suite -> GREEN; the
# allowlist edited afterwards (one appended newline: same JSON) -> RED.
def _suite_hashes_st(root):
    import hashlib

    out = {}
    for f in sorted(root.rglob("*")):
        rel = f.relative_to(root)
        if (
            not f.is_file()
            or rel.parts[0] == "results"
            or "__pycache__" in rel.parts
            or f.suffix == ".md"
        ):
            continue
        out[rel.as_posix()] = hashlib.sha256(f.read_bytes()).hexdigest()
    return out


rawM = work / "raw-recheck-manifest"
shutil.copytree(raw, rawM)
_man = json.loads((rawM / "inputs.json").read_text())
_man["suite"] = _suite_hashes_st(suite)
(rawM / "inputs.json").write_text(json.dumps(_man))
res = evaluate(new_tc, rawM, suite, "recheck-clean", recheck=True)
good = res["overall"] == "GREEN"
ok = ok and good
results.append(
    (
        "recheck[clean] grade-time re-hash of the unchanged suite (must be GREEN)",
        f"overall {res['overall']}",
        "",
    )
)
sQ = work / "suite-recheck-tampered"
shutil.copytree(suite, sQ, ignore=shutil.ignore_patterns("results"))
(sQ / "subset_kinds.json").write_text((sQ / "subset_kinds.json").read_text() + "\n")
res = evaluate(sQ / "toolcheck.py", rawM, sQ, "recheck-tampered", recheck=True)
good = res["overall"] == "RED" and any("subset_kinds.json" in x for x in res["pre"])
ok = ok and good
results.append(
    (
        "recheck[tampered] allowlist edited after the run (must be RED)",
        f"overall {res['overall']}; {res['pre'][:1]}",
        "",
    )
)
shutil.rmtree(sQ, ignore_errors=True)


# Rule P, each direction ALONE (so a mutant that drops one direction is killed): a Python-only
# start (the first command's head moved onto the second's line: Lean loses a start line, gains
# none) and a Lean-only start (an extra column-0 nested head on a comment line).
def _dup_head(recs):
    recs[1]["head_line"] = recs[2]["head_line"]
    return recs


def _extra_nested_head(recs):
    recs[1]["nested_heads"] = list(recs[1].get("nested_heads", [])) + [[2, 0]]
    return recs


for tag, mut in (
    ("parse-python-only-start", t01_parse(_dup_head)),
    ("parse-lean-only-start", t01_parse(_extra_nested_head)),
):
    planted(tag, mut, ["T01_DecideFin.lean"], "FAIL")


# Rule R ALONE: a guillemet / a raw-string opener inside T01's header COMMENT (same line count, so
# the real Lean-parser record still matches the file; the Lean layer is clean, rule R must fire).
for tag, r_old, r_new in (
    ("rule-R-guillemet-in-comment", "TOOLCHECK T01 —", "TOOLCHECK T01 «"),
    ("rule-R-raw-string-in-comment", "TOOLCHECK T01 —", 'TOOLCHECK T01 r"'),
):
    sR = work / f"suite-{tag}"
    shutil.copytree(suite, sR, ignore=shutil.ignore_patterns("results"))
    t01p = sR / "tests" / "T01_DecideFin.lean"
    t01text = t01p.read_bytes().decode("utf-8")
    assert t01text.count(r_old) == 1
    t01p.write_bytes(t01text.replace(r_old, r_new).encode("utf-8"))
    res = evaluate(sR / "toolcheck.py", raw, sR, tag)
    f = res["rows"]["T01_DecideFin.lean"]
    only_r = f["result"] == "FAIL" and not any(
        ("[L]" in x or "[P]" in x) for x in f["failures"]
    )
    ok = ok and only_r
    results.append(
        (
            f"plant[{tag}] T01 (must FAIL by rule R alone)",
            ("FAIL by R: " if only_r else "NOT R-only: ")
            + "; ".join(f["failures"])[:160],
            "",
        )
    )

# The subset_kinds.json pins: another toolchain, another T00 import list, another parser.
for tag, edit in (
    ("kinds-stale-toolchain", lambda k: k.update(toolchain="leanprover/lean4:v0.0.0")),
    ("kinds-stale-imports", lambda k: k.update(imports=k["imports"][:-1])),
    ("kinds-stale-parser", lambda k: k.update(parser_sha256="0" * 64)),
):
    sk = work / f"suite-{tag}"
    shutil.copytree(suite, sk, ignore=shutil.ignore_patterns("results"))
    kj = json.loads((sk / "subset_kinds.json").read_text())
    edit(kj)
    (sk / "subset_kinds.json").write_text(json.dumps(kj))
    res = evaluate(sk / "toolcheck.py", raw, sk, tag)
    ok = ok and res["rows"]["T01_DecideFin.lean"]["result"] == "FAIL"
    results.append(
        (
            f"plant[{tag}] subset_kinds.json pin (T01 must FAIL)",
            row(res, "T01_DecideFin.lean"),
            "",
        )
    )

# THE LEAN-PARSER LAYER ALONE (director decision, r5): a grader copy with every Python subset
# rule OFF (subset_violations returns []), so only rules L/P decide. Every must-fail is replayed
# as a pass-labelled attack. A must-fail that expects `subset-refused` MUST be caught by L/P;
# the rest are reported (their defect is not a subset matter: sorry, a false `decide`, …).
sL = work / "suite-lean-layer-only"
shutil.copytree(suite, sL, ignore=shutil.ignore_patterns("results"))
tcL = sL / "toolcheck.py"
tL = tcL.read_text()
assert tL.count(sig) == 1
tcL.write_text(
    tL.replace(sig, sig + "    return []  # SELFTEST: Python subset rules off\n")
)
lean_layer_rows = []
for mf in sorted((suite / "must-fail").glob("*/*.lean")):
    src_stem = mf.stem
    new_stem = "TL" + src_stem[2:4] + "_LeanLayerOnly"
    sLx, rLx = as_pass_attack(src_stem, mf.relative_to(suite).as_posix(), new_stem)
    shutil.copy(tcL, sLx / "toolcheck.py")
    res = evaluate(sLx / "toolcheck.py", rLx, sLx, new_stem)
    f = res["rows"][f"{new_stem}.lean"]
    lp = [x for x in f["failures"] if "[L]" in x or "[P]" in x]
    expects_subset = "subset-refused" in mf.read_text()
    good = bool(lp) or not expects_subset
    ok = ok and good
    tags = sorted(set(re.findall(r"\[(L|P)\] l\.\d+: ([^`(]*)", " ".join(lp))))
    lean_layer_rows.append((src_stem, "CAUGHT" if lp else "not caught", expects_subset))
    results.append(
        (
            f"lean-layer-only[{src_stem}] Python subset rules OFF"
            + (" (must be caught by L/P)" if expects_subset else " (reported)"),
            (
                ("CAUGHT by L/P: " + "; ".join(lp)[:160])
                if lp
                else ("not caught by L/P" + ("" if good else " — FAILURE"))
            ),
            f["result"],
        )
    )
    shutil.rmtree(sLx, ignore_errors=True)
    shutil.rmtree(rLx, ignore_errors=True)


# The command-heads pin: a heads list generated for another toolchain fails every pass file.
s10 = work / "suite-heads-stale"
shutil.copytree(suite, s10, ignore=shutil.ignore_patterns("results"))
hj = json.loads((s10 / "command_heads.json").read_text())
hj["toolchain"] = "leanprover/lean4:v0.0.0"
(s10 / "command_heads.json").write_text(json.dumps(hj))
res = evaluate(s10 / "toolcheck.py", raw, s10, "heads-stale")
ok = ok and res["rows"]["T01_DecideFin.lean"]["result"] == "FAIL"
results.append(
    (
        "plant[heads-stale] command_heads.json for another toolchain (T01 must FAIL)",
        row(res, "T01_DecideFin.lean"),
        "",
    )
)
s13 = work / "suite-heads-imports-stale"
shutil.copytree(suite, s13, ignore=shutil.ignore_patterns("results"))
hj = json.loads((s13 / "command_heads.json").read_text())
hj["imports"] = hj["imports"][:-1]  # same pins, one T00 import fewer
(s13 / "command_heads.json").write_text(json.dumps(hj))
res = evaluate(s13 / "toolcheck.py", raw, s13, "heads-imports-stale")
ok = ok and res["rows"]["T01_DecideFin.lean"]["result"] == "FAIL"
results.append(
    (
        "plant[heads-imports-stale] command_heads.json for another T00 import list (T01 must FAIL)",
        row(res, "T01_DecideFin.lean"),
        "",
    )
)


# The two structural-audit expectation kinds must FAIL when unmet: MF05's real `cheat` report
# removed from its auditor output (`audit-nonstd` unmet), and the clean T01 relabelled
# `audit-fails` (its audit is clean).
def mf05_clean_audit(d):
    p = d / "MF05_CustomAxiom.audit.out"
    lines = [l for l in p.read_text().split("\n") if l.strip()]
    i = next(k for k, l in enumerate(lines) if '"AXIOM-AUDIT-827"' in l)
    r = json.loads(lines[i])
    r["nonstd"] = []
    p.write_text(_emit(r, lines, i))


planted("audit-nonstd-unmet", mf05_clean_audit, ["MF05_CustomAxiom.lean"], "FAIL")
s11 = work / "suite-audit-fails-unmet"
shutil.copytree(suite, s11, ignore=shutil.ignore_patterns("results"))
t01 = s11 / "tests" / "T01_DecideFin.lean"
t01.write_bytes(
    t01.read_bytes().replace(
        b"TOOLCHECK-EXPECT: pass", b"TOOLCHECK-EXPECT: audit-fails"
    )
)
res = evaluate(new_tc, raw, s11, "audit-fails-unmet")
ok = ok and res["rows"]["T01_DecideFin.lean"]["result"] == "FAIL"
results.append(
    (
        "plant[audit-fails-unmet] clean T01 relabelled `audit-fails` (must FAIL)",
        row(res, "T01_DecideFin.lean"),
        "",
    )
)

# 7e. Rule isolation (Red Team r3 X1/X4): each source must give EXACTLY the expected rule tags,
#     so a mutant that weakens ONE rule is killed even where another rule also fires.
sys.path.insert(0, str(suite))
import toolcheck as _tc  # noqa: E402

RULE_CASES = [
    ("axiom foo : True", {"A", "D", "H"}),  # X1: column-0 `axiom`
    ("@[command_elab k] def x := 1", {"C"}),  # X4: handler attribute alone
    ("@[macro k] def x := 1", {"C", "D"}),
    ("@[simp] theorem t : True := trivial", set()),
    ("  simproc p (Nat.succ _) := fun _ => pure .continue", {"D", "H"}),  # T84 shape
    (
        "open Nat in simproc p (Nat.succ _) := fun _ => pure .continue",
        {"D", "H", "I"},
    ),  # T85
    ("open Nat in theorem t : True := trivial", set()),
    ("open Nat in qbp_user_cmd", {"I"}),
    ("set_option autoImplicit false in\n  theorem t : True := trivial", {"I"}),
    ("set_option autoImplicit false in\ntheorem t : True := trivial", set()),
    ("def q : Nat := 0 axiom cheat : False", {"D", "H"}),
    ("  example : True := trivial", {"H"}),
    ("  section", {"H"}),
    ("noncomputable instance : Inhabited Nat := ⟨0⟩", {"A"}),
    ("#check 1", {"A", "B", "H"}),
    ("theorem t : True := by\n  #print foo", {"B"}),
    ("open scoped Nat", set()),
    ("structure S where\n  x : Nat\n  deriving Repr", set()),
    ("  x scoped y", {"H"}),  # `scoped` excused only right after `open` (M48)
    (
        "  deriving instance Repr for Nat",
        {"H"},
    ),  # the `deriving instance` command (M49)
    ("  simproc_pattern% Nat.succ _ => go", {"H"}),  # T88: a non-word command head
    ("  x compile_def% y", {"H"}),
    ("  x $ y", {"H"}),
    ("  exact ?_", {"H"}),
    ("  x foo% y", {"H"}),  # any `name%` elaborator token
    ("theorem t : 7 % 2 = 1 := rfl", set()),  # the spaced `%` operator is fine
]
# Rule D in isolation: every refused keyword, mid-line, must give D, plus H exactly when Lean's
# own command-keyword list (read here from command_heads.json, which no grader mutant touches)
# has it. The keyword list is HARDCODED (the same list as SUBSET_PLANTS), never read from the
# grader, so dropping a word from SUBSET_DENY_WORDS is killed even where rule H also fires.
_heads = set(json.loads((suite / "command_heads.json").read_text())["word_heads"])
for _w in (
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
    "ofReduceBool",
    "reduceBool",
    "plausible",
    "slim_check",
    "axiom",
    "simproc",
    "dsimproc",
    "simproc_decl",
    "dsimproc_decl",
):
    RULE_CASES.append((f"  x {_w} y", {"D"} | ({"H"} if _w in _heads else set())))
RULE_CASES.append(("  decide +native", {"D"}))
rules_ok = True
for src_txt, want in RULE_CASES:
    got = {v[1] for v in _tc.subset_violations(src_txt + "\n") if v.startswith("[")}
    good = got == want
    rules_ok = rules_ok and good
    ok = ok and good
    if not good:
        results.append(
            (
                f"rule-isolation `{src_txt[:50]}`",
                f"FAIL: got {sorted(got)}, want {sorted(want)}",
                "",
            )
        )
results.append(
    (
        f"rule-isolation: {len(RULE_CASES)} one-construct sources, exact rule tags",
        "see failures above" if not rules_ok else "all exact",
        "",
    )
)


# 8. Gemini r3 (e): PIN Lean's `pos.column` unit on MF09's REAL output. The dirty report's
#    column must equal the codepoint offset of its `#print` in the original source line, and
#    (because the line has a multi-byte prefix) differ from the UTF-8 byte offset — so this
#    check distinguishes the two units and fails loudly if a toolchain ever switches.
mf09_src = (
    (suite / "must-fail/MF09_NonAsciiColumn/MF09_NonAsciiColumn.lean")
    .read_bytes()
    .decode("utf-8")
)
lines = mf09_src.split("\n")
mf09_ln = next(
    i
    for i, ln in enumerate(lines, start=1)
    if "#print axioms QBPToolcheck.MF09.dirty" in ln
)
idx = lines[mf09_ln - 1].index("#print axioms QBPToolcheck.MF09.dirty")
pre = lines[mf09_ln - 1][:idx]
cp, by, u16 = idx, len(pre.encode("utf-8")), len(pre.encode("utf-16-le")) // 2
got_col = None
for l in (raw / "MF09_NonAsciiColumn.log").read_bytes().decode("utf-8").split("\n"):
    if l.strip().startswith("{"):
        m = json.loads(l)
        if "'QBPToolcheck.MF09.dirty' depends on axioms" in m.get("data", ""):
            got_col = (m["pos"]["line"], m["pos"]["column"])
pin_ok = got_col == (mf09_ln, cp) and cp != by and cp != u16
ok = ok and pin_ok
results.append(
    (
        "pin[Lean column unit] MF09 real Lean output (must equal the CODEPOINT offset, not bytes or UTF-16)",
        f"{'PASS' if pin_ok else 'FAIL'}: Lean reported {got_col}; codepoint offset ({mf09_ln}, {cp}); UTF-8 byte offset ({mf09_ln}, {by}); UTF-16 offset ({mf09_ln}, {u16})",
        "",
    )
)


# 9. Gemini r4 (f): PIN Lean's LINE rule on MF10's and MF11's REAL output. Lean must report
#    `dirty` at the `\n`-only line of its `#print axioms` — and, because each file plants a
#    character that Python treats as a line break (form feed for `str.splitlines`, lone CR for
#    text-mode universal newlines), that line must DIFFER from the Python-rule line, so the
#    check distinguishes the two rules and fails loudly if a toolchain ever changes its rule.
def lean_line_pin(stem: str, thm: str, py_rule) -> tuple[bool, str]:
    src_b = next((suite / "must-fail").glob(f"{stem}/{stem}.lean")).read_bytes()
    needle = f"#print axioms {thm}"
    lean_ln = next(
        i
        for i, ln in enumerate(
            src_b.decode("utf-8").replace("\r\n", "\n").split("\n"), 1
        )
        if needle in ln
    )
    py_ln = next(i for i, ln in enumerate(py_rule(src_b), 1) if needle in ln)
    got = None
    for l in (raw / f"{stem}.log").read_bytes().decode("utf-8").split("\n"):
        if l.strip().startswith("{"):
            m = json.loads(l)
            if f"'{thm}' depends on axioms" in m.get("data", ""):
                got = m["pos"]["line"]
    good = got == lean_ln and lean_ln != py_ln
    return good, (
        f"{'PASS' if good else 'FAIL'}: Lean reported line {got}; `\\n`-only line {lean_ln}; "
        f"Python-rule line {py_ln}"
    )


for stem, thm, rule_name, rule in (
    (
        "MF10_FormFeedLineDesync",
        "QBPToolcheck.MF10.dirty",
        "str.splitlines (breaks at \\f)",
        lambda b: b.decode("utf-8").splitlines(),
    ),
    (
        "MF11_LoneCRLineDesync",
        "QBPToolcheck.MF11.dirty",
        "text-mode read (universal newlines: lone \\r -> \\n)",
        lambda b: b.decode("utf-8")
        .replace("\r\n", "\n")
        .replace("\r", "\n")
        .split("\n"),
    ),
):
    good, msg = lean_line_pin(stem, thm, rule)
    ok = ok and good
    results.append(
        (f"pin[Lean line rule] {stem} real Lean output vs {rule_name}", msg, "")
    )

for a, b, c in results:
    print(f"| {a} | {b} | {c} |")
for x in NO_OUTPUT:
    print(f"| grader NO OUTPUT (counted as a failed assertion) | {x} |  |")
print("selftest:", "OK — every plant behaved as required" if ok else "FAILED")
sys.exit(0 if ok else 1)
