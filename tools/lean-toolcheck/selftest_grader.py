"""Grader self-test: planted negative controls (PR #824 Red Team + Gemini rounds).

Takes the raw results of a real GREEN run, plants one defect per COPY, and runs the grader
on each copy; every plant must be caught (or, for spoofs, neutralised). Optionally also runs
an OLD grader (e.g. the toolcheck.py of commit de19998) to show the defect it missed.

usage: selftest_grader.py SUITE RAW_DIR WORK_DIR [OLD_TOOLCHECK]
  RAW_DIR = results/runs/<run-id>/raw of a full GREEN run; WORK_DIR is wiped and reused.
Exit 0 iff the unplanted run is GREEN and every plant behaved as required.
"""

import json
import shutil
import subprocess
import sys
from pathlib import Path

suite, raw, work = map(Path, sys.argv[1:4])
old_tc = Path(sys.argv[4]) if len(sys.argv) > 4 else None
new_tc = suite / "toolcheck.py"
if work.exists():
    shutil.rmtree(work)
work.mkdir(parents=True)


def evaluate(tc: Path, rawdir: Path, suitedir: Path, tag: str) -> dict:
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
        ],
        capture_output=True,
        text=True,
    )
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

ok = base["overall"] == "GREEN"
# 1. optionally demonstrate the bugs with an OLD grader on the same raw logs
old = evaluate(old_tc, raw, suite, "old") if old_tc is not None else None
for n in ("MF06_SpoofedAudit.lean", "T19_NestedComments.lean"):
    if old is not None:
        results.append((f"OLD grader on {n}", row(old, n), ""))
    results.append((f"NEW grader on {n}", row(base, n), ""))
    ok = ok and base["rows"][n]["result"] == "PASS"


def planted(tag, mutate, names, must):
    """must = 'FAIL' (the plant must be flagged) or 'PASS' (the spoof must be neutralised)."""
    global ok
    d = work / f"raw-{tag}"
    shutil.copytree(raw, d)
    mutate(d)
    res = evaluate(new_tc, d, suite, tag)
    for n in names:
        ok = ok and res["rows"][n]["result"] == must
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
    for ext in (".log", ".meta.json", ".checker.log", ".stderr"):
        p = r3 / f"{src_stem}{ext}"
        if p.exists():
            shutil.copy(p, r3 / f"{new_stem}{ext}")
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


MF05 = ("MF05_CustomAxiom", "must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean")
for tag, mut, what in (
    # M10: the real report is absent; a forged clean `information` report sits OFF the site.
    ("T96_ForgedOffSite", drop_real_and_forge("information", False), "position"),
    # M11: the real report is absent; a forged clean report sits AT the site as a `warning`.
    ("T96b_ForgedWarningAtSite", drop_real_and_forge("warning", True), "severity"),
):
    s3, r3 = as_pass_attack(*MF05, tag)
    mut(r3 / f"{tag}.log")
    res = evaluate(new_tc, r3, s3, tag)
    ok = ok and res["rows"][f"{tag}.lean"]["result"] == "FAIL"
    results.append(
        (f"plant[{tag}] spoof guard: {what} (must FAIL)", row(res, f"{tag}.lean"), "")
    )


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
print("selftest:", "OK — every plant behaved as required" if ok else "FAILED")
sys.exit(0 if ok else 1)
