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

for a, b, c in results:
    print(f"| {a} | {b} | {c} |")
print("selftest:", "OK — every plant behaved as required" if ok else "FAILED")
sys.exit(0 if ok else 1)
