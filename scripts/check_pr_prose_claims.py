#!/usr/bin/env python3
"""Advisory evidence-first lints on PR prose (#507 §1 + §2; review_tiers.md evidence-first 6–7).

Two crude, mechanical heuristics.  The REVIEWER remains the authority (rule 6);
these only make the two most common slips visible as GitHub annotations.

§1  Truth-in-labelling (title lint).  On a theory-bearing PR (label `tier-3-review`,
    or any changed path under `proofs/`, `docs/theory/`, `docs/foundations/`), a
    VERDICT WORD in the title ("proves", "establishes", "confirms", "verifies",
    "demonstrates", "shows", "falsifies", "refutes", "rules out") is flagged unless
    the body carries a verdict headline: a line starting with `**Verdict` /
    `Verdict:` / `## Verdict`, or a three-way evidence table header.  A title that
    states a verdict must point at the verdict's evidence, not just assert it.

§2  Oracle-fixture premise audit.  Any body line that cites an "oracle" run as
    evidence (contains "oracle" and either a URL or the words "run"/"report"/
    "output"/"evidence") must ALSO name an in-repo fixture/config path
    (`tests/fixtures/…`, `tests/…json`, `analysis/…`, `config/…`, `*.json`,
    `*.yaml`, `*.toml`) and a pinned commit sha (7–40 hex) on the same line or the
    next two lines.  Out-of-band JSON is not a premise.  Pairs with the
    differential guard (#504).

Mode: ADVISORY by default (`::warning::` annotations, exit 0).  `--strict` turns
every finding into `::error::` and exit 1 — the beekeeper's flip (#507 AC
"advisory-or-blocking per beekeeper choice").

Inputs (so the script is unit-testable without GitHub):
  --title STR  --body-file F  --labels "a,b"  --changed-file F (one path per line)
Exit: 0 (advisory, or strict with no findings); 1 (strict with findings); 2 (usage).
"""

from __future__ import annotations

import argparse
import re
import sys

VERDICT_WORDS = re.compile(
    r"\b(prove[sd]?|establish(?:es|ed)?|confirm(?:s|ed)?|verif(?:y|ies|ied)|"
    r"demonstrate[sd]?|shows\s+that|falsif(?:y|ies|ied)|refute[sd]?|rules?\s+out)\b",
    re.I,
)
VERDICT_HEADLINE = re.compile(
    r"^[\s>*+-]*(\*\*verdict\b|verdict\s*:|#{1,6}\s*verdict\b|\|\s*(claim|experimental evidence)\b)",
    re.I | re.M,
)
THEORY_PATHS = ("proofs/", "docs/theory/", "docs/foundations/")
THEORY_LABEL = "tier-3-review"

ORACLE_LINE = re.compile(r"\boracle\b", re.I)
ORACLE_EVIDENCE = re.compile(
    r"https?://|\b(run|report|output|evidence|results?)\b", re.I
)
# An in-repo premise is a ROOT-RELATIVE repo path (G9): URLs (anything with "://")
# and bare "*.json" tokens do not count — "out-of-band JSON is not a premise".
FIXTURE_PATH = re.compile(
    r"(?<![\w/:.])(tests?|analysis|config|fixtures?|docs|proofs|archive|scripts|verification|results)/[\w./-]+"
)
# A pinned sha is 7–40 hex chars that are not a pure decimal (Actions run ids, dates
# — Red Team G10). An all-letter prefix IS a valid sha prefix (Gemini BLOCKING on
# PR #731), so it is accepted; the residual false positive — a 7+ letter English word
# over {a–f} such as "defaced" — is the lesser error and is pinned by a test.
PINNED_SHA = re.compile(r"\b(?=[0-9a-f]{7,40}\b)(?![0-9]+\b)[0-9a-f]{7,40}\b")
STRUCK = re.compile(r"~~[^~]*~~")
NIL_MARK = "⊘"


def is_theory_bearing(labels, changed):
    if THEORY_LABEL in labels:
        return True
    return any(p.startswith(THEORY_PATHS) for p in changed)


def lint_title(title, body, labels, changed):
    """§1: return a list of finding strings (empty when clean)."""
    if not is_theory_bearing(labels, changed):
        return []
    m = VERDICT_WORDS.search(title or "")
    if not m:
        return []
    if VERDICT_HEADLINE.search(body or ""):
        return []
    return [
        f"title uses the verdict word '{m.group(0)}' on a theory-bearing PR but the body has no "
        f"verdict headline (`**Verdict:**`, `## Verdict`, or the three-way evidence table). "
        f"State what is established, or add the headline the title points at "
        f"(review_tiers.md evidence-first rule 6)."
    ]


def lint_oracle(body):
    """§2: return a list of finding strings for oracle citations without an in-repo pinned premise."""
    findings = []
    lines = (body or "").splitlines()
    for i, raw in enumerate(lines):
        if NIL_MARK in raw:
            continue  # a ⊘ line is a nil'd option, not a citation
        # struck FRAGMENTS are removed, the rest of the line is still checked (Gemini S-F)
        line = STRUCK.sub(" ", raw)
        if not (ORACLE_LINE.search(line) and ORACLE_EVIDENCE.search(line)):
            continue
        window = "\n".join(lines[i : i + 3])
        window_no_urls = re.sub(r"\S+://\S+", " ", window)
        has_path = bool(FIXTURE_PATH.search(window_no_urls))
        has_sha = bool(PINNED_SHA.search(window))
        if has_path and has_sha:
            continue
        missing = []
        if not has_path:
            missing.append("an in-repo fixture/config path")
        if not has_sha:
            missing.append("a pinned commit sha")
        findings.append(
            f"body line {i + 1} cites an oracle run as evidence without {' and '.join(missing)}: "
            f"`{line.strip()[:120]}` — an oracle premise must be a committed fixture at a pinned "
            f"sha, not out-of-band output (review_tiers.md evidence-first rule 7; #504)."
        )
    return findings


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--title", default="")
    ap.add_argument("--body-file")
    ap.add_argument("--labels", default="", help="comma-separated label names")
    ap.add_argument("--changed-file", help="file with one changed path per line")
    ap.add_argument(
        "--strict", action="store_true", help="findings become errors + exit 1"
    )
    args = ap.parse_args(argv)

    body = ""
    if args.body_file:
        with open(args.body_file, encoding="utf-8") as fh:
            body = fh.read()
    labels = {x.strip() for x in args.labels.split(",") if x.strip()}
    changed = []
    if args.changed_file:
        with open(args.changed_file, encoding="utf-8") as fh:
            changed = [ln.strip() for ln in fh if ln.strip()]

    findings = [
        ("title-lint", f) for f in lint_title(args.title, body, labels, changed)
    ]
    findings += [("oracle-premise", f) for f in lint_oracle(body)]

    level = "error" if args.strict else "warning"
    for kind, f in findings:
        print(f"::{level} title=evidence-first {kind}::{f}")
    mode = "STRICT" if args.strict else "ADVISORY"
    print(
        f"evidence-first prose lint ({mode}): {len(findings)} finding(s); "
        f"theory-bearing={is_theory_bearing(labels, changed)}; body lines={len(body.splitlines())}"
    )
    if findings and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
