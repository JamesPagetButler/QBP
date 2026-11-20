#!/usr/bin/env python3
"""Triage an Agda release-notes file into the three #823 R5 buckets.

Every changelog item between the pinned and the candidate version must land in
exactly one bucket:

  relevant  -> a test is needed (or names the existing test that covers it)
  breaking  -> does it touch our usage? (names the usage to check / migration)
  not       -> one-line reason why it cannot affect QBP's Agda files

The release notes are DOWNLOADED, UNTRUSTED text: this script only reads them
(run it with `python3 -I`), it never executes anything from them.

Usage:
  python3 -I triage_changelog.py --notes agda-2.9.0.md [--notes ...] \
      --overrides triage_overrides.json --label "Agda 2.8.0 -> 2.9.0" > table.md

Items are matched first against the overrides (a JSON list of
{"match": <regex on the item key or title>, "bucket": ..., "reason": ...};
first match wins), then against the built-in keyword rules, then default to
"relevant / unclassified -> needs a human look" so nothing is silently dropped.
"""

import argparse
import json
import re
import sys

BUCKETS = {
    "relevant": "relevant → test needed",
    "breaking": "breaking → touches our usage?",
    "not": "not relevant",
}

# Built-in rules: (regex on the title, bucket, reason). Order matters.
RULES = [
    # soundness / --safe / cubical core -> always relevant
    (
        r"safe|postulate|consisten|Proof of global choice|False because|canonicity",
        "relevant",
        "soundness of --safe / the cubical core: re-run project layer; mustfail/ pins the gate",
    ),
    (
        r"cubical|Cubical|Glue|HCompU|HIT|transp|hcomp|IsOne|interval|path abstraction|boundary",
        "relevant",
        "cubical core behaviour: covered by tool/ (Interval, PathP, Transp, HComp, GlueUa, *HIT) + project re-run",
    ),
    (
        r"terminat|positivity|Positivity|guarded|Guarded|copattern|Copattern|coinductiv|productiv",
        "relevant",
        "termination/positivity/guardedness checker: tool/Guardedness + mustfail/Terminating + project re-run",
    ),
    (
        r"opaque|abstract block",
        "relevant",
        "opaque/abstract blocks: tool/Opaque pins the behaviour",
    ),
    (
        r"perf|Perf|optimi|Optimi|faster|slow|cach|Cach|serialis|serializ|parallel|Parallel|checkpoint|free variable|Free variable|Lines/second|benchmark",
        "relevant",
        "performance: R6 baseline comparison (per-file wall/RSS in results/*.json); a big slowdown is a finding",
    ),
    (
        r"interface file|Interface|\.agda-lib|library|Library|defaults",
        "relevant",
        "library/interface management: run.sh reads the pins; re-run the suite after any change",
    ),
    (
        r"unused import|UnusedImports|redundant imports",
        "relevant",
        "new warning only; QBP uses explicit `using` lists, so expect warnings, not errors (no -Werror); count them in the baseline",
    ),
    (
        r"fixity|Fixity|operator parsing|Operator parse|operator",
        "breaking",
        "operator parsing: the pinned agda/cubical renames primIMin/primIMax without fixity → needs cubical ≥ c2d05f7 together with Agda 2.9.0",
    ),
    (
        r"[Ee]rror|[Ww]arning|message|highlight|Highlight|wording|ClashingDefinition|colour|color|Color",
        "relevant",
        "diagnostics text only: mustfail EXPECT substrings may need re-pinning (run.sh reports WRONG-ERROR)",
    ),
    # not relevant families
    (
        r"Emacs|emacs|Mimer|C-c|C-u|M-\.|Xref|interaction|Interaction|JSON|goal|Goal|hole|Cmd_|[Cc]ase split|[Ss]plit|Give|[Rr]efine|helper function|agda2-|info buffer|information buffer|Catch-all copattern clauses are now tolerated",
        "not",
        "interactive / Emacs-mode only; QBP checks in batch mode",
    ),
    (
        r"JS backend|GHC backend|[Bb]ackend|COMPILE|FOREIGN|compil|LaTeX|HTML|html|Forester|forester|[Ll]iterate|Markdown|Typst|Scott|treeless|ghc-trace",
        "not",
        "backend / literate output; QBP never compiles or renders Agda",
    ),
    (
        r"GHC|[Nn]ix|cabal|stack|Windows|aarch64|darwin|workflow|Makefile|version-with-git-hash|zlib|install_agda|ecosystem|submodule|actions/",
        "not",
        "build / installation; QBP uses the official prebuilt bindist",
    ),
    (
        r"[Rr]ewrit|REWRITE|[Cc]onfluence|rewrite rule",
        "not",
        "rewriting; forbidden by QBP's --safe discipline and never enabled",
    ),
    (
        r"[Rr]eflection|tactic|Tactic|macro|quote|unquote|tcTypeError|Mimer|synthesis|Synthesis",
        "not",
        "reflection / tactics / proof search; QBP uses none",
    ),
    (
        r"erasure|erased|Erased|@0|@ω|irrelevan|Irrelevan|Prop\b|polarit|Polarit|cohesion|flat|sharp|Sharp|modalit|Modalit|resourced",
        "not",
        "modalities / erasure / Prop / polarity / cohesion; none of these flags is on in QBP",
    ),
    (
        r"[Ss]ized|Size",
        "not",
        "sized types; off (QBP uses --guardedness, which excludes --sized-types under --safe)",
    ),
    (
        r"[Ii]nstance|⦃",
        "not",
        "instance search; QBP declares no instances and no instance arguments",
    ),
    (r"record where|Record where", "not", "`record where` sugar; not used in QBP"),
    (
        r"\bwith\b|With-abstraction|with-abstraction|inspect",
        "not",
        "with-abstraction; no QBP Agda file uses `with`",
    ),
    (
        r"Float|float|Char|String|Word64|literal|Literal|FromNat|Num\b",
        "not",
        "builtin literals / primitives QBP does not use",
    ),
    (r"mutual|Mutual|interleaved", "not", "mutual blocks; QBP uses none"),
    (
        r"\bdo\b|idiom|Idiom|qualified",
        "not",
        "do-notation / idiom brackets; QBP uses none",
    ),
    (
        r"[Pp]rojection|postfix|Postfix",
        "not",
        "postfix-projection syntax; QBP writes projections as `.fst`/`fst x` only (no parenthesised postfix forms)",
    ),
    (
        r"generali[sz]|Generali[sz]",
        "relevant",
        "generalisable `variable` blocks are used throughout QBP: tool/CoreSyntax + project re-run",
    ),
    (
        r"module|Module|scope|Scope|import|Import|open|renaming",
        "relevant",
        "module system / scoping: tool/CoreSyntax (anonymous modules, renaming) + project re-run",
    ),
    (
        r"eta|Eta|ETA",
        "relevant",
        "eta rules for records: HSpace/CDLaws are records without `no-eta-equality`; project re-run shows any UnguardedEtaRecord",
    ),
    (
        r"[Pp]arse|[Ss]yntax|comment|delimiter|underscore",
        "relevant",
        "surface syntax: tool/CoreSyntax + project re-run (all files re-parsed)",
    ),
    (
        r"documentation|Documentation|doc:|Doc |docs|\bdoc\b|README|cite|Cite",
        "not",
        "documentation only",
    ),
    (
        r"unifier|Unifier|unification|metaOccurs|meta|Meta|solve|Solve|constraint",
        "relevant",
        "unifier / meta solving: SkyrmionCharge depends on --lossy-unification behaviour; tool/LossyUnification + project re-run",
    ),
    (
        r"coverage|Coverage|clause|Clause|pattern|Pattern|match",
        "relevant",
        "pattern matching / coverage / clause compilation: every HIT recursor in QBP; tool/*HIT + project re-run",
    ),
    (
        r"level|Level|universe|Universe|sort|Sort",
        "relevant",
        "universe levels: QBP files are level-polymorphic (ℓ, ℓ', ℓ-max); project re-run",
    ),
    (
        r"record|Record|field|Field|constructor",
        "relevant",
        "records and constructors (HSpace, CDLaws, Iso): project re-run",
    ),
]


UNCLASSIFIED = "UNCLASSIFIED — needs a human look before the upgrade PR"


def classify(title, overrides, issue_titles=None):
    """Overrides first, then keyword rules, then (for a PR that only says
    'Fix #N') the title of issue N from the same notes, then UNCLASSIFIED."""
    for ov in overrides:
        if re.search(ov["match"], title):
            return ov["bucket"], ov["reason"]
    for pat, bucket, reason in RULES:
        if re.search(pat, title):
            return bucket, reason
    if issue_titles:
        for num in re.findall(r"#(\d+)", title):
            if num in issue_titles:
                bucket, reason = classify(issue_titles[num], overrides)
                return bucket, f"(via Issue #{num}: {issue_titles[num][:60]}) {reason}"
    return "relevant", UNCLASSIFIED


ITEM_RE = re.compile(r"^- \[(Issue|PR) #(\d+)\]\([^)]*\): (.*)$")
SECTION_RE = re.compile(r"^(.+)\n(=+|-+)$", re.M)


def parse(text):
    """Yield (section, key, title) for every changelog item."""
    section = "(preamble)"
    lines = text.split("\n")
    bullet = None
    for i, line in enumerate(lines):
        nxt = lines[i + 1] if i + 1 < len(lines) else ""
        if nxt and re.fullmatch(r"[=-]{3,}", nxt) and line.strip():
            if bullet:
                yield bullet
                bullet = None
            section = line.strip()
            continue
        if line.startswith("### "):
            if bullet:
                yield bullet
                bullet = None
            section = line[4:].strip()
            continue
        m = ITEM_RE.match(line)
        if m:
            if bullet:
                yield bullet
                bullet = None
            yield (section, f"{m.group(1)} #{m.group(2)}", m.group(3).strip())
            continue
        if line.startswith("* "):
            if bullet:
                yield bullet
            bullet = (section, "note", line[2:].strip())
            continue
        if (
            bullet
            and line.startswith("  ")
            and len(bullet[2]) < 160
            and not line.strip().startswith("```")
        ):
            bullet = (bullet[0], bullet[1], (bullet[2] + " " + line.strip())[:220])
    if bullet:
        yield bullet


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--notes",
        action="append",
        required=True,
        help="release-notes markdown (repeatable)",
    )
    ap.add_argument("--overrides", help="JSON list of {match, bucket, reason}")
    ap.add_argument(
        "--label", default="", help="heading label, e.g. 'Agda 2.8.0 → 2.9.0'"
    )
    args = ap.parse_args()

    overrides = []
    if args.overrides:
        with open(args.overrides, encoding="utf-8") as fh:
            overrides = json.load(fh)
        for ov in overrides:
            if ov["bucket"] not in BUCKETS:
                sys.exit(f"bad bucket in override: {ov}")

    items = []
    for path in args.notes:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        for section, key, title in parse(text):
            items.append((path.rsplit("/", 1)[-1], section, key, title))
    issue_titles = {
        k.split("#")[1]: t for _, _, k, t in items if k.startswith("Issue #")
    }

    rows = []
    for f, section, key, title in items:
        bucket, reason = classify(title, overrides, issue_titles)
        rows.append((f, section, key, title, bucket, reason))

    counts = {b: 0 for b in BUCKETS}
    for r in rows:
        counts[r[4]] += 1
    out = []
    out.append(f"### Candidate triage{(': ' + args.label) if args.label else ''}")
    out.append("")
    out.append(
        f"{len(rows)} items · "
        + " · ".join(f"{BUCKETS[b]}: **{counts[b]}**" for b in BUCKETS)
    )
    out.append("")
    out.append(
        "| file | section | item | title | bucket | test / usage to check / reason |"
    )
    out.append("|---|---|---|---|---|---|")
    for f, sec, key, title, bucket, reason in rows:
        t = title.replace("|", "\\|")
        if len(t) > 110:
            t = t[:107] + "…"
        out.append(f"| {f} | {sec} | {key} | {t} | {BUCKETS[bucket]} | {reason} |")
    print("\n".join(out))


if __name__ == "__main__":
    main()
