#!/usr/bin/env python3
"""Job display-name uniqueness lint across `.github/workflows` (#757 AC2).

Every human-facing check surface identifies a check by (display name, app):
`gh pr checks` dedupes by name, the merge box groups by (name, app),
branch-protection required checks match by name, and the PR check-status
notifier reduces check-runs to the newest per name (#721 AC1).  Two jobs in two
workflows that render to the same display name therefore collapse into ONE
check: an earlier failure is hidden behind a later success of the other job
(live hazard found on PR #756's review — `validate` x2, `typecheck` x2).

Rule: a job's display name is its `name:` if set, else its job id.  Every
display name must be defined by exactly one job repo-wide — across workflows
AND inside one workflow (two job ids with the same `name:` collide just the
same; YAML keys already prevent two identical ids in one file).

Matrix jobs: GitHub renders a `strategy.matrix` job as `name (matrix values)`,
so two matrix jobs with the same base name still share a prefix and sort/dedupe
confusingly; this lint compares the BASE name only (the `name:` text or the job
id, `${{ }}` expressions left as their literal template) and treats two equal
base names as a collision.

Usage: check_job_display_names.py [--workflows-dir .github/workflows]
Exit 0 when every display name is unique, 1 on a collision, 2 on a usage/parse
error.
"""

from __future__ import annotations

import argparse
import glob
import os
import sys
from collections import defaultdict

import yaml


class WorkflowParseError(Exception):
    """A workflow file is not valid YAML or has no usable `jobs:` mapping."""


def _on_block(doc):
    """PyYAML parses the bare key `on` as boolean True; accept both spellings."""
    if not isinstance(doc, dict):
        return None
    if "on" in doc:
        return doc["on"]
    if True in doc:
        return doc[True]
    return None


def display_name(job_id, job):
    """Display name = `name:` if set (non-empty), else the job id.

    A `strategy.matrix` job renders as `<name> (<matrix values>)` on GitHub; the
    base name is what this lint compares (see module docstring).
    """
    if isinstance(job, dict):
        name = job.get("name")
        if name is not None and str(name).strip():
            return str(name)
    return str(job_id)


def load_jobs(workflows_dir):
    """Return [(path, workflow_name, job_id, display_name)] for every job.

    Raises WorkflowParseError on a YAML parse error or a `jobs:` that is not a
    mapping.  Files whose top level is not a mapping (empty files) are skipped.
    """
    out = []
    paths = sorted(
        glob.glob(os.path.join(workflows_dir, "*.yml"))
        + glob.glob(os.path.join(workflows_dir, "*.yaml"))
    )
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            try:
                doc = yaml.safe_load(fh)
            except yaml.YAMLError as e:
                raise WorkflowParseError(f"{p}: YAML parse error: {e}") from e
        if not isinstance(doc, dict):
            continue
        # Touch the on-block so a bare `on:` (parsed as True) is accepted, not
        # mistaken for a malformed file.
        _on_block(doc)
        wf_name = doc.get("name") or os.path.relpath(p)
        jobs = doc.get("jobs")
        if jobs is None:
            continue
        if not isinstance(jobs, dict):
            raise WorkflowParseError(f"{p}: `jobs:` is not a mapping")
        for job_id, job in jobs.items():
            out.append((p, str(wf_name), str(job_id), display_name(job_id, job)))
    return out


def find_collisions(jobs):
    """Return {display_name: [(path, workflow_name, job_id), ...]} with >1 definer."""
    by_name = defaultdict(list)
    for path, wf_name, job_id, dname in jobs:
        by_name[dname].append((path, wf_name, job_id))
    return {n: defs for n, defs in sorted(by_name.items()) if len(defs) > 1}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--workflows-dir", default=".github/workflows")
    args = ap.parse_args(argv)

    if not os.path.isdir(args.workflows_dir):
        print(f"::error::workflows directory not found: {args.workflows_dir}")
        return 2
    try:
        jobs = load_jobs(args.workflows_dir)
    except WorkflowParseError as e:
        print(f"::error::{e}")
        return 2
    if not jobs:
        print(f"::error::no workflow jobs found under {args.workflows_dir}")
        return 2

    collisions = find_collisions(jobs)
    n_files = len({p for p, _, _, _ in jobs})
    if collisions:
        for dname, defs in collisions.items():
            where = "; ".join(
                f"{os.path.relpath(p)} ({wf}) job `{jid}`" for p, wf, jid in defs
            )
            print(
                f"::error::job display name '{dname}' is defined {len(defs)} times "
                f"— {where}. Set a unique `name:` on each (checks are identified by "
                f"display name: gh pr checks / merge box / notifier collapse them)"
            )
        print(
            f"job display names COLLIDE: {len(collisions)} name(s) defined more than "
            f"once (of {len(jobs)} jobs in {n_files} workflow files)."
        )
        return 1
    print(
        f"job display names unique: {len(jobs)} jobs in {n_files} workflow files, "
        f"no display name defined twice."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
