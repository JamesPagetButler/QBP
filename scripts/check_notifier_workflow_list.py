#!/usr/bin/env python3
"""workflow_run enumeration-drift lint for the PR check-status notifier (#507 §3).

The notifier (`.github/workflows/pr-check-status.yml`) re-evaluates a PR's verdict
on `workflow_run: completed` events, but GitHub only delivers those for workflows
listed by NAME under `on.workflow_run.workflows`.  A PR-triggered workflow that is
missing from that list can finish last and its completion is never seen, so the
verdict is never finalised (the "missed final event" class).

Rule: every workflow with a `pull_request` (or `pull_request_target`) trigger must
be listed; the notifier itself is exempt; workflows without a PR trigger (push-only,
schedule, workflow_dispatch) are ignored — they never run on a PR head.  A listed
name that matches no workflow is also an error (a renamed workflow silently drops
out of the list).

Usage: check_notifier_workflow_list.py [--workflows-dir .github/workflows]
                                       [--notifier pr-check-status.yml]
Exit 0 when in sync, 1 on drift, 2 on a usage/parse error.
"""

from __future__ import annotations

import argparse
import glob
import os
import sys

import yaml

PR_TRIGGERS = ("pull_request", "pull_request_target")


def _on_block(doc):
    """PyYAML parses the bare key `on` as boolean True; accept both spellings."""
    if not isinstance(doc, dict):
        return None
    if "on" in doc:
        return doc["on"]
    if True in doc:
        return doc[True]
    return None


def _triggers(on):
    """Normalise the `on:` block to a set of trigger names."""
    if on is None:
        return set()
    if isinstance(on, str):
        return {on}
    if isinstance(on, list):
        return {str(t) for t in on}
    if isinstance(on, dict):
        return {str(k) for k in on.keys()}
    return set()


def load_workflows(workflows_dir):
    """Return {path: (name, triggers)} for every *.yml/*.yaml under workflows_dir."""
    out = {}
    paths = sorted(
        glob.glob(os.path.join(workflows_dir, "*.yml"))
        + glob.glob(os.path.join(workflows_dir, "*.yaml"))
    )
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            try:
                doc = yaml.safe_load(fh)
            except yaml.YAMLError as e:  # pragma: no cover - surfaced as exit 2
                raise SystemExit(f"::error file={p}::YAML parse error: {e}")
        if not isinstance(doc, dict):
            continue
        name = doc.get("name")
        if not name:
            # GitHub falls back to the file path as the display name; the notifier
            # cannot reliably list that, so a PR-triggered nameless workflow is drift.
            name = os.path.relpath(p)
        out[p] = (str(name), _triggers(_on_block(doc)))
    return out


def notifier_list(notifier_path):
    with open(notifier_path, encoding="utf-8") as fh:
        doc = yaml.safe_load(fh)
    on = _on_block(doc)
    if not isinstance(on, dict) or "workflow_run" not in on:
        raise SystemExit(
            f"::error file={notifier_path}::no `on.workflow_run` block in the notifier"
        )
    wr = on["workflow_run"] or {}
    listed = wr.get("workflows") or []
    if not isinstance(listed, list):
        raise SystemExit(
            f"::error file={notifier_path}::`workflow_run.workflows` must be a list"
        )
    name = doc.get("name") if isinstance(doc, dict) else None
    return str(name), [str(x) for x in listed]


def compute_drift(workflows, notifier_name, listed):
    """Return (missing, stale): PR-triggered names not listed; listed names that exist nowhere."""
    pr_names = {
        name
        for _, (name, trig) in workflows.items()
        if trig & set(PR_TRIGGERS) and name != notifier_name
    }
    all_names = {name for _, (name, _) in workflows.items()}
    listed_set = set(listed)
    missing = sorted(pr_names - listed_set)
    stale = sorted(listed_set - all_names)
    return missing, stale


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--workflows-dir", default=".github/workflows")
    ap.add_argument("--notifier", default="pr-check-status.yml")
    args = ap.parse_args(argv)

    notifier_path = os.path.join(args.workflows_dir, args.notifier)
    if not os.path.isfile(notifier_path):
        print(f"::error::notifier workflow not found: {notifier_path}")
        return 2
    workflows = load_workflows(args.workflows_dir)
    if not workflows:
        print(f"::error::no workflow files found under {args.workflows_dir}")
        return 2
    notifier_name, listed = notifier_list(notifier_path)
    missing, stale = compute_drift(workflows, notifier_name, listed)

    rel = os.path.relpath(notifier_path)
    for name in missing:
        print(
            f"::error file={rel}::PR-triggered workflow '{name}' is not in "
            f"`on.workflow_run.workflows` — its completion cannot finalise a verdict"
        )
    for name in stale:
        print(
            f"::error file={rel}::listed workflow '{name}' matches no workflow name "
            f"under {args.workflows_dir} (renamed or deleted?)"
        )
    n_pr = sum(
        1
        for _, (name, trig) in workflows.items()
        if trig & set(PR_TRIGGERS) and name != notifier_name
    )
    if missing or stale:
        print(
            f"notifier workflow list DRIFTED: {len(missing)} missing, {len(stale)} stale "
            f"(of {n_pr} PR-triggered workflows, {len(listed)} listed)."
        )
        return 1
    print(
        f"notifier workflow list in sync: {n_pr} PR-triggered workflows, "
        f"{len(listed)} listed, {len(workflows)} workflow files scanned."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
