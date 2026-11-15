#!/usr/bin/env python3
"""Guard (#507 §6/§7): every merge-blocking / review-completeness check is listed in the
notifier's REVIEW_GATES, so it is excluded from TECH-GREEN and included in ALL-GREEN.

Live failure this guards against (PR #785, 2026-10-29): `Merge-blocking boxes` landed
(PR #780) in the notifier's workflow_run list but not in REVIEW_GATES, so an open HVR
box made the notifier post "Checks FAILED — review-ready revoked" and the CI-green
evidence box could never tick. Runs under pytest or as a plain script.
"""

from __future__ import annotations

import json
import os
import re
import sys

import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NOTIFIER = os.path.join(ROOT, ".github", "workflows", "pr-check-status.yml")
MERGE_BLOCKING_WF = os.path.join(
    ROOT, ".github", "workflows", "merge-blocking-boxes.yml"
)
TIER3_GATE_NAME = "Tier-3 review-label required on theory-bearing diffs"


def review_gates(notifier_text: str) -> list[str]:
    m = re.search(r"^\s*REVIEW_GATES='(\[.*?\])'\s*$", notifier_text, re.M)
    assert m, "REVIEW_GATES assignment not found in the notifier"
    return json.loads(m.group(1))


def merge_blocking_check_names(wf_text: str) -> set[str]:
    doc = yaml.safe_load(wf_text)
    names = set()
    for job_id, job in (doc.get("jobs") or {}).items():
        names.add(job.get("name") or job_id)
    return names


def test_review_gates_is_valid_json_list():
    with open(NOTIFIER, encoding="utf-8") as fh:
        gates = review_gates(fh.read())
    assert isinstance(gates, list) and all(isinstance(g, str) for g in gates)


def test_tier3_gate_listed():
    with open(NOTIFIER, encoding="utf-8") as fh:
        assert TIER3_GATE_NAME in review_gates(fh.read())


def test_every_merge_blocking_check_listed():
    with open(NOTIFIER, encoding="utf-8") as fh:
        gates = set(review_gates(fh.read()))
    with open(MERGE_BLOCKING_WF, encoding="utf-8") as fh:
        names = merge_blocking_check_names(fh.read())
    assert names, "merge-blocking-boxes.yml defines no jobs"
    missing = names - gates
    assert (
        not missing
    ), f"merge-blocking check(s) not in REVIEW_GATES: {sorted(missing)}"


def test_merge_blocking_check_also_in_workflow_run_list():
    with open(NOTIFIER, encoding="utf-8") as fh:
        doc = yaml.safe_load(fh.read())
    on = doc.get("on", doc.get(True))
    listed = set(on["workflow_run"]["workflows"])
    with open(MERGE_BLOCKING_WF, encoding="utf-8") as fh:
        wf_name = yaml.safe_load(fh.read())["name"]
    assert (
        wf_name in listed
    ), f"{wf_name!r} missing from the notifier's workflow_run list"


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
