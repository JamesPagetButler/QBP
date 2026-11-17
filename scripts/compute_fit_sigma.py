#!/usr/bin/env python3
"""Computed fit_sigma + one-way status cap on the CTH ledger — QBP#809 phase 1 (AC4).

Beekeeper ruling 2026-11-13 ("adopt your recommendation") on #650's review, refined by
inter#238 D3 (qbp-oppenheimer, "fed-sigma-v1" threshold naming). AC1 (schema) lives in
docs/cth/inventory.schema.v0.3.json / docs/cth/qbp-local-extensions.md; this script is
AC4, the mechanism — nothing here is hand-entered.

For every anchor carrying BOTH a numeric `predicted_value` and `measured_value` (the
candidate set — an anchor missing either is left untouched, never given a stray
fit_sigma/fit_history):

  1. fit_sigma = |predicted_value - measured_value| / sqrt(sigma_meas**2 + sigma_pred**2)
     sigma_pred = 0.0 (no prediction-error field exists yet).
     sigma_meas = measured_error if present, else the side of measured_error_plus/
     measured_error_minus facing the prediction if BOTH are present (plus when
     predicted_value > measured_value, else minus — not a symmetrised average,
     T3 ruling, issuecomment-6886846959), else None.
     Rounded to FIT_SIGMA_ROUND_NDIGITS before storage/comparison so IEEE-754 float
     noise on the predicted/measured subtraction can't push a mathematically-exact
     boundary value (e.g. MEAS-alpha's exact 5.0σ, 128.05-127.95 computed as
     5.000000000000426 in raw float64) across a cap line.
     fit_sigma is None (-> null + fit_sigma_reason) when:
       (a) no usable sigma_meas is pinned yet (most of today's 64 candidates — AC2/AC3
           have not landed; this is EXPECTED and correct pre-phase-2), or
       (b) sigma_meas == 0 with a nonzero discrepancy (undefined: division by zero with
           a real disagreement, e.g. FLAG-ngc2683-mass-discrepancy) — NOT the same as
           sigma_meas == 0 with a ZERO discrepancy, which is a clean fit_sigma = 0.0.

  2. One-way status cap (never raises/improves status, only lowers/worsens-or-caps it):
     fit_sigma > FIT_SIGMA_INCOHERENT_CAP  -> status capped at 'incoherent'-or-worse
     fit_sigma > FIT_SIGMA_MARGINAL_CAP    -> status capped at 'marginal'-or-worse
     Both thresholds are STRICTLY greater-than (exactly 2.0 or exactly 5.0 does not
     trigger) — the issue text's own ">5"/">2" wording, applied uniformly. "Or-worse"
     needs a total severity ordering over the Status enum that upstream does not define;
     SEVERITY below is qbp-oppenheimer's theory-axis ruling on this script's draft
     (issuecomment-6886846959, T2): `contested` is a logical dispute state, not on the
     empirical scale (inter#238 R1), so it is deliberately NOT in SEVERITY — it is
     treated exactly like an unmapped future status: never capped, only flagged.

  2b. REPORT MODE IS THE DEFAULT (T1, qbp-oppenheimer issuecomment-6886846959): the
     #809 ruling caps only where a pinned 1σ error exists, and pinning is AC2 (phase 2,
     not yet done). So by default this script computes fit_sigma + fit_history for real
     (written to the ledger) but leaves `status` untouched, and prints every would-be
     cap instead of applying it. Pass --apply-caps to actually write the capped status
     (the phase-2 PR's job, once AC2 pins real sources) — never the default.

  3. fit_history[] gets one APPENDED entry per evaluation (never overwritten, never
     edited in place — append_fit_history() refuses to replace an existing list), UNLESS
     the run is idempotent: the existing last entry already has the same predicted_value
     AND the same fit_sigma, meaning this evaluation produced no new information (Gemini
     G1, PR #814 review). A trial under inter#238 D3 is a distinct predicted value tried
     against the measurement, not a script invocation — a no-op re-run must not inflate
     that count. When every candidate is idempotent, NOTHING is written: no fit_history
     append, no version bump, no changelog entry (G2). This happens the same way in BOTH
     modes — fit_sigma itself is real, computed data; only the status WRITE is gated on
     --apply-caps.

Usage: python3 scripts/compute_fit_sigma.py [--dry-run] [--apply-caps] [--ledger PATH]
Exit 0 always on a clean run (confinement failures raise and exit non-zero via
cth_ledger_edit's ConfinementError).
"""

import argparse
import math
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402
from ledger_fragment import write_fragment  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"

# fed-sigma-v1 (inter#238 D3): named constants, not inlined — a future PR reuses these.
FIT_SIGMA_MARGINAL_CAP = 2.0
FIT_SIGMA_INCOHERENT_CAP = 5.0
FIT_SIGMA_ROUND_NDIGITS = 9

# Best (0) -> worst (highest) empirical-confidence ordering over the full Status enum.
# Not upstream-defined; qbp-oppenheimer's theory-axis ruling (T2, issuecomment-6886846959):
# `untested` above `marginal`/`incoherent` is correct (a numeric measurement+error IS a
# confrontation); `refuted`==`falsified` tie is correct (both terminal-bad, worse than
# incoherent, and the caps never target either so the tie can't change an outcome);
# `converged` best / `killed` worst: correct. `contested` is DELIBERATELY ABSENT — a
# logical dispute state, not on the empirical scale (inter#238 R1 crosswalks it to n/a) —
# so it takes the same fail-safe "never capped, only flagged" path as an unmapped future
# enum value, below.
SEVERITY = {
    "converged": 0,
    "coherent": 1,
    "untested": 2,
    "marginal": 3,
    "incoherent": 4,
    "refuted": 5,
    "falsified": 5,
    "killed": 6,
}

# Best-effort provenance pointer for fit_history[].source, until AC2 backfills a real
# per-anchor citation of "the PR/spike/leader that produced the prediction".
_SOURCE_FIELDS = ("theory_citation", "theory_url", "theory_doi", "foundation_batch")
_UNRESOLVED_SOURCE = (
    "unresolved — pre-#809 ledger value; phase-2 backfill (QBP#809 AC2) will cite the "
    "originating PR/spike/leader per anchor"
)


def _is_num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool)


def is_candidate(anchor):
    """The candidate set: BOTH predicted_value and measured_value are numeric. Anchors
    outside this set are never touched — no stray fit_sigma/fit_history on a proof or
    axiom that never had a prediction/measurement pair."""
    return _is_num(anchor.get("predicted_value")) and _is_num(
        anchor.get("measured_value")
    )


def sigma_meas_for(anchor):
    """The 1sigma measured uncertainty to use, or None if none is usable yet.

    For an asymmetric error bar, T3 (qbp-oppenheimer, issuecomment-6886846959): use the
    side FACING the prediction — measured_error_plus when predicted_value > measured_value
    (the discrepancy runs through the upper error bar), measured_error_minus otherwise —
    never the average of the two. This is the standard convention; averaging would be a
    different (and wrong) number whenever the two sides differ."""
    me = anchor.get("measured_error")
    if _is_num(me):
        return float(me)
    plus, minus = anchor.get("measured_error_plus"), anchor.get("measured_error_minus")
    if _is_num(plus) and _is_num(minus):
        predicted, measured = anchor.get("predicted_value"), anchor.get(
            "measured_value"
        )
        if _is_num(predicted) and _is_num(measured):
            return float(plus) if predicted > measured else float(minus)
        # Defensive only: is_candidate() already guarantees both are numeric for every
        # caller in this script, so this branch is unreachable in normal use.
        return (float(plus) + float(minus)) / 2.0
    return None


def raw_fit_sigma(predicted, measured, sigma_meas, sigma_pred=0.0):
    """|predicted - measured| / sqrt(sigma_meas**2 + sigma_pred**2), or None at the
    undefined zero-denominator-with-nonzero-discrepancy case. Caller rounds."""
    diff = abs(predicted - measured)
    denom = math.sqrt(sigma_meas**2 + sigma_pred**2)
    if denom == 0:
        return 0.0 if diff == 0 else None
    return diff / denom


def compute_fit_sigma_and_reason(anchor):
    """(fit_sigma: float|None, reason: str|None) for this anchor's CURRENT predicted/
    measured/error fields. reason is set iff fit_sigma is None."""
    predicted, measured = anchor["predicted_value"], anchor["measured_value"]
    sigma_meas = sigma_meas_for(anchor)
    if sigma_meas is None:
        return None, (
            "no usable measured 1σ error recorded (measured_error / "
            "measured_error_plus+measured_error_minus absent) — pending AC2/AC3 "
            "backfill (QBP#809 phase 2)"
        )
    raw = raw_fit_sigma(predicted, measured, sigma_meas)
    if raw is None:
        diff = abs(predicted - measured)
        return None, (
            f"measured_error is 0 but predicted_value != measured_value "
            f"(discrepancy={diff!r}) — fit_sigma undefined at zero denominator"
        )
    return round(raw, FIT_SIGMA_ROUND_NDIGITS), None


def target_cap_for(fit_sigma):
    """The cap floor implied by fit_sigma ALONE, independent of any current status:
    'incoherent', 'marginal', or None if fit_sigma is None or doesn't cross either
    threshold. Exposed separately from capped_status() so the report can flag what a
    status OUTSIDE SEVERITY (e.g. 'contested') would be capped to, without actually
    capping it."""
    if fit_sigma is None:
        return None
    if fit_sigma > FIT_SIGMA_INCOHERENT_CAP:
        return "incoherent"
    if fit_sigma > FIT_SIGMA_MARGINAL_CAP:
        return "marginal"
    return None


def capped_status(current_status, fit_sigma):
    """The one-way cap: never raises (improves) current_status, only lowers (worsens)
    it to meet the cap floor implied by fit_sigma. A status OUTSIDE SEVERITY — an
    unmapped future enum value, or 'contested' (a logical dispute state, not on the
    empirical scale; T2, qbp-oppenheimer issuecomment-6886846959) — is left untouched:
    never capped, never guessed. Use target_cap_for() to report what it WOULD be."""
    target = target_cap_for(fit_sigma)
    if target is None or current_status not in SEVERITY:
        return current_status
    sev = SEVERITY[current_status]
    return target if sev < SEVERITY[target] else current_status


def prediction_source(anchor):
    for key in _SOURCE_FIELDS:
        v = anchor.get(key)
        if isinstance(v, str) and v.strip():
            return f"{key}:{v}"
    return _UNRESOLVED_SOURCE


def history_is_idempotent(history, entry):
    """True iff history's last entry already represents this exact evaluation (same
    predicted_value and fit_sigma) — a repeat run with no new information, not a new
    trial under inter#238 D3 (Gemini G1, PR #814 review). Only these two fields are
    compared: date/source/ledger_version legitimately differ run-to-run without the
    evaluation itself having changed."""
    if not history:
        return False
    last = history[-1]
    return last.get("predicted_value") == entry.get("predicted_value") and last.get(
        "fit_sigma"
    ) == entry.get("fit_sigma")


def append_fit_history(anchor, entry):
    """Append-only: refuses to replace an existing fit_history list, only extends it —
    unless the evaluation is idempotent (history_is_idempotent), in which case the
    existing list is returned unchanged rather than appending a duplicate-looking entry
    (Gemini G1). Returns a list with the same contents either way (a fresh list object
    when it does append; the old list's contents, untouched, when idempotent)."""
    existing = anchor.get("fit_history")
    if existing is not None and not isinstance(existing, list):
        raise TypeError(
            f"fit_history on {anchor.get('id')} is not a list (got {type(existing)}) "
            f"— refusing to overwrite"
        )
    history = list(existing) if existing else []
    if history_is_idempotent(history, entry):
        return history
    return history + [entry]


def evaluate(anchor, ledger_version, date, apply_caps):
    """Compute the full update for one candidate anchor. fit_sigma/fit_history are
    always real, computed data. `status` is only actually changed when apply_caps is
    True (T1: phase 1 defaults to report mode — the #809 ruling caps only where a
    PINNED 1σ error exists, and pinning is AC2/phase 2, not this PR). Returns a dict of
    the field values to apply, plus a one-line summary string for the run report."""
    fit_sigma, reason = compute_fit_sigma_and_reason(anchor)
    old_status = anchor.get("status")
    would_cap = capped_status(old_status, fit_sigma)
    target = target_cap_for(fit_sigma)
    entry = {
        "date": date,
        "predicted_value": anchor["predicted_value"],
        "source": prediction_source(anchor),
        "ledger_version": ledger_version,
        "fit_sigma": fit_sigma,
    }
    new_history = append_fit_history(anchor, entry)
    applied_status = would_cap if apply_caps else old_status

    flag = ""
    if would_cap != old_status:
        verb = "CAP" if apply_caps else "WOULD-CAP (report mode, not applied)"
        flag = f"  {verb} {old_status} -> {would_cap}"
    elif target is not None and old_status not in SEVERITY:
        # e.g. contested: fit_sigma crosses a line, but the status is deliberately
        # outside SEVERITY, so it is flagged, never capped (T2).
        flag = f"  UNMAPPED STATUS {old_status!r} not capped (would-target={target})"

    summary = (
        f"{anchor['id']:50s} fit_sigma={fit_sigma!s:14s} "
        f"{'(' + reason[:40] + '...)' if reason else '':44s} status={old_status}{flag}"
    )
    return {
        "fit_sigma": fit_sigma,
        "fit_sigma_reason": reason,
        "status": applied_status,
        "would_cap": would_cap,
        "fit_history": new_history,
        "summary": summary,
    }


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument(
        "--apply-caps",
        action="store_true",
        help=(
            "Actually write the one-way status cap (T1: NOT the default — phase 1 "
            "computes fit_sigma/fit_history for real but reports would-be caps only, "
            "since the #809 ruling caps only on a PINNED 1σ error, and pinning is "
            "AC2/phase 2). Pass this once AC2 has pinned real sources."
        ),
    )
    ap.add_argument("--ledger", default=str(LEDGER))
    ap.add_argument(
        "--pr",
        type=int,
        help=(
            "The PR number this run's fragment belongs to (QBP#817 variant A: "
            "required whenever this run actually changes anything — the ledger's "
            "version/changelog/last_updated are frozen, so a real change is "
            "recorded as a fragment under archive/cth-inventory/changes.d/ "
            "instead, and the changelog view needs a PR number to link)."
        ),
    )
    ap.add_argument(
        "--slug",
        help="Fragment slug (default: a timestamp, unique per real run).",
    )
    args = ap.parse_args()

    date = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    n_candidates = n_computed = n_null = n_capped = n_would_cap = n_written = 0
    with ledger_edit(args.ledger, dry_run=args.dry_run) as ed:
        L = ed.ledger
        # QBP#817 variant A: version is frozen, read-only here — never bumped,
        # never touched. Still a legitimate per-anchor fit_history provenance
        # value: "this evaluation ran when the ledger's frozen base was X".
        frozen_base = L["version"]

        # snapshot ids first: we look records up by id as we go via ed.record()
        candidate_ids = [a["id"] for a in L["anchors"] if is_candidate(a)]
        n_candidates = len(candidate_ids)
        by_id = {a["id"]: a for a in L["anchors"]}

        touched = []
        touched_ids = []
        would_caps = []
        for aid in candidate_ids:
            raw = by_id[aid]
            old_status = raw.get("status")
            old_fit_sigma = raw.get("fit_sigma")
            old_fit_sigma_reason = raw.get("fit_sigma_reason")
            old_history = raw.get("fit_history") or []

            # Read-only evaluation first (evaluate() does not mutate): decide whether
            # this candidate actually changes BEFORE declaring it to ed.record(), so an
            # idempotent re-run (Gemini G1/G2) declares nothing and raises no silent-
            # no-op ConfinementError.
            upd = evaluate(raw, frozen_base, date, args.apply_caps)
            touched.append(upd["summary"])
            if upd["fit_sigma"] is None:
                n_null += 1
            else:
                n_computed += 1
            if upd["would_cap"] != old_status:
                n_would_cap += 1
                would_caps.append((aid, old_status, upd["would_cap"], upd["fit_sigma"]))

            will_change = (
                upd["fit_sigma"] != old_fit_sigma
                or upd["fit_sigma_reason"] != old_fit_sigma_reason
                or upd["status"] != old_status
                or upd["fit_history"] != old_history
            )
            if not will_change:
                continue

            n_written += 1
            touched_ids.append(aid)
            if upd["status"] != old_status:
                n_capped += 1
            a = ed.record("anchors", aid)
            a["fit_sigma"] = upd["fit_sigma"]
            if upd["fit_sigma_reason"] is not None:
                a["fit_sigma_reason"] = upd["fit_sigma_reason"]
            else:
                a.pop("fit_sigma_reason", None)
            a["status"] = upd["status"]
            a["fit_history"] = upd["fit_history"]

        if n_written:
            # QBP#817 variant A: version/changelog/last_updated are frozen — a real
            # change is recorded as a fragment instead (ed.touch() on any of the
            # three would now raise ConfinementError by construction).
            mode_note = (
                f"{n_capped} had their status one-way capped (never raised, only "
                f"lowered/capped) by the fed-sigma-v1 thresholds"
                if args.apply_caps
                else (
                    f"REPORT MODE (T1, qbp-oppenheimer issuecomment-6886846959): status "
                    f"is NOT written here — {n_would_cap} anchor(s) would be capped once "
                    f"AC2 pins a real source (listed in the PR/run output), by the "
                    f"fed-sigma-v1 thresholds"
                )
            )
            fragment_note = (
                f"QBP#809 phase 1 (AC4): scripts/compute_fit_sigma.py evaluated "
                f"{n_candidates} candidate anchor(s); {n_written} actually changed "
                f"({n_computed} real fit_sigma, {n_null} null + fit_sigma_reason "
                f"among all candidates; the rest were idempotent re-evaluations, "
                f"Gemini G1/G2, and wrote nothing). {mode_note} "
                f"(fit_sigma > {FIT_SIGMA_INCOHERENT_CAP} -> incoherent-or-worse; "
                f"> {FIT_SIGMA_MARGINAL_CAP} -> marginal-or-worse; inter#238 D3). "
                f"fit_history[] appended only where the evaluation changed — a repeat "
                f"run with the same predicted_value/fit_sigma is not a new trial under "
                f"inter#238 D3 and does not inflate the trials count. AC1 schema fields "
                f"(measured_error 1σ convention, measured_error_plus/minus, "
                f"measured_source minLength, fit_sigma/fit_sigma_reason/fit_history) in "
                f"docs/cth/inventory.schema.v0.3.json 0.3.8. AC2/AC3/AC5/AC6 remain phase 2."
            )
            if not args.dry_run:
                if not args.pr:
                    raise SystemExit(
                        "this run changed anchors, so it needs --pr <number> to write "
                        "its changes.d/ fragment (QBP#817 variant A)"
                    )
                slug = args.slug or datetime.now(timezone.utc).strftime(
                    "run-%Y%m%d-%H%M%S"
                )
                # changes.d/ is a sibling of the ledger actually in use (not a
                # hardcoded repo-root default) — matters for tests pointed at a
                # tmp_path ledger, same bug class as generate_ledger_changelog_view.
                write_fragment(
                    issue=809,
                    slug=slug,
                    pr=args.pr,
                    encoder="scripts/compute_fit_sigma.py",
                    note=fragment_note,
                    touched_ids=touched_ids,
                    changes_dir=Path(args.ledger).resolve().parent / "changes.d",
                )

    mode = (
        "APPLY-CAPS" if args.apply_caps else "REPORT MODE (default, status not written)"
    )
    if n_written:
        print(
            f"{'DRY-RUN ' if args.dry_run else ''}compute_fit_sigma [{mode}]: "
            f"{n_candidates} candidate(s) ({n_computed} computed, {n_null} null), "
            f"{n_written} changed, {n_would_cap} would-be cap(s), {n_capped} status "
            f"cap(s) actually applied; ledger frozen base {frozen_base} "
            f"(version is derived, QBP#817: see scripts/ledger_version.py)"
        )
    else:
        print(
            f"{'DRY-RUN ' if args.dry_run else ''}compute_fit_sigma [{mode}]: "
            f"{n_candidates} candidate(s) ({n_computed} computed, {n_null} null) — "
            f"no-op: every candidate's evaluation already matches its stored "
            f"fit_sigma/fit_history/status at ledger frozen base {frozen_base}; "
            f"nothing written (Gemini G1/G2, a repeat evaluation is not a new trial)."
        )
    print()
    for line in touched:
        print(line)
    if would_caps and not args.apply_caps:
        print()
        print(
            f"Would-be caps ({len(would_caps)}, NOT applied — phase 2/AC5 territory):"
        )
        for aid, old, new, fs in would_caps:
            print(f"  {aid:50s} {old} -> {new}  (fit_sigma={fs})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
