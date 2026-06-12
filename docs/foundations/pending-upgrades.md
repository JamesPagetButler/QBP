# Pending Upgrades Register

Tracks deliverables that are **conditionally complete** — an acceptance-criterion
cell or claim ruled MET for now, but with a known enhancement owed once a named
unblocking issue lands. The companion CI guard (`scripts/check_pending_upgrades.py`)
**fails the build when an unblocking issue here is CLOSED but its row is still
`status: pending`** — converting "we'll update it later" from a memory-dependent
promise into a mechanical merge-gate. (PATTERN-01 lesson: promises-to-update rot;
only an un-mergeable state holds.)

## How to resolve a row when its unblocking issue closes

1. Apply the upgrade the row describes (the AC cell / annotation / doc edit).
2. Change the row's `status:` from `pending` to `resolved` (keep the row as a
   forensic record — mark, don't delete), or delete the row if the register entry
   itself was the only artifact.
3. CI goes green again.

## Register

<!-- one row per pending upgrade; the guard parses: issue: #N | status: pending|resolved -->

| item | ruled | upgrade owed | unblocking issue | status |
|---|---|---|---|---|
| #474 AC6 exp/log cell | RESOLVED (2026-06-11) — full-ℝ one-parameter group law (`exp_smul_add_real`) + left-inverse on the principal strip (`log_exp`, `imNorm<π` tight) proved, kernel-clean | AC6 exp/log cell now FULLY met; #474 AC6 tick on merge; matrix-index annotation lands with the AC7 manifest | issue: #525 | status: resolved |
