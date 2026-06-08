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
| #474 AC6 exp/log cell | MET-pending (beekeeper, 2026-06-08) — exp total + log on dense domain + exp∘log=id clears "well-defined"; full-ℝ group law & left-inverse are enhancements | flip AC6 exp/log cell pending→full in #474 tracking + matrix index (PR-G) annotation | issue: #525 | status: pending |
