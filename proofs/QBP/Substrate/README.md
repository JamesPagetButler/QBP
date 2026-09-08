# QBP.Substrate

**Status change 2026-09-07.** This directory was RESERVED (no Lean files) under
the #471 rule that sorried scaffolding is banned. The beekeeper LIFTED that rule
for exactly one file (#473 `issuecomment-5574256922`, 2026-09-07):
`Hosting.lean`, the hosting **definition** file for #639.

## Files

| File | Role |
|---|---|
| `Hosting.lean` | The hosting frame as definitions: `StateSphere` (the substrate = imaginary unit sphere of 𝕊), `potential` (V = ‖[cdLo s, cdHi s]‖²), `UniverseSpace` / `InFlight`, `Universe` and `Universe.hosted`. Definitions plus inhabitedness/coherence theorems only — **no new mathematics**; every substantive result restates a `QBP.Foundations` theorem and cites it. |

Aggregator: `QBP/Substrate.lean` (imported from `QBP.lean`).

## Standing constraints

* Layer rules: `docs/foundations/layer-architecture.md`. Substrate imports
  `QBP.Foundations` (enrichment direction) and never imports `QBP.Physics`
  except via ratified bridge files.
* Zero `sorry`, zero `native_decide`, zero vacuous `True` stubs; every theorem
  carries a `#print axioms` line and must show a subset of
  `{propext, Classical.choice, Quot.sound}` (`decide`-based lemmas show fewer).
* `Hosting.lean` derives **no** measure, **no** rule/flow, **no** boundary or
  holography semantics, and does **not** identify the crystal's ℍ with "the
  observer's ℍ" (DERIV-holographic flag 3 pending). See its §11 for the full
  not-in-this-file list with issue owners (#635, #636, #637, #639).
* The condensed/locale substrate mathematics remains napkin-level and is still
  gated; nothing here authorises new files beyond the lift above.
