# Results Versioning Protocol

*Protocol for managing experiment result files across sprint rework cycles.*

---

## Problem

As experiments undergo multiple rework phases, output formats change (new columns, renamed columns, different file counts). Without a protocol, the `results/` directory accumulates incompatible generations of files.

---

## Directory Structure

```
results/
  {experiment_id}/
    v{N}/                          # Versioned subdirectory
      {datatype}_{timestamp}.csv   # Timestamped data files
      metadata_{timestamp}.json    # Run metadata
      summary_{timestamp}.csv      # Summary statistics
    CURRENT -> v{N}                # Symlink to latest version
    v{N-1}/                        # Previous version (archived)
```

### Example

```
results/
  03_double_slit/
    v3/
      results_nearfield_2026-02-15_01-23-50.csv
      results_farfield_2026-02-15_01-23-50.csv
      decay_2026-02-15_01-23-50.csv
      metadata_2026-02-15_01-23-50.json
      summary_2026-02-15_01-23-50.csv
    CURRENT -> v3
    v2/
      fringe_data_2026-02-14_22-11-52.csv
      ...
```

---

## Versioning Rules

### When to Increment Version

A new version (`v{N+1}`) is required when a Phase 2 rework changes any of:

| Change | Requires new version? |
|--------|----------------------|
| CSV schema (new/renamed/removed columns) | Yes |
| Number of output files changes | Yes |
| File naming convention changes | Yes |
| Metadata format version changes | Yes |
| Bug fix (same schema, corrected values) | No — overwrite in current version |
| Re-run with different parameters | No — new timestamp in current version |

### Version Numbering

- `v1` — initial experiment implementation
- `v2`, `v3`, ... — each Phase 2 rework that changes the schema
- Version numbers are experiment-local (Experiment 01 and 03 each have their own v1, v2, etc.)

---

## Consumer Discovery

### Recommended: CURRENT Symlink

Consumers (viz, analysis, tests) should discover the latest results via the `CURRENT` symlink:

```python
from pathlib import Path

results_dir = Path("results/03_double_slit/CURRENT")
nearfield = sorted(results_dir.glob("results_nearfield_*.csv"))[-1]
```

### Why Symlinks

| Approach | Pros | Cons |
|----------|------|------|
| **Symlink (chosen)** | Simple, filesystem-native, no code needed | Doesn't work on all platforms |
| Manifest JSON | Portable, metadata-rich | Extra file to maintain |
| Glob for highest vN | No extra files | Fragile if naming changes |

**Fallback for CI/Windows:** If symlinks aren't available, consumers should glob for `v*/` and pick the highest version number.

---

## Archival Policy

| Age | Action |
|-----|--------|
| Current version | Active use — read/write |
| Previous version (N-1) | Read-only archive — kept for audit trail |
| Older versions (N-2 and below) | May be deleted after sprint retrospective confirms no regressions |

**Never delete results during an active sprint.** Cleanup happens during retrospective.

---

## Metadata Requirements

Each version directory must contain a `metadata_{timestamp}.json` with at minimum:

```json
{
  "version": 3,
  "experiment": "03_double_slit",
  "created_by": "simulate.py",
  "created_at": "2026-02-15T01:23:50Z",
  "schema_changes": "Split fringe_data into nearfield + farfield; added far-field FFT",
  "parent_version": 2,
  "columns": {
    "results_nearfield": ["regime", "U1_strength_eV", "eta0", "x_position_m", "..."],
    "results_farfield": ["regime", "U1_strength_eV", "eta0", "x_position_m", "..."]
  }
}
```

---

## Sprint Workflow Integration

During each Phase 2 rework:

1. **Check current version:** Read `results/{experiment}/CURRENT` target
2. **Create new version:** `mkdir results/{experiment}/v{N+1}`
3. **Update simulate.py:** Point output directory to new version
4. **Run simulation:** Generates timestamped files in new version dir
5. **Update symlink:** `ln -sfn v{N+1} results/{experiment}/CURRENT`
6. **Update consumers:** Analysis and viz scripts use `CURRENT` (no change needed if already using symlink)
7. **Commit:** Include new version dir + updated symlink in the PR

---

## Current State (as of Sprint 3)

| Experiment | Latest Version | Notes |
|-----------|---------------|-------|
| 01_stern_gerlach | v1 | Migrated — `CURRENT -> v1` |
| 01b_angle_dependent | v1 | Migrated — `CURRENT -> v1` |
| 03_double_slit | v3 | `CURRENT -> v3` (v2 archived) |

All experiments now follow the versioned protocol.

---

## References

- [Issue #341](https://github.com/JamesPagetButler/QBP/issues/341) — Tracking issue
- [Issue #340](https://github.com/JamesPagetButler/QBP/issues/340) — Phase 2 rework that surfaced this need
- [Sprint Mode Workflow](sprint_mode_workflow.md) — Sprint execution process
