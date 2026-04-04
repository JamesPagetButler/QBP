# V&V Checklist — Experiment 03: Double-Slit

**Issue:** #302 (Phase 4e)
**Sprint:** 3
**Date:** 2026-02-21

## Setup Verification

| # | Check | Expected | Actual | Pass |
|---|-------|----------|--------|------|
| 1 | Lab room loads without crash | 3D room visible, 4000+ FPS | | [ ] |
| 2 | Optical bench visible | Source, barrier, detector on bench | | [ ] |
| 3 | Double-slit barrier has two visible gaps | Two slits in brass barrier plate | | [ ] |
| 4 | Detector screen visible | Ivory panel at +X end of bench | | [ ] |

## Behavior Verification

| # | Check | Expected | Actual | Pass |
|---|-------|----------|--------|------|
| 5 | Emitter starts on launch | Particles accumulate on detector | | [ ] |
| 6 | Enter toggles start/stop | Particles stop/resume on Enter key | | [ ] |
| 7 | Slit separation slider works | Dragging slider changes d value | | [ ] |
| 8 | Slider resets detector | Changing d clears accumulated hits | | [ ] |
| 9 | Preset keys apply parameters | 5=Bach, 6=Zeilinger, 7=Tonomura | | [ ] |
| 10 | Oracle overlay toggles | O key shows/hides Fraunhofer curve | | [ ] |
| 11 | R key resets detector | Clears all accumulated particles | | [ ] |

## Results Validation

| # | Check | Expected | Actual | Pass |
|---|-------|----------|--------|------|
| 12 | V&V verdict on preset | N>1000 → PASS (fringe spacing within 5%) | | [ ] |
| 13 | Custom params show UNVALIDATED | Moving slider away from preset | | [ ] |

## Acceptance Criteria (from #302)

- [ ] **AC1:** Go simulation scene implemented for Experiment 03
- [ ] **AC2:** Physics oracle provides Lean-proven predictions
- [ ] **AC3:** Human can manipulate experiment setup parameters
- [ ] **AC4:** V&V checklist documented and completed

## Sign-off

| Role | Name | Date |
|------|------|------|
| Developer | Claude (Herschel) | |
| Reviewer | James | |
