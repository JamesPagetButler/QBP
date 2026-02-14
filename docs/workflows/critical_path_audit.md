# Herschel: Critical Path Audit

A systematic audit to ensure all necessary GitHub issues exist for the complete experimental roadmap, with correct Sprint field assignments and consistent labels.

## Invocation

```
"Herschel, run a Critical Path Audit"
```

## Purpose

Verify that the project board and issue tracker have complete coverage for:
- All experiments in the roadmap
- All phases per sprint (7 total)
- Correct sprint numbering
- Project board field options
- **Sprint field values set correctly for every critical-path issue**
- **Labels applied consistently per the label schema**

## Audit Parameters

Before running, confirm these with James:

| Parameter | Options |
|-----------|---------|
| **Scope** | Full roadmap / Specific sprints |
| **Action on gaps** | Report only / Create issues / Hybrid |
| **Sprint mapping** | 1:1 (one experiment = one sprint) |
| **Retrospectives** | Yes, verify for all sprints |

## Audit Checklist

### 1. Gather Source Data

```bash
# Read experiment list
cat research/README.md

# List all issues with labels
gh issue list --state all --limit 300 --json number,title,state,labels

# List all board items with Sprint field values
gh project item-list 1 --owner JamesPagetButler --limit 300 --format json
```

### 2. Verify Sprint Structure

Each sprint requires **7 phases**:

| Phase | Issue Title Pattern |
|-------|---------------------|
| 1. Ground Truth | `Experiment XX: [Name] - Phase 1: Ground Truth` |
| 2. Implementation | `Experiment XX: [Name] - Phase 2: Implementation` |
| 3. Visualization | `Experiment XX: [Name] - Phase 3: Visualization` |
| 4. Formal Verification | `Experiment XX: [Name] - Phase 4: Formal Verification` |
| 4a. Formal Proof | `Experiment XX: Phase 4a — Formal Proof (Lean 4)` |
| 4b. Proof Review | `Experiment XX: Phase 4b — Proof Review` |
| 4c. Proof Visualization | `Experiment XX: Phase 4c — Interactive Proof Visualization` |
| 4d. Differential Testing | `Experiment XX: Phase 4d — Verified Differential Testing` |
| 4e. Simulation Engine | `Experiment XX: Phase 4e — Verified Simulation Engine` |
| 5. Publication | `Experiment XX: [Name] - Phase 5: Publication` |
| 6. Theory Refinement | `Sprint N Theory Refinement: Post [Name] Analysis` |
| 7. Retrospective | `Sprint N Retrospective: Experiment XX ([Name])` |

### 3. Verify Sprint ↔ Experiment Mapping

| Sprint | Experiment | Description |
|--------|------------|-------------|
| 1 | 01 | Stern-Gerlach |
| 2 | 01b | Angle-Dependent Measurement |
| 3 | 03 | Double-Slit |
| 4 | 04 | Lamb Shift |
| 5 | 05 | Anomalous g-2 |
| 6 | 06 | Bell's Theorem |
| 7 | 07 | Particle Statistics |
| 8 | 08 | Positronium |
| 9 | 09 | Hydrogen Spectrum |
| 10 | 10 | Gravity Tests |

### 4. Check Project Board — Membership AND Sprint Field (MANDATORY)

**Both checks are required. Board membership without correct Sprint field is a failure.**

```bash
# Get all board items with Sprint field values
gh project item-list 1 --owner JamesPagetButler --limit 300 --format json

# For EVERY critical-path issue, verify:
#   1. Issue is on the board (item exists)
#   2. Sprint field is set to the CORRECT sprint (not null, not wrong sprint)
```

Report must include a **Sprint Field Verification Table**:

| Issue | Expected Sprint | Actual Sprint | Status |
|-------|----------------|---------------|--------|
| #263 | Sprint 4 | Sprint 4: Lamb Shift | PASS |
| #264 | Sprint 4 | NOT SET | **FAIL** |

**Any FAIL = action required before audit can pass.**

### 5. Check Labels (MANDATORY)

**Every issue must have labels matching its type. Missing labels are audit failures.**

#### Label Schema

| Issue Type | Required Labels |
|------------|----------------|
| Experiment Phase 1 | `type: experiment`, `phase: ground-truth` |
| Experiment Phase 2 | `type: experiment`, `phase: implementation` |
| Experiment Phase 3 | `type: experiment`, `phase: visualization` |
| Experiment Phase 4/4a/4b/4c/4d/4e | `type: experiment`, `phase: proof` |
| Experiment Phase 5 | `type: experiment`, `phase: publication` |
| Theory Refinement | `type: research` |
| Retrospective | `type: retrospective` |
| Research issues | `type: research` |
| Hypergraph/infra | `type: infra` |
| Housekeeping | `housekeeping` |

Report must include a **Label Verification Table** for any issues with missing/wrong labels.

### 6. Set Sprint Field Values (when fixing gaps)

After adding issues to the board, set their Sprint field:

```bash
# Get project ID
gh project list --owner JamesPagetButler --format json | jq '.projects[0].id'

# Get Sprint field ID and option IDs
gh project field-list 1 --owner JamesPagetButler --format json | jq '.fields[] | select(.name == "Sprint")'

# Set Sprint field for an issue (replace IDs)
gh project item-edit \
  --project-id PVT_kwHOAHUYqc4BOWYV \
  --id <ITEM_ID> \
  --field-id PVTSSF_lAHOAHUYqc4BOWYVzg9E_kw \
  --single-select-option-id <SPRINT_OPTION_ID>
```

### 7. Common Issues to Check

| Issue Type | How to Detect | Fix |
|------------|---------------|-----|
| Misnumbered Theory Refinement | Title says wrong sprint | `gh issue edit N --title "..."` |
| Missing Retrospective | No issue for Sprint N Retrospective | Create from template |
| Missing Phase 4 sub-issues | Parent exists, no 4a/4b/4c/4d/4e | Create sub-issues |
| Issues not on board | Not in project item list | `gh project item-add` |
| Sprint field options wrong | API shows wrong names | Fix in UI (manual) |
| **Sprint field not set** | `sprint: null` in item list | `gh project item-edit` with field ID |
| **Wrong labels** | Labels don't match schema | `gh issue edit --add-label/--remove-label` |
| **Wrong label from bulk creation** | e.g., `housekeeping` on experiment issues | Remove wrong label, add correct ones |

## Issue Creation Checklist

**When creating new issues (bulk or individual), ALWAYS apply these before marking creation complete:**

1. **Add to project board** — `gh project item-add`
2. **Set Sprint field** — `gh project item-edit` with correct sprint option
3. **Apply labels per schema** — See Label Schema table above
4. **Verify all three** — Query back to confirm

**Never report "issues created" without confirming all three steps are done.**

## Output

After audit, report:

1. **Gap Summary Table** — What's missing, count, action needed
2. **Sprint-by-Sprint Status** — Each sprint's issue coverage
3. **Sprint Field Verification** — PASS/FAIL for every critical-path issue's Sprint field
4. **Label Verification** — PASS/FAIL for every critical-path issue's labels
5. **Manual Actions Required** — Anything that can't be automated (e.g., field options)

## History

| Date | Auditor | Findings |
|------|---------|----------|
| 2026-02-10 | Herschel (Claude) | 8 Theory Refinement issues renumbered, 8 Retrospectives created, 3 Phase 4 sub-issues created, 18 issues added to board, Sprint field values set, Sprint field options corrected (UI) |
| 2026-02-12 | Herschel (Claude) | 3 Sprint 3 Phase 4 sub-issues created (#259, #260, #261), #22 title fixed ("Experiment 3" → "Experiment 03"), 6 issues added to board (#190, #255, #258, #259, #260, #261), Sprint field values set, SPRINT_STATUS.md knowledge graph counts updated (21→42 vertices, 9→10 hyperedges) |
| 2026-02-12 | Herschel (Claude) | 21 Phase 4 sub-issues created for Sprints 4-10 (#263-#283), all added to project board. Title consistency verified against #256 renumbering — all correct. Phase 4d (#242) and 4e (#245) closed via PR #262. Sprint 3 blocked on Pre-Sprint Research #255. **NOTE: Sprint field values were NOT set for #263-#283. Labels incorrectly set to `housekeeping` instead of `type: experiment` + `phase: proof`.** |
| 2026-02-13 | Herschel (Claude) | **Root cause analysis of Sprint field + label gaps.** Fixed: 21 Sprint fields set (#263-#283), 27 Phase 4 sub-issues relabeled (removed `housekeeping`, added `type: experiment` + `phase: proof`), 10 retrospectives labeled (`type: retrospective` — new label), 5 research/theory issues labeled, 4 hypergraph issues labeled. **Audit procedure hardened:** Added mandatory Sprint Field Verification and Label Verification steps. Added Issue Creation Checklist. Fixed Sprint 3 experiment mapping (03, not 02). |
| 2026-02-13 | Herschel (Claude) | **Phase 4 expansion: 4a/4b/4c → 4a/4b/4c/4d/4e.** Created 20 new issues (#297-#316): Phase 4d and 4e for all 10 sprints. All labeled `type: experiment` + `phase: proof`, added to project board, Sprint fields set. Updated 10 parent Phase 4 issues (#55, #163, #56-#63) with 4d/4e sub-issue references. Updated 6 docs (CONTRIBUTING.md, SPRINT_STATUS.md, critical_path_audit.md, sprint_mode_workflow.md, TODO.md, MEMORY.md). Sprints 1-2 issues marked as deferred (pre-date 4d/4e standard). |

---

*This audit should be run at the start of each new sprint or when experiments are added/reorganized.*
