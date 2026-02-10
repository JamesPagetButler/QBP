# Herschel: Critical Path Audit

A systematic audit to ensure all necessary GitHub issues exist for the complete experimental roadmap.

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

# List all issues
gh issue list --state all --limit 200 --json number,title,state
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
| 5. Publication | `Experiment XX: [Name] - Phase 5: Publication` |
| 6. Theory Refinement | `Sprint N Theory Refinement: Post [Name] Analysis` |
| 7. Retrospective | `Sprint N Retrospective: Experiment XX ([Name])` |

### 3. Verify Sprint ↔ Experiment Mapping

| Sprint | Experiment | Description |
|--------|------------|-------------|
| 1 | 01 | Stern-Gerlach |
| 2 | 01b | Angle-Dependent Measurement |
| 3 | 02 | Double-Slit |
| 4 | 03 | Lamb Shift |
| 5 | 04 | Anomalous g-2 |
| 6 | 05 | Bell's Theorem |
| 7 | 06 | Particle Statistics |
| 8 | 07 | Positronium |
| 9 | 08 | Hydrogen Spectrum |
| 10 | 09 | Gravity Tests |

### 4. Check Project Board

```bash
# List project field options
gh project field-list 1 --owner JamesPagetButler --format json | jq '.fields[] | select(.name == "Sprint") | .options'

# Verify Sprint 2 issues are on board
gh project item-list 1 --owner JamesPagetButler --limit 100 --format json | jq '.items[] | select(.content.number >= 160)'
```

### 5. Set Sprint Field Values

After adding issues to the board, set their Sprint field:

```bash
# Get project ID
gh project list --owner JamesPagetButler --format json | jq '.projects[0].id'

# Get Sprint field ID and option IDs
gh project field-list 1 --owner JamesPagetButler --format json | jq '.fields[] | select(.name == "Sprint")'

# Set Sprint field for an issue (replace IDs)
gh project item-edit \
  --project-id PVT_kwHOAHUYqc4BOWYV \
  --id PVTI_lAHOAHUYqc4BOWYVzglMdVY \
  --field-id PVTSSF_lAHOAHUYqc4BOWYVzg9E_kw \
  --single-select-option-id c2825eef

# Verify Sprint field is set
gh project item-list 1 --owner JamesPagetButler --format json | \
  jq '.items[] | select(.sprint == "Sprint 2: Angle-Dependent (01b)")'
```

### 6. Common Issues to Check

| Issue Type | How to Detect | Fix |
|------------|---------------|-----|
| Misnumbered Theory Refinement | Title says wrong sprint | `gh issue edit N --title "..."` |
| Missing Retrospective | No issue for Sprint N Retrospective | Create from template |
| Missing Phase 4 sub-issues | Parent exists, no 4a/4b/4c | Create sub-issues |
| Issues not on board | Not in project item list | `gh project item-add` |
| Sprint field options wrong | API shows wrong names | Fix in UI (manual) |
| Sprint field not set | `sprint: null` in item list | `gh project item-edit` with field ID |

## Output

After audit, report:

1. **Gap Summary Table** — What's missing, count, action needed
2. **Sprint-by-Sprint Status** — Each sprint's issue coverage
3. **Manual Actions Required** — Anything that can't be automated (e.g., field options)

## History

| Date | Auditor | Findings |
|------|---------|----------|
| 2026-02-10 | Herschel (Claude) | 8 Theory Refinement issues renumbered, 8 Retrospectives created, 3 Phase 4 sub-issues created, 18 issues added to board, Sprint field values set, Sprint field options corrected (UI) |

---

*This audit should be run at the start of each new sprint or when experiments are added/reorganized.*
