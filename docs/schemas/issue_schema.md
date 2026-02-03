# QBP Issue Schema & Best Practices

This document defines the standard structure for GitHub issues in the QBP project, based on industry best practices.

## Sources

- [GitHub Issue Templates Documentation](https://docs.github.com/en/communities/using-templates-to-encourage-useful-issues-and-pull-requests/configuring-issue-templates-for-your-repository)
- [Best Practices for Using GitHub Issues](https://rewind.com/blog/best-practices-for-using-github-issues/)
- [Acceptance Criteria Best Practices](https://www.atlassian.com/work-management/project-management/acceptance-criteria)
- [Definition of Done in Agile](https://www.atlassian.com/agile/project-management/definition-of-done)

---

## Label Taxonomy

Use namespaced labels for clarity and filtering.

### Type Labels (required - pick one)

| Label | Color | Description |
|-------|-------|-------------|
| `type: experiment` | `1D76DB` | Physics experiment implementation |
| `type: feature` | `a2eeef` | New feature or enhancement |
| `type: bug` | `d73a4a` | Something isn't working |
| `type: docs` | `0075ca` | Documentation improvements |
| `type: research` | `D4C5F9` | Theoretical investigation |
| `type: infra` | `F9D0C4` | CI/CD, tooling, infrastructure |

### Status Labels (optional - for triage)

| Label | Color | Description |
|-------|-------|-------------|
| `status: triage` | `FBCA04` | Needs review and prioritization |
| `status: blocked` | `B60205` | Blocked by external dependency |
| `status: ready` | `0E8A16` | Ready for implementation |

### Priority Labels (optional)

| Label | Color | Description |
|-------|-------|-------------|
| `priority: critical` | `B60205` | Must be done immediately |
| `priority: high` | `FF6B6B` | Important, do soon |
| `priority: medium` | `FFC107` | Normal priority |
| `priority: low` | `0E8A16` | Nice to have |

### Effort Labels (optional)

| Label | Color | Description |
|-------|-------|-------------|
| `effort: small` | `C2E0C6` | < 1 day of work |
| `effort: medium` | `FEF2C0` | 1-3 days of work |
| `effort: large` | `F9D0C4` | > 3 days of work |

---

## Issue Structure Schema

### Required Sections

Every issue MUST include:

```markdown
## Summary
[1-2 sentence description of what this issue addresses]

## Background
[Context: why is this needed? Link to related issues/PRs/docs]

## Acceptance Criteria
- [ ] Testable criterion 1
- [ ] Testable criterion 2
- [ ] Testable criterion 3

## Definition of Done
- [ ] Code reviewed and approved
- [ ] Tests pass in CI
- [ ] Documentation updated (if applicable)
```

### Optional Sections

Include as relevant:

```markdown
## Tasks
- [ ] Task 1
- [ ] Task 2

## Technical Approach
[High-level design notes, if non-obvious]

## Dependencies
- Requires #XX to be completed first
- Depends on [external library/tool]

## References
- `path/to/relevant/file.py`
- [Link to documentation](url)

## Out of Scope
- [Explicitly state what this issue does NOT cover]
```

---

## Issue Templates by Type

### Experiment Issue Template

```markdown
## Summary
Implement [Experiment Name] in the quaternionic framework.

## Background
[Physical description of the experiment and its significance]

## Tasks

### Theory Phase
- [ ] Review `research/NN_experiment_expected_results.md`
- [ ] Define quaternionic representation
- [ ] Determine acceptance criteria with error bounds

### Implementation Phase
- [ ] Create `experiments/NN_name/simulate.py`
- [ ] Create `tests/physics/test_name.py`
- [ ] Validate against expected values

### Visualization Phase (if applicable)
- [ ] Create Manim scene
- [ ] Create interactive demo

## Acceptance Criteria
- [ ] Simulation produces correct prediction within tolerance
- [ ] Tests pass in CI
- [ ] Red Team review approved
- [ ] Gemini review approved

## Definition of Done
- [ ] All acceptance criteria met
- [ ] Code reviewed
- [ ] Documentation updated
- [ ] PR merged

## References
- `research/NN_experiment_expected_results.md`
```

### Feature Issue Template

```markdown
## Summary
[What feature is being added]

## Background
[Why is this feature needed]

## Acceptance Criteria
- [ ] Criterion 1 (specific, testable)
- [ ] Criterion 2
- [ ] Criterion 3

## Definition of Done
- [ ] Code reviewed and approved
- [ ] Tests pass in CI
- [ ] Documentation updated

## References
- [Related files/docs]
```

### Bug Issue Template

```markdown
## Summary
[Brief description of the bug]

## Steps to Reproduce
1. Step 1
2. Step 2
3. Step 3

## Expected Behavior
[What should happen]

## Actual Behavior
[What actually happens]

## Environment
- Python version:
- OS:
- Relevant dependencies:

## Acceptance Criteria
- [ ] Bug no longer reproducible
- [ ] Regression test added

## Definition of Done
- [ ] Fix implemented
- [ ] Tests pass
- [ ] No new bugs introduced
```

---

## Best Practices

### Writing Good Issues

1. **Be Specific**: Vague issues lead to scope creep
2. **Make Criteria Testable**: Use pass/fail criteria, not subjective assessments
3. **Link Context**: Reference related issues, PRs, and documentation
4. **Define Scope**: Explicitly state what's out of scope
5. **Keep It Updated**: Update the issue as work progresses

### Acceptance Criteria Guidelines

From [Atlassian](https://www.atlassian.com/work-management/project-management/acceptance-criteria):

- **Testable**: Results must be yes/no or pass/fail
- **Clear**: No ambiguity in interpretation
- **Concise**: Focus on the what, not the how
- **Independent**: Each criterion stands alone

### Definition of Done (Project-Wide)

Every completed issue in QBP must satisfy:

- [ ] Code follows project patterns (`src/` structure)
- [ ] Type hints on public API
- [ ] Tests written and passing
- [ ] Pre-commit hooks pass (black, mypy)
- [ ] PR reviewed by Red Team or Gemini (for physics)
- [ ] Documentation updated if API changed

---

## Issue Lifecycle

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Created   │ ──▶ │   Triaged   │ ──▶ │    Ready    │
│ status:triage│     │  assigned   │     │ status:ready│
└─────────────┘     └─────────────┘     └─────────────┘
                                               │
                                               ▼
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Closed    │ ◀── │  In Review  │ ◀── │ In Progress │
│             │     │   PR open   │     │  branch     │
└─────────────┘     └─────────────┘     └─────────────┘
```

---

## Checklist for New Issues

Before creating an issue, verify:

- [ ] Summary is clear and specific
- [ ] Background provides sufficient context
- [ ] Acceptance criteria are testable
- [ ] Definition of done is included
- [ ] Appropriate type label selected
- [ ] Related issues/docs linked
- [ ] Out of scope defined (if applicable)
