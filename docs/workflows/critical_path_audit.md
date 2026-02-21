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

## Rate Limit Safety

**CRITICAL:** The GitHub GraphQL API has a 5,000 req/hr budget shared across all `gh` CLI operations. On 2026-02-19, a per-issue audit loop exhausted this budget and blocked all board operations for ~1 hour (see #377).

**Before starting any audit:**
```bash
gh api graphql -f query='{ rateLimit { remaining resetAt } }'
```

If `remaining < 500`, defer the audit until the budget resets.

**After the audit completes**, log the remaining budget again. If the audit consumed >200 requests, investigate and optimize.

## Cache-First Audit Pattern

**All read operations use bulk-fetched cache files.** Individual API calls are reserved for write operations only.

### Step 0: Check Rate Limit

```bash
gh api graphql -f query='{ rateLimit { remaining resetAt } }'
# Abort if remaining < 500
```

### Step 1: Bulk-Fetch All Data (≤3 API calls)

```bash
# 1a. Fetch ALL board items (1 API call)
gh project item-list 1 --owner JamesPagetButler --format json --limit 300 > /tmp/board_cache.json

# 1b. Fetch ALL issues with labels and state (1 API call)
gh issue list --repo JamesPagetButler/QBP --state all --limit 500 \
  --json number,title,state,labels > /tmp/issues_cache.json

# 1c. Fetch Sprint field options (1 API call)
gh project field-list 1 --owner JamesPagetButler --format json > /tmp/fields_cache.json
```

### Step 2: Parse Caches Locally (0 API calls)

All verification steps below operate on the cached JSON files using `python3` or `jq`. **No per-issue API calls.**

```bash
# Example: Find issues missing from board
python3 -c "
import json
board = json.load(open('/tmp/board_cache.json'))
issues = json.load(open('/tmp/issues_cache.json'))
board_nums = {i['content']['number'] for i in board['items'] if i.get('content')}
issue_nums = {i['number'] for i in issues}
missing = issue_nums - board_nums
if missing:
    print(f'Issues not on board: {sorted(missing)}')
else:
    print('All issues on board')
"

# Example: Find board items with no Sprint field
python3 -c "
import json
board = json.load(open('/tmp/board_cache.json'))
no_sprint = [i for i in board['items'] if not i.get('sprint')]
for item in no_sprint:
    num = item.get('content', {}).get('number', '?')
    print(f'  #{num}: {item[\"title\"]} — sprint not set')
print(f'Total without Sprint: {len(no_sprint)}')
"

# Example: Find issues with wrong/missing labels
python3 -c "
import json
issues = json.load(open('/tmp/issues_cache.json'))
for issue in issues:
    labels = [l['name'] for l in issue.get('labels', [])]
    if not labels:
        print(f'  #{issue[\"number\"]}: {issue[\"title\"]} — NO LABELS')
"
```

## Audit Checklist

### 1. Gather Source Data (from cache)

```bash
# Read experiment list (local file, no API call)
cat research/README.md

# Issues and board data already cached in Step 1 above
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

### 4. Check Project Board (from cache)

```bash
# Sprint field options (from /tmp/fields_cache.json)
python3 -c "
import json
fields = json.load(open('/tmp/fields_cache.json'))
for f in fields['fields']:
    if f['name'] == 'Sprint':
        for opt in f.get('options', []):
            print(f'  {opt[\"id\"]}: {opt[\"name\"]}')
"

# Verify issues on board (from /tmp/board_cache.json)
python3 -c "
import json
board = json.load(open('/tmp/board_cache.json'))
for item in board['items']:
    num = item.get('content', {}).get('number', '?')
    sprint = item.get('sprint', 'NOT SET')
    status = item.get('status', '?')
    print(f'  #{num}: sprint={sprint}, status={status}')
"
```

### 5. Set Sprint Field Values (targeted writes only)

Only make individual API calls for issues that **need fixing** (identified from cache analysis).

```bash
# Set Sprint field for an issue (replace IDs)
gh project item-edit \
  --project-id PVT_kwHOAHUYqc4BOWYV \
  --id <ITEM_ID_FROM_CACHE> \
  --field-id PVTSSF_lAHOAHUYqc4BOWYVzg9E_kw \
  --single-select-option-id <SPRINT_OPTION_ID>

# After all writes, re-fetch board cache to verify
gh project item-list 1 --owner JamesPagetButler --format json --limit 300 > /tmp/board_cache.json
```

### 6. Unresolved Pivot Check

Check SPRINT_STATUS.md for the Pivot Log section. For each pivot entry:

| Check | Threshold | Action |
|-------|-----------|--------|
| Pivot OPEN in current sprint | OK | Normal — research in progress |
| Pivot OPEN for > 1 sprint | **WARNING** | Flag in audit report. Verify research issue is actively worked. |
| Pivot OPEN for > 2 sprints | **FAILURE** | Audit fails. Pivot must be resolved or escalated to James. |
| Pivot resolved but no retrospective entry | **WARNING** | Retrospective must include Pivot Analysis section. |

**How to check:**
```bash
# Find OPEN pivots in SPRINT_STATUS.md
grep -A1 "PIVOT-S" SPRINT_STATUS.md | grep "OPEN"
```

Temporary ACs must not become permanent silently. Each audit should verify that resolved pivots have been backported to their original issues (original AC reinstated or permanently replaced with rationale).

### 7. Common Issues to Check

| Issue Type | How to Detect | Fix |
|------------|---------------|-----|
| Misnumbered Theory Refinement | Title says wrong sprint | `gh issue edit N --title "..."` |
| Missing Retrospective | No issue for Sprint N Retrospective | Create from template |
| Missing Phase 4 sub-issues | Parent exists, no 4a/4b/4c | Create sub-issues |
| Issues not on board | Not in project item list | `gh project item-add` |
| Sprint field options wrong | API shows wrong names | Fix in UI (manual) |
| Sprint field not set | `sprint: null` in item list | `gh project item-edit` with field ID |
| Unresolved pivot > 1 sprint | Check Pivot Log in SPRINT_STATUS.md | Verify research issue is active |

## Output

After audit, report:

1. **Rate Limit Usage** — remaining before/after (must not exceed 200 consumed)
2. **Gap Summary Table** — What's missing, count, action needed
3. **Sprint-by-Sprint Status** — Each sprint's issue coverage
4. **Manual Actions Required** — Anything that can't be automated (e.g., field options)

## History

| Date | Auditor | Findings |
|------|---------|----------|
| 2026-02-10 | Herschel (Claude) | 8 Theory Refinement issues renumbered, 8 Retrospectives created, 3 Phase 4 sub-issues created, 18 issues added to board, Sprint field values set, Sprint field options corrected (UI) |
| 2026-02-12 | Herschel (Claude) | 3 Sprint 3 Phase 4 sub-issues created (#259, #260, #261), #22 title fixed ("Experiment 3" → "Experiment 03"), 6 issues added to board (#190, #255, #258, #259, #260, #261), Sprint field values set, SPRINT_STATUS.md knowledge graph counts updated (21→42 vertices, 9→10 hyperedges) |
| 2026-02-12 | Herschel (Claude) | 21 Phase 4 sub-issues created for Sprints 4-10 (#263-#283), all added to project board. Title consistency verified against #256 renumbering — all correct. Phase 4d (#242) and 4e (#245) closed via PR #262. Sprint 3 blocked on Pre-Sprint Research #255. |
| 2026-02-19 | — | GraphQL rate limit exhausted during audit (0/5000 remaining). Root cause: per-issue `gh project item-list` loops. See #377. |
| 2026-02-20 | Herschel (Claude) | Audit procedure rewritten with cache-first pattern (#377). Bulk fetch ≤3 API calls, local parsing, rate limit checks before/after. |

---

*This audit should be run at the start of each new sprint or when experiments are added/reorganized.*
