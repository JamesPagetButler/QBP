# Pivot Protocol: Handling Mid-Sprint Theory Failures

*When an acceptance criterion fails because the underlying assumptions were wrong, not because the code had bugs.*

**Introduced:** Sprint 3 (2026-02-13) — after AC #9 unit mismatch discovery (PIVOT-S3-001)

---

## Purpose

Sprint workflows assume that when an AC fails, you fix the implementation and iterate. But sometimes an AC failure reveals a **systemic problem**: the theory or assumptions underlying the AC are flawed. The AC itself cannot be satisfied without research, not just code changes.

This protocol defines how to handle mid-sprint pivots when theory must be updated.

---

## 1. Pivot Detection Criteria

A failure is **systemic** (theory/assumptions) rather than **local** (code bug) if:

| Signal | Example |
|--------|---------|
| **AC compares incompatible things** | "Verify BPM natural units match Fraunhofer SI" (different unit systems) |
| **Code is correct but AC remains unmet** | Simulation matches equations, but equations don't match AC predictions |
| **Fixing requires research/derivation** | "Need to define SI mapping for quaternionic quantities" |
| **Review finds theory errors, not code errors** | Both Red Team and Gemini flag the same conceptual problem |

### Decision Gate

1. **Can the AC be satisfied by changing code alone?** If YES = local failure (standard iteration).
2. **Does fixing require re-deriving theory or changing assumptions?** If YES = systemic failure (pivot).
3. **Would satisfying the current AC produce scientifically invalid results?** If YES = pivot is mandatory.

**When in doubt:** Ask James. Pivots change scientific direction — they are NEVER autonomous decisions.

---

## 2. Temporary Fix Protocol

### Step 1: Document the Finding

Add a **Pivot Log Entry** to `SPRINT_STATUS.md`:

```markdown
### PIVOT-SN-XXX: [Short Title]

- **Date:** YYYY-MM-DD
- **Sprint/Phase:** N / M
- **Original AC:** "[Verbatim text]" (Issue #XX)
- **Root Cause:** [What assumption was wrong]
- **Evidence:** [Quote from review or analysis]
- **Research Issue:** #ZZ
- **Temporary AC:** "[Replacement text]"
- **Status:** OPEN / RESOLVED
```

### Step 2: Create Research Issue

The research issue must:
- Reference the pivot ID in its body
- Define what question must be answered
- Close only when the pivot is resolved

### Step 3: Define Temporary Replacement AC

The temporary AC must be:

1. **Scientifically honest** — tests something real, not a placeholder
2. **Testable now** — can be satisfied without waiting for research
3. **Traceable** — explicitly marks itself as temporary with pivot ID

**Bad:** `Skip quaternionic comparison test` (no scientific content)
**Good:** `Verify C(U₁>0) vs C(U₁=0) shows measurable visibility reduction (PIVOT-S3-001)`

### Step 4: Mark Original AC as Deferred

In the issue, annotate the original AC:

```markdown
- [ ] ~~**AC #9:** Scenario C matches A, diff < 10⁻⁴~~
  **DEFERRED** (PIVOT-S3-001): Unit system mismatch. See #319.
  **Temporary AC #9:** C(U₁>0) vs C(U₁=0) visibility drop > 5%
```

### Step 5: Proceed with Sprint

- Continue using the replacement AC
- The research issue is NOT sprint-blocking — it enters the backlog
- Sprint can close with temporary AC satisfied
- Pivot remains OPEN until research resolves it

---

## 3. Traceability

### Pivot Log in SPRINT_STATUS.md

```markdown
## Pivot Log

| ID | Sprint | Original AC | Research Issue | Status |
|----|--------|-------------|----------------|--------|
| PIVOT-S3-001 | 3 | AC #9: C matches A | #319 | OPEN |
```

### Pivot ID Format

`PIVOT-SN-NNN` — Sprint number + sequential (001, 002, ...).

### Critical Path Audit Check

The audit must check for unresolved pivots:
- **Warning:** Any pivot OPEN for > 1 sprint
- **Failure:** Any pivot OPEN for > 2 sprints

Temporary ACs must not become permanent silently.

---

## 4. Retrospective Integration

Every pivot triggers a **mandatory retrospective item**:

```markdown
### Pivot Analysis: PIVOT-SN-XXX

1. **What assumption was wrong?**
2. **Why didn't we catch it earlier?** (Pre-Sprint Research? Ground truth review?)
3. **What check would have caught it?** (Dimensional analysis? Unit consistency?)
4. **Process update:** [What workflow change prevents recurrence]
```

This is **required** for sprint closure, even if the research issue is still open.

---

## 5. Anti-Fragility Principle

**Core rule:** Each pivot must make the system stronger.

### Required Outputs per Pivot

| Output | Purpose |
|--------|---------|
| Updated workflow/checklist | Close the gap that allowed the bad AC |
| Knowledge graph entry | Document the corrected understanding |
| Retrospective analysis | Extract lessons for future sprints |

### Examples

| Pivot Cause | Anti-Fragility Response |
|-------------|------------------------|
| Unit system mismatch | Add "Unit Consistency" to AC verification protocol |
| Wrong equation citation | Add "Primary Source Verification" to ground truth schema |
| Dimensionally incorrect formula | Add "Dimensional Analysis" to Tier 3 reviews |

---

## 6. Workflow Integration

### In PR Review Protocol

When reviews identify a systemic failure:

1. **Red Team/Gemini:** Flag as "BLOCKING (PIVOT REQUIRED)"
2. **Synthesis:** Create pivot log entry and research issue
3. **Pivot Proposal:** Present temporary AC to James
4. **James Decision:** Approve temporary AC OR block sprint
5. **Proceed:** If approved, continue with temporary AC

### In Focus/Sprint Mode

1. **STOP** — Do not proceed with original AC
2. **Document** — Create pivot log entry
3. **Escalate** — Present finding + proposed temporary AC to James
4. **Await approval** — Do not resume until James approves

---

## 7. First Application: PIVOT-S3-001

**Date:** 2026-02-13
**Sprint/Phase:** 3 / Phase 3 (Visualization)

**What Failed:** AC #9 — "At detector, Scenario C matches Scenario A — Difference < 10⁻⁴"
**Result:** max |residual| = 0.997 (off by ~4 orders of magnitude)

**Root Cause:** Scenario A (Fraunhofer) uses SI metres with plane-wave source. Scenario C (BPM) uses natural units (h=m=1) with Gaussian wavepacket. The comparison is physically meaningless — different unit systems, different source profiles. Not a code bug.

**Evidence:** Both Red Team (Sabine) and Gemini (Furey, Feynman) independently flagged this. James identified the deeper cause: no SI mapping exists for quaternionic quantities.

**Research Issue:** #319 (Quaternionic SI Definitions)
**Housekeeping Issue:** #320 (SI Standardization & Enforcement)

**Temporary AC #9:** Verify that Scenario C with U₁>0 shows measurable visibility reduction compared to C with U₁=0, consistent with the coherence sink effect (V_norm drop > 5% at U₁=10).

**Anti-Fragility Response:**
- Created #320 with mandatory unit enforcement at issue level
- Review workflow to include unit consistency verification
- Issue template to require SI unit declarations

**Status:** OPEN — resolves when #319 delivers SI definitions
