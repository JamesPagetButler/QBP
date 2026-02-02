# Claude Prompt Review Protocol

**Purpose:** When James asks Claude to run a prompt file, Claude reviews it first and reports any issues before execution.

---

## Trigger

When James says:
- "run the [filename].md"
- "execute [filename]"
- Any instruction to follow a prompt file

---

## Claude's Response Format

### If prompt is safe to execute:

```
✅ PROMPT READY: [filename]

Summary: [1-2 sentence description]

Executing now...
```

### If prompt has issues:

```
⚠️ PROMPT REVIEW: [filename]

**Issue:** [Brief description]

**Impact:**
- [What would be lost/broken]
- [What would be gained]

**Recommendation:** [Skip / Modify / Execute anyway]

**Awaiting instruction:** Reply with one of:
- "skip" - Don't execute
- "proceed" - Execute as-is despite issues
- "update prompt" - I'll suggest edits to the prompt file first
```

---

## Examples

### Outdated Prompt (like today)
```
⚠️ PROMPT REVIEW: update_from_review_prompt.md

**Issue:** Prompt predates recent work; would overwrite newer content.

**Impact:**
- Would lose: Hard gate docs, reviewing agents table, test dependencies
- Would gain: Nothing (paper file already current)

**Recommendation:** Skip

**Awaiting instruction:** skip / proceed / update prompt
```

### Conflicting Prompt
```
⚠️ PROMPT REVIEW: refactor_auth.md

**Issue:** Conflicts with current branch work on auth system.

**Impact:**
- Would lose: Current uncommitted changes to auth/
- Would gain: Different auth implementation

**Recommendation:** Stash current work first, or skip

**Awaiting instruction:** skip / proceed / update prompt
```

---

## File Location

This protocol file: `claude_prompt_review.md`

Prompt files Claude may be asked to run:
- `claude_review_prompt.md` - Review command instructions
- `update_from_review_prompt.md` - Update from Gemini feedback
- Any future `*_prompt.md` files

---

## Step 4: Gemini Consultation Prompt

When a prompt review finds issues, Claude provides this copy/paste block for James to consult Gemini:

```
---
**Copy/paste this into Gemini CLI:**
---

Claude flagged an issue with `[FILENAME]`

**Issue:** [BRIEF DESCRIPTION]

**What would be lost:**
- [ITEM 1]
- [ITEM 2]

**What would be gained:**
- [ITEM 1 or "Nothing — files already current"]

**Current status:** [BRANCH/STATE INFO]

**Options:**
1. [OPTION 1]
2. [OPTION 2]
3. [OPTION 3]

What's your recommendation?
```

Claude fills in the bracketed values based on the specific situation.

---

**Protocol active.**
