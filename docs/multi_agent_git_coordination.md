# Multi-Agent Git Coordination Guide

This document provides mandatory git workflow protocols for Claude and Gemini when working on the QBP repository. Following these rules prevents commits from landing on wrong branches and ensures clean version control history.

---

## The Problem We're Solving

When multiple AI agents work on the same repository, branch confusion can occur:
- Agent A starts work on Branch X
- Agent B creates Branch Y but commits accidentally go to Branch X
- Commits appear in wrong PRs, causing review confusion

**Real Example:** A Lean proof intended for `feat/exp01-phase4-proof-v2` landed on `fix/issue-93-remaining-content`, causing unrelated code to appear in a documentation PR.

---

## Mandatory Pre-Commit Protocol

**EVERY commit must be preceded by branch verification.** No exceptions.

### Step 1: Verify Current Branch

Before ANY git operation that modifies the repository:

```bash
git branch --show-current
```

**Expected:** The branch name you intend to work on.

**If wrong:** STOP. Switch to correct branch before proceeding.

### Step 2: Verify Repository State

```bash
git status
```

Check:
- You're on the intended branch (shown at top)
- No unexpected staged files
- No uncommitted changes that could block branch switching

### Step 3: Only Then Proceed

After verification, proceed with your git operations.

---

## Safe Branch Creation Pattern

The naive `git checkout -b <branch>` fails silently if the branch already exists.

### Safe Pattern

```bash
# Fetch latest from remote
git fetch origin

# Create new branch from master (fails loudly if exists)
git checkout -b new-branch origin/master

# ALWAYS verify the switch worked
git branch --show-current
```

### If Branch Might Already Exist

```bash
# Try to create; if exists, switch to it
git checkout -b new-branch origin/master 2>/dev/null || git checkout new-branch

# ALWAYS verify
git branch --show-current
```

### What NOT to Do

```bash
# DANGEROUS: Silent failure if branch exists
git checkout -b my-feature
git add .
git commit -m "feature"  # May commit to WRONG branch!
```

---

## Pre-Flight Checklist

Copy this checklist into your workflow before every commit:

```
PRE-COMMIT VERIFICATION:
[ ] Ran: git branch --show-current
[ ] Confirmed: On correct branch (<branch-name>)
[ ] Ran: git status
[ ] Confirmed: Only intended files will be committed
[ ] Confirmed: Branch name in status matches expected
```

---

## Agent-Specific Protocols

### Gemini's Git Workflow

Gemini handles implementation work and creates PRs.

1. **Announce intent** at start of work session:
   ```
   "Starting work on Issue #XX. Will use branch: feat/issueXX-description"
   ```

2. **Create branch with full verification:**
   ```bash
   git fetch origin
   git checkout master
   git pull origin master
   git checkout -b feat/issueXX-description
   git branch --show-current  # MUST verify
   ```

3. **Before EVERY commit:**
   ```bash
   git branch --show-current  # Verify still on correct branch
   git status                  # Verify correct files staged
   ```

4. **Include branch name in commit message** as secondary verification:
   ```bash
   git commit -m "feat(proofs): Add formal proof for Experiment 1

   Branch: feat/exp01-phase4-proof
   Closes #55"
   ```

5. **Push with tracking:**
   ```bash
   git push -u origin feat/issueXX-description
   ```

6. **Create PR and STOP:**
   ```bash
   gh pr create --title "..." --body "..."
   ```
   Then wait for review cycle.

### Claude's Git Workflow

Claude handles reviews, scribing, and targeted fixes.

1. **Verify no uncommitted work before switching:**
   ```bash
   git status
   git stash  # If needed
   ```

2. **For fix branches:**
   ```bash
   git fetch origin
   git checkout -b fix/issue-XX-description origin/master
   git branch --show-current  # MUST verify
   ```

3. **Same pre-commit verification as Gemini**

4. **After completing work, verify what will be in PR:**
   ```bash
   git log origin/master..HEAD --oneline
   git diff origin/master..HEAD --stat
   ```

---

## Coordination Between Agents

### Rule 1: One Branch Per Agent at a Time

- Each agent works on ONE branch at a time
- Announce branch ownership in shared conversation
- Do not touch another agent's active branch

### Rule 2: Clear Handoffs

When handing work between agents:

```
"Gemini: I've completed work on feat/X and created PR #YY.
Branch is ready for Claude's Red Team review.
I am now switching to a different branch for my next task."
```

### Rule 3: No Parallel Commits to Same Branch

If both agents need to modify the same files:
1. One agent completes and pushes first
2. Second agent pulls before starting
3. Never have both agents with uncommitted changes on same branch

---

## Recovery Procedures

### Wrong Branch Commit (Not Yet Pushed)

```bash
# Save the commit hash
git log -1 --format="%H"

# Move HEAD back (keeps changes staged)
git reset --soft HEAD~1

# Switch to correct branch
git checkout correct-branch

# Recommit
git commit -m "original message"
```

### Wrong Branch Commit (Already Pushed)

**Do NOT force push.** Instead:

1. Document the issue
2. Cherry-pick to correct branch:
   ```bash
   git checkout correct-branch
   git cherry-pick <commit-hash>
   git push
   ```
3. Revert from wrong branch:
   ```bash
   git checkout wrong-branch
   git revert <commit-hash>
   git push
   ```

### Unsure Which Branch You're On

```bash
# Full status including branch tracking
git status -sb

# See recent commits to confirm context
git log --oneline -5

# See all local branches and which is current
git branch -vv
```

---

## Branch Naming Conventions

| Purpose | Pattern | Example |
|---------|---------|---------|
| New feature | `feat/<issue>-<description>` | `feat/exp01-phase4-proof` |
| Bug fix | `fix/<issue>-<description>` | `fix/issue-93-remaining-content` |
| Documentation | `docs/<description>` | `docs/lean4-setup` |
| Housekeeping | `chore/<description>` | `chore/update-gitignore` |

---

## Audit Trail Requirements

Every PR description must include:

```markdown
## Branch History

- Branch created from: `master` at commit `<hash>`
- Commits in this PR: `<count>`
- Verified branch before each commit: Yes
```

This provides an audit trail for debugging future issues.

---

## Summary

The key rules:

1. **Always verify branch** with `git branch --show-current` before committing
2. **Use safe branch creation** that fails loudly if branch exists
3. **Include branch name in commits** as secondary verification
4. **One branch per agent** at any given time
5. **Announce branch ownership** in shared conversations
6. **Never force push** to recover from errors

Following these protocols ensures clean git history and prevents cross-contamination between PRs.
