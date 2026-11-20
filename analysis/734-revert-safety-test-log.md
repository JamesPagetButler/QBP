# #734 — Git revert safety: dummy-branch test log

**Date:** 2026-11-01 (UTC) · **Builder:** forging pilot round 1 (director qbp-oppenheimer) ·
**Worktree `$W`:** `/home/prime/Documents/QBP/.claude/worktrees/734-revert-safety` (branch `process/734-git-revert-safety`) ·
**Clone `$C`:** `<scratchpad>/734-clone` (throwaway, deleted) · **Capacity:** 0 compute, < 1 MB disk.

Delivers AC4 of #734 (the "test revert path on a dummy branch" AC deferred from #383 in PR #456).
Every command below ran as shown; outputs are verbatim except that the two long directory paths
are shortened to `$W` / `$C`, pre-commit hook output is folded to one bracketed line, and the two
commit-message trailer lines (`Co-Authored-By` / `Claude-Session`) are elided from the command echo.

## Reading

The revert path works, and it taught something the first draft of the decision tree did not say.
Three one-line appends to one file (A, B, C) and a `git revert --no-edit` of the middle one **did not
apply cleanly**: because C's line sits directly under B's, git cannot tell B's hunk from C's and
raised a content conflict (`UU analysis/734-dummy/notes.txt`). The resolution was the obvious one —
keep A's and C's lines, `git add`, `git revert --continue` — and the resulting commit `92d2dfc` is a
one-line deletion whose diff against A is exactly "A + C". So: `git revert` is still the right default
on a shared branch, but `--no-edit` is a convenience for the clean case, not a guarantee; when
neighbouring commits touch adjacent lines the reverter resolves by hand, and that is the signal the
decision tree calls "built upon" (if the resolution were not obvious, a forward commit would beat the
revert). Two of git's own guards showed up as well — it refused `git switch` while the revert was in
progress and refused `git branch -D` of the checked-out branch — both of which protect exactly the
mistakes a hurried seat would make. Part 2, in a throwaway clone, shows the forbidden operation: after
`git reset --hard HEAD~1` on a branch pretending to be shared, commit `0bdeec2` and `collab.txt` are
gone from `git log` and the index, visible only in the local **reflog** — which a collaborator who
fetched the branch does not have, and which a push would then overwrite for them. That asymmetry
(revert leaves a forward record everyone sees; reset leaves a private reflog entry) is the whole
reason for the rule. **No branch was pushed at any point.** The throwaway branch
`process/734-dummy-revert-test` was deleted (`was 92d2dfc`), `analysis/734-dummy/` does not exist on
the PR branch, and the clone directory was removed (`exists? no`). Timestamps are UTC, HH:MM:SSZ.

## Part 1 — dummy branch in `$W`: three commits, revert the middle one

```text
== PART 1: dummy-branch revert (in W) ==
[02:45:21Z] $ git -C $W switch -c process/734-dummy-revert-test
Switched to a new branch 'process/734-dummy-revert-test'
    (rc=0)
[02:45:21Z] $ mkdir -p $W/analysis/734-dummy
    (rc=0)
[02:45:21Z] $ git -C $W add analysis/734-dummy/notes.txt
    (rc=0)
[02:45:21Z] $ git -C $W commit -m "[test] #734 dummy A: add notes.txt" (+ the two trailer lines)
    [pre-commit: gitleaks Passed; black/mypy/validate-knowledge/physlean-differential Skipped]
    (rc=0)
[02:45:21Z] $ git -C $W add analysis/734-dummy/notes.txt
    (rc=0)
[02:45:21Z] $ git -C $W commit -m "[test] #734 dummy B: append line 2" (+ the two trailer lines)
    [pre-commit: gitleaks Passed; black/mypy/validate-knowledge/physlean-differential Skipped]
    (rc=0)
[02:45:22Z] $ git -C $W add analysis/734-dummy/notes.txt
    (rc=0)
[02:45:22Z] $ git -C $W commit -m "[test] #734 dummy C: append line 3" (+ the two trailer lines)
    [pre-commit: gitleaks Passed; black/mypy/validate-knowledge/physlean-differential Skipped]
    (rc=0)
[02:45:22Z] $ git -C $W log --oneline -4
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
4e12d7e [test] #734 dummy A: add notes.txt
620993d [process] #734: Git Revert Safety section — tags, revert-vs-reset tree, Oppenheimer-gate checklist, logging format
    (rc=0)
[02:45:22Z] $ cat $W/analysis/734-dummy/notes.txt
line 1 (commit A)
line 2 (commit B — the one we will revert)
line 3 (commit C)
    (rc=0)
[02:45:22Z] middle commit B = 6426cdd
[02:45:22Z] $ git -C $W revert --no-edit 6426cdd
Auto-merging analysis/734-dummy/notes.txt
CONFLICT (content): Merge conflict in analysis/734-dummy/notes.txt
error: could not revert 6426cdd... [test] #734 dummy B: append line 2
hint: After resolving the conflicts, mark them with
hint: "git add/rm <pathspec>", then run
hint: "git revert --continue".
hint: You can instead skip this commit with "git revert --skip".
hint: To abort and get back to the state before "git revert",
hint: run "git revert --abort".
    (rc=1)
[02:45:22Z] $ git -C $W log --oneline -5
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
4e12d7e [test] #734 dummy A: add notes.txt
620993d [process] #734: Git Revert Safety section — tags, revert-vs-reset tree, Oppenheimer-gate checklist, logging format
8d68a09 [spike] qbp-kz-g2 round 3: pre-registration DRAFT r1–r7 + FROZEN-v1 (equilibrium first-order test; sha 132f6a42…) (#800)
    (rc=0)
[02:45:22Z] $ cat $W/analysis/734-dummy/notes.txt
line 1 (commit A)
<<<<<<< HEAD
line 2 (commit B — the one we will revert)
line 3 (commit C)
=======
>>>>>>> parent of 6426cdd ([test] #734 dummy B: append line 2)
    (rc=0)
[02:45:22Z] $ git -C $W status --short
UU analysis/734-dummy/notes.txt
    (rc=0)
[02:45:22Z] $ git -C $W switch process/734-git-revert-safety
fatal: cannot switch branch while reverting
Consider "git revert --quit" or "git worktree add".
    (rc=128)
[02:45:22Z] $ git -C $W branch -D process/734-dummy-revert-test
error: Cannot delete branch 'process/734-dummy-revert-test' checked out at '$W'
    (rc=1)
[02:45:22Z] $ git -C $W branch --list process/734*
* process/734-dummy-revert-test
  process/734-git-revert-safety
    (rc=0)
[02:45:22Z] $ git -C $W log --oneline -2
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
    (rc=0)
[02:45:22Z] $ ls $W/analysis/734-dummy
notes.txt
    (rc=0)
```

## Part 1b — resolve the conflict and finish the revert; return to the PR branch; delete the dummy

```text
== PART 1b: resolve the revert conflict (keep A's and C's lines, drop B's), continue ==
[02:45:44Z] $ printf 'line 1 (commit A)\nline 3 (commit C)\n' > analysis/734-dummy/notes.txt
[02:45:44Z] $ git -C $W add analysis/734-dummy/notes.txt
    (rc=0)
[02:45:44Z] $ env GIT_EDITOR=true git -C $W revert --continue
    [pre-commit: gitleaks Passed; black/mypy/validate-knowledge/physlean-differential Skipped]
[process/734-dummy-revert-test 92d2dfc] Revert "[test] #734 dummy B: append line 2"
 1 file changed, 1 deletion(-)
    (rc=0)
[02:45:44Z] $ git -C $W log --oneline -5
92d2dfc Revert "[test] #734 dummy B: append line 2"
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
4e12d7e [test] #734 dummy A: add notes.txt
620993d [process] #734: Git Revert Safety section — tags, revert-vs-reset tree, Oppenheimer-gate checklist, logging format
    (rc=0)
[02:45:44Z] $ git -C $W show --stat --format=%h %s%n%b HEAD
92d2dfc Revert "[test] #734 dummy B: append line 2"
This reverts commit 6426cddd7b7f1d32f20d1421858cd35d15b0954f.


 analysis/734-dummy/notes.txt | 1 -
 1 file changed, 1 deletion(-)
    (rc=0)
[02:45:44Z] $ cat $W/analysis/734-dummy/notes.txt
line 1 (commit A)
line 3 (commit C)
    (rc=0)
[02:45:44Z] $ git -C $W diff 4e12d7e HEAD -- analysis/734-dummy/notes.txt
diff --git a/analysis/734-dummy/notes.txt b/analysis/734-dummy/notes.txt
index 4b36b99..a213009 100644
--- a/analysis/734-dummy/notes.txt
+++ b/analysis/734-dummy/notes.txt
@@ -1 +1,2 @@
 line 1 (commit A)
+line 3 (commit C)
    (rc=0)
[02:45:44Z] $ git -C $W status --short
    (rc=0)
[02:45:44Z] $ git -C $W switch process/734-git-revert-safety
Switched to branch 'process/734-git-revert-safety'
Your branch is ahead of 'origin/master' by 1 commit.
  (use "git push" to publish your local commits)
    (rc=0)
[02:45:44Z] $ git -C $W branch -D process/734-dummy-revert-test
Deleted branch process/734-dummy-revert-test (was 92d2dfc).
    (rc=0)
[02:45:44Z] $ git -C $W branch -a --list *734*
* process/734-git-revert-safety
    (rc=0)
[02:45:44Z] $ git -C $W log --oneline -2
620993d [process] #734: Git Revert Safety section — tags, revert-vs-reset tree, Oppenheimer-gate checklist, logging format
8d68a09 [spike] qbp-kz-g2 round 3: pre-registration DRAFT r1–r7 + FROZEN-v1 (equilibrium first-order test; sha 132f6a42…) (#800)
    (rc=0)
[02:45:44Z] $ ls $W/analysis/734-dummy
ls: cannot access '$W/analysis/734-dummy': No such file or directory
    (rc=2)
[02:45:44Z] $ git -C $W status --short
    (rc=0)
```

## Part 2 — throwaway CLONE: what `git reset --hard` on a shared branch loses

```text
== PART 2: forbidden reset in a throwaway CLONE ==
[02:45:22Z] $ git clone -q $W $C
    (rc=0)
[02:45:23Z] $ git -C $C switch -c shared/demo
Switched to a new branch 'shared/demo'
    (rc=0)
[02:45:23Z] $ git -C $C add collab.txt
    (rc=0)
[02:45:23Z] $ git -C $C commit -m "[test] #734 clone: collaborator commit X (pretend pushed + fetched by a peer)" (+ the two trailer lines)
    (rc=0)
[02:45:23Z] $ git -C $C log --oneline -3
0bdeec2 [test] #734 clone: collaborator commit X (pretend pushed + fetched by a peer)
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
    (rc=0)
[02:45:23Z] $ git -C $C reset --hard HEAD~1
HEAD is now at 9b47d84 [test] #734 dummy C: append line 3
    (rc=0)
[02:45:24Z] $ git -C $C log --oneline -2
9b47d84 [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
    (rc=0)
[02:45:24Z] $ git -C $C ls-files collab.txt
    (rc=0)
[02:45:24Z] $ git -C $C reflog -n 4
9b47d84 HEAD@{0}: reset: moving to HEAD~1
0bdeec2 HEAD@{1}: commit: [test] #734 clone: collaborator commit X (pretend pushed + fetched by a peer)
9b47d84 HEAD@{2}: checkout: moving from process/734-dummy-revert-test to shared/demo
9b47d84 HEAD@{3}: clone: from $W
    (rc=0)
[02:45:24Z] $ git -C $C log --oneline --all --decorate -3
9b47d84 (HEAD -> shared/demo, origin/process/734-dummy-revert-test, origin/HEAD, process/734-dummy-revert-test) [test] #734 dummy C: append line 3
6426cdd [test] #734 dummy B: append line 2
4e12d7e [test] #734 dummy A: add notes.txt
    (rc=0)
[02:45:24Z] $ rm -rf $C
    (rc=0; exists? no)
[02:45:24Z] $ git -C $W status --short
UU analysis/734-dummy/notes.txt
    (rc=0)
[02:45:24Z] $ git -C $W branch -a --list *734*
* process/734-dummy-revert-test
  process/734-git-revert-safety
    (rc=0)
```

## Statement

- `git revert` executed and validated on a throwaway branch; the revert commit is `92d2dfc` (deleted with its branch).
- `git reset --hard` was executed **only** inside the throwaway clone `$C`, which was `rm -rf`'d; `$W` and every real branch are untouched.
- Nothing was pushed. `git -C $W branch -a --list '*734*'` after the test lists only `process/734-git-revert-safety`.
- Doc consequence: one bullet added under *Revert-vs-reset decision tree* in `docs/workflows/sprint_mode_workflow.md` recording the adjacent-line conflict and git's two refusals.
