# Lean / Mathlib Version-Cadence Policy

**Status:** policy of record for QBP #489 (Sprint-4 housekeeping, tracking #714); beekeeper direction 2026-06-01
**Applies to:** `proofs/lean-toolchain`, the Mathlib `require … @ "<sha>"` in `proofs/lakefile.lean`, and the (gitignored) `proofs/lake-manifest.json`
**First application:** PR #491 (merged 2026-06-01, `7c95fd4`) — `v4.30.0-rc2` → `v4.30.0` stable; the bump caught one real cross-version breakage at the gate (`qJ_sq`, DoubleSlit.lean:68, `@[scoped simp]` change) — the policy working as designed
**Upstream rule:** `~/Documents/inter/lean-proof-best-practices.md` §12 (toolchain-pin discipline: toolchain / lakefile SHA / manifest in lockstep)

---

## 1. Current state (verified 2026-10-17)

| | Value | Source |
|---|---|---|
| **QBP toolchain pin** | `leanprover/lean4:v4.30.0` (stable) | `proofs/lean-toolchain` |
| **QBP Mathlib pin** | `c5ea00351c28e24afc9f0f84379aa41082b1188f` = Mathlib tag `v4.30.0` | `proofs/lakefile.lean` l.15 |
| **Latest stable Lean** | `v4.35.0` (2026-10-12); `v4.34.1` (2026-09-24) | `gh api repos/leanprover/lean4/releases` |
| **Latest Mathlib stable tag** | `v4.35.0` (`v4.36.0-rc1` is the current RC) | `gh api repos/leanprover-community/mathlib4/git/matching-refs/tags/v4.3` |
| **Drift** | **5 stable minors behind** (4.31, 4.32, 4.33, 4.34, 4.35) | — |
| **PhysLean bridge** | `leanprover/lean4:v4.29.1` | `proofs-physlean-bridge/lean-toolchain` |

The policy's *target* lag is one stable release (§2 P2); the measured lag is five. The next hygiene bump (§4) is **owed** and is the first thing the Toddle drift detector (§6) would flag. It is not done in the housekeeping PR that lands this document — a bump is its own scheduled PR (P3).

---

## 2. Policy (the five rules)

| # | Rule | Why |
|---|---|---|
| **P1** | **Pin to a named STABLE tag.** Never an RC (`v4.30.0-rc2`), never Mathlib `master`/HEAD. The Mathlib SHA in the lakefile is the SHA *of the stable tag*, written out so `lake update` is reproducible across machines. | An RC inherits RC churn without release stability — the riskiest posture (that is what #489 found QBP on). |
| **P2** | **Lag by ~one stable release, deliberately.** Target = latest stable − 1; acceptable band = 1–2 behind. | The community shakes out migration pain first; Mathlib's cache is warm; migration notes exist. Ride the asset ~4 weeks de-risked. |
| **P3** | **A bump is its own scheduled PR — never incidental to feature work.** One PR = one bump. No proof changes in a bump PR except the migration fixes the bump itself forces (tactic-only, math unchanged, each listed in the PR body as #491 did). | A bump folded into a feature PR hides which diff broke what, and lets a migration regression ride a feature review. |
| **P4** | **The bump PR's merge gate IS the zero-sorry rebuild + axiom audit** (§3). | The zero-sorry foundation is itself the regression test for a Mathlib bump; breakage is caught at the gate, not in production. |
| **P5** | **Trigger = capability-pull OR hygiene cadence** (§4). Never chase a release for its own sake. | Bump *toward* a Mathlib advance QBP wants (a Clifford-algebra lemma, octonion/Cayley-Dickson work) — that is the payoff of riding a 772-contributor effort; or bump to avoid drifting past the P2 band. |

Lean's release heartbeat: a stable `v4.N.0` lands roughly monthly (it is the last RC of that line, finalised); `v4.(N+1).0-rc1` follows within days; patch releases (`v4.N.1`, `.2`) appear mid-cycle. Mathlib tags `v4.N.0` the commit that moves onto that toolchain.

---

## 3. The rebuild gate (merge condition for every bump PR)

All four must hold on the PR head; the first two are mechanical (CI), the last two are hand-run until §6 automates them.

| Gate | How it is checked | Owner |
|---|---|---|
| **G1 — `lake build` green, zero errors** | `.github/workflows/lean-foundations.yml` job `lake build (zero errors)` — a **required status check on master since 2026-09-21**. It installs the toolchain from `proofs/lean-toolchain` and fetches the Mathlib cache for the lakefile pin, so it exercises exactly the bumped pair. | CI |
| **G2 — foundations standard unchanged** | Same workflow, job `foundations-standard`: `scripts/check_lean_foundations.py` (no `native_decide`, no vacuous `: True := by trivial`, `sorry`-ratchet against `.lean-gate-baseline.json`) + `scripts/check_layer_imports.py` + its self-test. A bump may not *raise* the baseline. | CI |
| **G3 — `#print axioms` audit unchanged** | For every anchor with `proof_state: verified` / `provenance_kind: proof` + `lean_theorem` in the ledger, `#print axioms <thm>` ⊆ `{propext, Classical.choice, Quot.sound}`. Today hand-run in a scratch file / `lake env lean` (as #491 did for `qJ_sq`, `j_mul_complex`, `coupling_decomposition`), result pasted in the PR body. The workflow carries a NOTE marking where this step is wired when it is automated (#481 AC). A new axiom appearing (e.g. `Lean.ofReduceBool` from a `native_decide` Mathlib pulled in) is BLOCKING. | PR author; confirmed by the Tier-2 reviewer |
| **G4 — PA grades unchanged** | `pa-reconcile` CI (`.github/workflows/pa-reconcile.yml`) recomputes `pa_local`/`pa_effective` from the notary evidence at the pinned SHAs and fails on any diff. A toolchain bump changes the `lean-toolchain` handle the closure report records, but must not change a grade. | CI |

**Sign-off.** A bump PR is a **Tier-2** PR (`docs/workflows/review_tiers.md`): Red Team review + Gemini review, with the G3 axiom-audit output as the required anchored artifact (review-anchoring rule). It is an infra PR, so no theory-headline review object is needed unless a migration fix touches a theorem *statement* (then Tier-3). Merge stays beekeeper-gated like every PR.

---

## 4. Procedure

### 4.1 When to open a bump PR

| Trigger | Action |
|---|---|
| **Capability-pull** — a Mathlib lemma/structure QBP needs exists only past the pin | Open the bump PR first (to latest-stable − 1 or the first stable tag containing the lemma, whichever is later); the feature PR stacks on it. |
| **Hygiene** — QBP is ≥ 2 stable minors behind latest (P2 band breached) | Open a bump PR to latest-stable − 1 at the next sprint boundary (housekeeping-before-sprint gate), **not** mid-sprint. Today: owed (5 behind). |
| **Security / correctness advisory** on the pinned toolchain or Mathlib | Bump immediately to the fixed stable tag regardless of lag. |
| **Patch release** (`v4.N.k`, same minor) | Fold into the next scheduled bump unless it fixes something QBP hits. |

Never: bump because a new release exists; bump to an RC "to get ahead"; bump inside a feature PR.

### 4.2 Steps (one PR, one bump)

```
# 0. Pick the target: a Mathlib STABLE tag vT and its commit SHA
gh api repos/leanprover-community/mathlib4/git/ref/tags/vT --jq .object.sha
#    (if the tag object is annotated, dereference: gh api repos/.../git/tags/<sha> --jq .object.sha)

# 1. Branch — one PR per bump, named for it
git switch -c infra/lean-bump-vT origin/master

# 2. Edit the pin pair IN LOCKSTEP (inter §12)
#    proofs/lean-toolchain   → leanprover/lean4:vT
#    proofs/lakefile.lean    → require mathlib … @ "<sha of tag vT>"  (update the comment too)

# 3. Resolve + fetch (manifest is gitignored; it regenerates from the lakefile)
cd proofs
lake update            # add --keep-toolchain only if lake tries to move lean-toolchain off vT
lake exe cache get     # warm Mathlib .oleans for the new pin

# 4. Full rebuild — zero errors (G1) — and the foundations standard (G2)
lake build
python3 ../scripts/check_lean_foundations.py --dir QBP/Foundations
python3 ../scripts/check_layer_imports.py && python3 ../scripts/test_check_layer_imports.py

# 5. Axiom audit (G3) — every verified / proof anchor's lean_theorem
#    e.g. scratch file importing the modules, then `#print axioms <thm>` per theorem,
#    run with `lake env lean scratch.lean`; paste the output table into the PR body.

# 6. Migration fixes, if the rebuild broke anything: tactic-only, math unchanged,
#    one bullet per site in the PR body (#491 pattern). A fix that needs a statement
#    change is NOT a migration fix — stop, file an issue, the bump waits.

# 7. PR to master: body = target tag + SHA, drift before/after, G1–G4 table,
#    migration-fix list, `#print axioms` output, Tier-2 reviews. Not draft.
```

`lake-manifest.json` is **not committed** (`.gitignore` l.80); the `pa-reconcile` closure derivation copies the running checkout's manifest into its pin worktree and checks it against the lakefile rev (G-L2, `docs/cth/qbp-local-extensions.md` §Anchor fields). A manifest/lakefile mismatch is therefore a refusal there too — a second net under inter §12.

### 4.3 Related pins that move with (or lag) a bump

| Pin | Rule |
|---|---|
| `proofs-physlean-bridge/lean-toolchain` (`v4.29.1`) | PhysLean sets its own toolchain; QBP does not bump it. The differential guard (`scripts/check_physlean_differential.py`) compares JSON outputs, so a QBP↔PhysLean skew is tolerated. Proof-level integration (#486) needs skew ≤ 1 stable; note the skew in every bump PR body. |
| `inter/lean-proof-best-practices.md` §12 | Names the current pin in prose. Still reads `v4.30.0-rc2 / 215c5f44` — stale since #491. A one-line inter-side fix is owed (inter is a separate repo; not edited from QBP). Every bump PR should list the inter line as a follow-up until §12 stops naming a specific SHA. |
| `.lean-gate-baseline.json` | Never raised by a bump. If a bump *lowers* sorry/vacuous counts (a Mathlib lemma closed a stub), ratchet it down in the same PR. |

---

## 5. Rollback

A bump PR is reverted, never patched forward, when any of G1–G4 fails after merge (it should not — the gate runs on the PR head — but a cache or runner skew can hide a failure).

1. `git revert <bump merge sha>` on a branch; this restores `lean-toolchain` + lakefile SHA together (they were one commit — P3 is what makes rollback a single revert).
2. `lake update && lake exe cache get && lake build` locally to confirm the old pin still resolves (Mathlib caches for stable tags persist; a stale-tag cache miss means a from-source build in CI — expect it, do not block on it).
3. PR the revert (Tier-1 — it reinstates a previously green state); the re-attempt is a fresh bump PR that cites the failure.
4. If migration fixes from the bump are wanted independently of the pin (rare), they come back in their own PR after the revert.

A rollback across a `lake-manifest` format change is the one case `lake update` may not restore cleanly; delete `proofs/.lake/` and `proofs/lake-manifest.json` and re-resolve.

---

## 6. How the pending-upgrades guard interacts

`.github/workflows/pending-upgrades.yml` runs `scripts/check_pending_upgrades.py` on **every PR**, reading `docs/foundations/pending-upgrades.md`: a register of deliverables ruled MET-for-now with an upgrade owed once a named unblocking issue closes. It **fails the build when a row's unblocking issue is CLOSED but the row is still `status: pending`** (PATTERN-01: only an un-mergeable state holds a promise).

Interaction with version bumps:

| Situation | Rule |
|---|---|
| A proof is parked with a weaker form **because the pinned Mathlib lacks a lemma** that a later stable has | Add a register row: `upgrade owed = <the stronger form> \| unblocking issue = the bump issue for the tag containing the lemma \| status: pending`. The bump PR closes that issue ⇒ the guard goes red on every PR until the stronger form lands ⇒ the capability-pull is un-skippable. **Keep the row's issue separate from the bump PR itself:** the bump PR must stay a pure bump (P3); the owed proof upgrade is the follow-up PR that resolves the row. |
| A bump PR *itself* has a known follow-up (e.g. the inter §12 line, or a `#print axioms` step to automate) | Register it with its own issue; do not leave it as prose in the PR body. |
| The guard is red because a bump closed an issue someone else's row names | That row's owner applies the owed upgrade; the bump is not reverted for it. |

The guard skips gracefully (exit 0, loud) when `gh` is unauthenticated, so local commits never block on it; CI is authoritative. It therefore never blocks the local steps in §4.2, only the merge.

---

## 7. Phased hardening (Crawl → Toddle → Walk)

Same shape as the CTH schema-propagation discipline (#488).

| Phase | Mechanism | State |
|---|---|---|
| **Crawl (now)** | Manual scheduled bump PR; G1/G2/G4 in CI; G3 hand-run and pasted; pin documented in the lakefile comment + this policy. | **In force** since #491. |
| **Toddle — drift detector (spec, #489 AC4)** | A scheduled workflow (`on: schedule: cron '0 6 * * 1'` weekly + `workflow_dispatch`) that: (1) reads `proofs/lean-toolchain`; (2) lists stable Lean releases via `gh api repos/leanprover/lean4/releases --jq '.[] \| select(.prerelease==false) .tag_name'`; (3) computes the minor-version lag; (4) if lag ≥ 2 (P2 band breached) opens-or-updates ONE issue titled `[infra] Lean/Mathlib drift: vX pinned, vY latest (N behind)` labelled `type: infra, housekeeping` (idempotent: search for the open title first, edit rather than duplicate), and asserts the Mathlib tag for the recommended target (latest − 1) exists; (5) never edits the pin — the bump PR stays human-applied. Also fails (red, not an issue) when `lean-toolchain` names an RC or `lakefile.lean`'s SHA is not a stable-tag SHA (P1 violation detector). Est. cost: one `gh api` page per run, no toolchain install. | Spec'd here; implementation is a follow-up issue. |
| **Walk — bump bot (design note, #489 AC5)** | Akin to Mathlib's own `bump/v4.N.0` branches: on the detector's trigger, a bot opens the branch per §4.2 steps 1–3 (edit pin pair, `lake update`, commit), lets CI run G1/G2/G4, runs the G3 audit as a workflow step (the `#print axioms` step the lean-foundations NOTE reserves) and posts the output as a PR comment; a human reviews a green gate and the beekeeper merges. Design constraints: the bot pushes only to `infra/lean-bump-*` branches; it never force-pushes; it never commits a migration fix (a red G1 means the PR stays open for a human, who is the only one allowed to write proof text); it records the PhysLean skew. Prerequisite: the G3 step automated in Toddle+ (needs the verified-theorem list derivable from the ledger — `scripts/check_anchor_manifest.py` already enumerates `lean_theorem`s). | Design noted; no implementation planned before Walk. |

---

## Change history

| Date | Author | Change |
|---|---|---|
| 2026-10-17 | qbp-implementor (housekeeping seat) | v1.0 — policy written for #489 (AC1, AC3, AC4 spec, AC5 design note); AC2 cited as landed in PR #491; current drift measured (5 behind) and the owed hygiene bump named |
