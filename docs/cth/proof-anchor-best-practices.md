# CTH Proof-Anchor Best Practices

**Audience:** anyone adding or maintaining a `provenance_kind:proof` anchor in the CTH ledger
(`archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json`). **Status:** the standing process,
post-FAULT-S4-005 / S4-007. **Why it exists:** the ledger drifted from the proof corpus in *both*
directions — 21 anchors claimed proofs that didn't exist, ~100 clean proofs existed that no anchor
claimed — because the old enforcement was a *ratchet* (tolerate a frozen count) not a *gate* (assert the
claim). This document is how you keep it from happening again. Analysis: `docs/rca/cth-proof-evidence-process-2026-09-02.md`.

---

## The one rule

> **If you claim it's proven, you must submit the evidence that it's proven — in the same change.**
> "Proven" is not a label you write; it is a property the gate re-derives. A resolving file, a matching
> name, or a hand-typed `verified` are **not** evidence. The evidence is a clean toolchain audit.

---

## What "proven" means — the evidence bar (enforced by C3-FULL)

A `provenance_kind:proof` anchor must carry **all** of:

| Field | Requirement |
|---|---|
| `proof_state` | `"verified"` |
| `proof_file` | resolves on `master` **and** the source is hole-free (see per-language table) |
| `verification.axiom_closure` | **clean for the language** (below) |
| `sorry_count` | `0` |

Miss any one → the gate hard-fails (`scripts/check_anchor_manifest.py`, CI job *Inverse Anchor Audit*).

### Per-language: what counts as a hole, and what counts as clean

| System | Reads as UNPROVEN — never ship these | Authoritative audit | Clean bar |
|---|---|---|---|
| **Lean 4** | `sorry`, `admit`, `sorryAx`, **`native_decide`** (compiler-trusted, not kernel-clean) | `#print axioms <thm>` | closure ⊆ `{propext, Classical.choice, Quot.sound}` |
| **Agda** | `postulate`, `{! !}` holes, unsolved metas, `TERMINATING`/`NON_TERMINATING` | build under `--safe` | `--safe` typechecks (postulate-free, total, no `primTrustMe`/`REWRITE`) |
| **Coq** | `Admitted`, `admit`, `Axiom` (unwhitelisted) | `Print Assumptions` | closed under accepted axioms only |

> `native_decide` is a proof *smell*, not a proof: it trusts the compiler (`Lean.ofReduceBool`), so it is
> **not** axiom-clean. Migrate to kernel `decide` before claiming `proof`.

---

## Adding a proof anchor — the checklist

1. **Write and verify the proof.** Capture the audit verbatim: `#print axioms <thm>` (Lean) or the `--safe`
   build result (Agda). This capture *is* the evidence — keep it.
2. **Anchor it** with `proof_state:verified`, the real `proof_file`, `sorry_count:0`, and
   `verification.axiom_closure` = the captured closure. Fill `lean_theorem` / `lean_companion_theorems`
   with the witness names.
3. **Never** set `provenance_kind:proof` on something not yet verified. If the result is analytic/sympy/
   modeling, use `derivation` or `theory` — that is honest, not lesser. It can earn `proof` later.
4. Run `python3 scripts/check_anchor_manifest.py` locally — it must pass before you push.
5. If you edited the schema/gate, add an **adversarial test** (plant a bad claim, assert it's caught) —
   see `scripts/test_check_anchor_manifest.py`. A gate is validated by what it *catches*, not by green.

---

## The two directions — both are ledger-integrity failures

| Direction | Failure | Gate | Legacy debt |
|---|---|---|---|
| **Over-claim** | anchor says proven, no/weak evidence | C3-FULL evidence bar (absolute, whole-ledger) | register (below), #617/#615/#613 |
| **Under-claim** | a clean proof exists, no anchor claims it ("orphan" / lost work) | orphan audit (being converted to an absolute manifest gate — #619) | ~100 result orphans, #619 |

Anchoring an orphan is *recovering* proven work into the ledger — low-risk, because the proof is already
clean, so a correct new anchor clears the evidence bar immediately.

---

## Legacy debt: the remediation register (not a baseline)

`docs/cth/proof-anchor-remediation.json` holds the known pre-existing over-claims. It is **shrink-only**:

- An entry leaves **only** by the anchor meeting the evidence bar (proved) or being reclassified (honest).
- The gate hard-fails if a **new** over-claim appears off-register, if a listed entry now *passes* (stale —
  remove it), or if any entry lacks a tracking issue.
- Adding an entry is a **visible, reviewed commit** — never a silent count-bump.

This is the difference between a register and the ratchet it replaced: `anchor_side_phantoms: 16` hid
sixteen unnamed over-claims behind one bump-able number; the register names every one, links each to an
issue, and can only shrink.

### Resolving a register item (the 1×1 discipline)

For each item: **prove-if-possible, else reclassify.** Supply the verified + axiom-clean proof and remove
the entry, **or** change `provenance_kind: proof → derivation|theory` and remove the entry. "I made the
file resolve" is **not** resolution — the C3-FULL bar will still fail it. Done = the evidence is attached.

---

## The principle behind all of it (so new gates don't repeat the mistake)

> **PATTERN-02 — never gate a truth-claim with a ratchet.** A ratchet ("no worse than a frozen baseline of
> our past state") can only forbid regression; it structurally cannot assert correctness, and on a corpus
> that already holds debt it *encodes that debt as acceptable*. For any check that a claim is **true**, the
> acceptance criterion must be **absolute** (test the property), cover the **whole population** (never a
> subset), re-derive the property where feasible (not trust a claimed value), and hold tolerated debt only
> in an **itemised, issue-linked, shrink-only register**. When "proven" strengthens, **re-audit the whole
> ledger** against the new bar in the same change — never grandfather silently. A gate is judged by what it
> **catches**, not by whether CI is green.

**Audit on change, not on a clock:** the full-ledger audit path-triggers on the CTH ledger, `proofs/**`,
and the audit tooling — a proof edit re-triggers it even when the ledger bytes are untouched, because a
proof edit can invalidate a claim.

---

## The gates, and where they live

| Gate | Enforces | File |
|---|---|---|
| C1/C2 | a declared anchor-worthy deliverable must be anchored (manifest, not `grep theorem`) | `check_anchor_manifest.py` + `anchor-worthy-manifest.json` |
| C3 | a declared anchor's witnesses resolve in source | `check_anchor_manifest.py` |
| C3-FULL | **every** proof anchor carries its evidence (the bar above) | `check_anchor_manifest.py` + `proof-anchor-remediation.json` |
| orphan audit | under-claim direction (→ absolute gate, #619) | `anchor_inverse_audit.py` |
| airtight (planned) | re-run `#print axioms`/`--safe`, diff vs the claimed closure | foundations CI, #618 |
| Tier-3 review | a real reviewer comment (not the PR body) before a theory merge | `tier-3-review-gate.yml` |

All run in CI on any change to the ledger, proofs, or tooling.
