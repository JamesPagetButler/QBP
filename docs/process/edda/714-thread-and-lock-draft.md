<!-- Provenance: copied verbatim 2026-10-24 from the qbp-implementor session scratchpad draft (714-edda-thread.md) for QBP#714; the compilable subset (§B1) is also the file ./qbp_housekeeping_sprint4_gate.edda; §B2 is pseudo-spec, §(c) = 8 questions for edda-implementor (bragi); see inter#197. -->

# QBP#714 as a thread, in federation ontology v0.5.0 language, with an Edda lock DRAFT

Sources: `inter` ontology v0.5.0 (`6e83b72:ontology/ontology.yaml`), forging doc (`origin/main:best-practices/forging-spikes-strikes-executable-specs.md`), inter#194 (Sprint 4 weave; QBP row = "Housekeeping burn-down | QBP#714 | lock: —"), inter#196 (AC manifest spike: Q1 manifest shape, D1 ruled), inter#197 (forging → Edda lowering table), Edda Main @9d571a5 (`edda-language-theory-v0.3.md`, `internal/stage0|stage1`, `cmd/edda-stage-1`).

DRAFT for edda-implementor review; the bucket tables on #714 remain the operational record.

## (a) Glossary — the QBP housekeeping window on the ontology

| Term (ontology id, status) | Maps to, in this window | Ontology quote (first sentence of `definition`) |
|---|---|---|
| **warp** (`fed:warp`, derived) | QBP's own lengthwise progression on `JamesPagetButler/QBP` (spec, backlog, roadmap), tended by **qbp-oppenheimer** as its write axis; qbp-implementor writes on it only under the inter#162 interim grant (a crossing, not a second warp). | "A repo's own lengthwise progression (spec, backlog, roadmap). A seat tends exactly one warp, its write axis (Seat Charter R1)." |
| **weft** (alias of `fed:thread`; no separate entry) | Not a second concept. #714 is a *warp thread* (one repo); where it touches inter (#735) or reads sibling repos (#738/#761) those are crossings. | "'Weft' is this same concept named for its cross-repo orientation (weft ≡ thread)." |
| **thread** (`fed:thread`, derived; v0.5.0 note: "the ACTIVE STATE of a spec-driven path toward a lock") | The window #714 defines: **`qbp-housekeeping-sprint4-gate`**. Intent + per-issue spec-deltas are spelled out in #714's bucket tables; it converts into strikes as each issue's executable spec (its AC legs) is defined. DESIGN-PROPOSAL: a DIAGRAM in the federation category. | "The ephemeral, parallel conceptual-development unit within a sprint, where intent, theory and per-repo spec-deltas are spelled out and where spikes run; converts into one or more strikes once its executable specification is fully defined." |
| **thread path** (`fed:thread-path`, design-proposal) | The ordered route to the lock: **A (14 closes) ∥ B (14 strikes) → C (10 gated-lane strikes) → D (20 reconciled by the beekeeper) → 🔒**. DESIGN-PROPOSAL: a composable chain of morphisms (strikes) ending at the lock. | "The spec-driven, ordered route of strikes a thread takes to its lock: the thread's proof plan." |
| **strike** (`fed:strike`, derived) | Each housekeeping issue's PR landing on `master` under the gate (or its evidence comment, for no-PR items). Exit is **its AC legs green**, not the merge (Governing Principle 2). | "One retained increment of forging. Entry: its executable specification is fully defined. Exit (lands): that executable specification is green, not when its build merges." |
| **spike** (`fed:spike`, derived) | **#734** (forging pilot: Git Revert Safety block) is this thread's spike: time-boxed, disposable, output = a capability-gap list for the revert workflow. inter#196 is the federation spike whose Q1/Q2 output this lock consumes. | "A time-boxed, disposable probe that answers an explicit question and outputs a capability-gap list; runs in the thread phase, before a strike is defined." |
| **lock** (`fed:lock`, design-proposal) | **#714's executable spec**: LEGS = every AC id of every bucket-A/B issue (D1 ruled, inter#196); the lock's own assertions are stated at the external interface (below). Criteria content-addressed; loosening needs a beekeeper witness. DESIGN-PROPOSAL: a TYPE. | "The executable specification a thread must open. Its LEGS are every AC of every issue on the thread; a lock is green only when every leg is discharged and its own assertions pass." |
| **meta-lock** (`fed:meta-lock`, derived) | Not needed: #714 is repo-local. The one cross-repo strike (#735, inter PR) lands on inter's own lock; it is listed here as a crossing, not aggregated. | "The aggregate of a cross-repo strike's per-repo locks; it IS that strike's executable specification, not a separate gate." |
| **forging** (`fed:forging`, derived) | The method the window follows: retained, risk-ordered strikes (A before B before C), each advancing only when its spec is green. | "The method: a chain of retained, risk-ordered strikes that de-risks and builds a capability; repo-agnostic." |
| **forging product** (`fed:forging-product`, design-proposal) | **QBP-at-Sprint-4-kickoff**: a `master` with `housekeeping` open-count 0 (or beekeeper-moved), plus the process tooling the strikes leave behind (#753 closing-keyword guard, #738/#761 xref linter, #737 paths filter, #757 job names). DESIGN-PROPOSAL: the TERM that inhabits the lock's type. | "What a forging produces: a typed package with a manifest of its interfaces, MANY traits and MANY characteristics, a bill of materials, and provenance, proven by its lock at the external interface." |
| **interface** (`fed:interface`, design-proposal) | The product's typed external boundary = what consumers (herschel's R4 check, the kickoff gate) read: GitHub API `issues?labels=housekeeping&state=open`, PR `mergeStateStatus`, check-runs at head, the #714 body. | "The forging product's typed external boundary: its inputs, outputs and config schema, verified by type checks." |
| **trait** (`fed:trait`, design-proposal) | Promises at that interface: **FailClosed** (#674 gating, #753 guard), **NothingRelabelled** (count shrinks only by evidence or the beekeeper's hand), **AuthorNotMerger** (oppenheimer ↔ implementor cross-merge), **Tier3Excluded**. | "A behavioral promise stated at an interface: what consumers may rely on (for example Lossless, FailClosed, DryRunDefault)." |
| **characteristic** (`fed:characteristic`, design-proposal) | Measured values with evidence: open-housekeeping count (58 → 0), CI check count at head (e.g. #759: 18 pass), mutants killed (#738: 3/3), PA grades on ledger items. | "A property of the forging product itself: internal configuration or a measured attribute, carried with a value, a unit and evidence." |
| **standing crossing** (`fed:standing-crossing`, derived) | The implementor-grant lane (qbp-implementor → QBP under the inter#162 interim) and #761's read-only sibling checkouts (Contextus, BMA): each carries a **handle** (pinned sha + artifact tie), not the upstream justification. | "A persistent crossing: a consumption seam where one warp continuously consumes another's output. Its lock is a handle (grade + pinned source sha + artifact tie)." |
| **Capability** (`fed:Capability`, derived; RULED 2026-10-22) | The **AUTO-MODE grant** = tool (`gh pr merge`) + authority (the beekeeper-written `AUTO-MODE: ON` line on #714 = Edda `Cap`) + capacity (scope label `housekeeping`, target `master`, from-date). Bare `gh` is not the capability. | "A capability is a tool plus the authority to use it plus an allocated capacity, bound together at instantiation." |
| **type / category** (`math:type`, `math:category`, derived; DESIGN-PROPOSAL mappings) | Lock = TYPE; product = TERM inhabiting it ("a green lock is then a witness that the product has that type"); thread = DIAGRAM; thread path = composable chain of strikes. Objects/morphisms of the federation category are "not yet defined anywhere on the record". | `math:type`: "A term INHABITS its type; under propositions-as-types, a proof is a term of the proposition it proves." |

## (b) Edda lock DRAFT — thread `qbp-housekeeping-sprint4-gate`

**What is real and what is guessed.** Edda today (Main @9d571a5, `cmd/edda-stage-1 check`) parses `module`, `contract { tier, requires: cap(...), body }`, `skill { vessel, node, op : tails/heads/transit/control/mechanism }`, `edge`, and the proof-state verbs `open / settle … as / exercise … with`. It has **no** `lock`, `legs`, `where{}`, `pre`/`post`/`seam`, or `requires: cth:` form: `lock { invariants: [...] }` is theory v0.3 §3.4 only (not in the parser); `where{}`/`pre`/`post`/`seam`/`cth:` are the unreviewed RFC-EDDA-2026-03 proposals listed in inter#197 as "proposed". Per Edda v0.3 B2/B3 ("every quantity that weights an admission … is substrate-witnessed and derived, never producer-declared") a *runtime* `cth:` query in a lock is the wrong layer; evidence below is **pinned and witnessed** (PR → merge sha on master, comment URL, ruling URL), which is what the inter#196 Q1 checker already resolves.

### B1. Real Edda (type-checks: `edda-stage-1 check` → `ok … 1 contract(s), 1 skill(s)`; negative probe exercise-before-settle → `EDDA-AUTH-018`, exit 1)

```edda
-- QBP#714 thread `qbp-housekeeping-sprint4-gate` — the thread PATH as an Edda skill
-- (inter#197 lowering row: thread / thread path -> `skill`, a scoped hypergraph of `op`s)
-- and the strike-exit grant-gate as an Edda contract (theory v0.3 §4.13: exercisable
-- authority = hold grant ∧ step witnessed-settled). Real stage-1 syntax (edda Main 9d571a5).
module qbp.housekeeping.sprint4_gate

skill qbp_housekeeping_sprint4_gate {
    -- the warp this thread runs on: QBP master is the embodiment vessel
    vessel qbp_master
    node qbp_master : Vessel
    -- one node per #714 bucket; quantities = open housekeeping issues at the 2026-10-24 read
    node bucket_a : Vessel
    node bucket_b : Vessel
    node bucket_c : Vessel
    node bucket_d : Vessel
    node discharged : Vessel
    -- control = the pr-merge-completeness gate; mechanisms = the lanes
    node gate : Junction
    node oppenheimer : Junction
    node implementor : Junction
    node beekeeper : Junction
    -- strikes (E4 mass-balance: issues in == issues discharged, nothing relabelled away)
    op close_a     : tails { bucket_a: 14 } heads { discharged: 14 } control { gate } mechanism { beekeeper }
    op strike_b    : tails { bucket_b: 14 } heads { discharged: 14 } control { gate } mechanism { oppenheimer, implementor }
    op lane_c      : tails { bucket_c: 10 } heads { discharged: 10 } control { gate } mechanism { implementor }
    op reconcile_d : tails { bucket_d: 20 } heads { discharged: 20 } control { gate } mechanism { beekeeper }
    -- the lock at the end of the thread path: 58 discharged -> the Sprint-4-ready warp
    op unlock_714  : tails { discharged: 58 } heads { qbp_master: 58 } control { gate } mechanism { beekeeper }
}

-- the strike-exit gate for ONE strike: a leg is opened, settled (witnessed), and only then
-- may the auto-mode merge capability be exercised. Exercise-before-settle is EDDA-AUTH-018.
contract strike_exit {
    tier: C
    requires: cap(merge_housekeeping, scope = qbp.master)
    body: {
        open leg
        settle leg as leg_witness
        exercise merge_housekeeping with leg_witness
    }
}
```

Reading: the E4 mass-balance **is** the "nothing relabelled or closed to shrink the count" rule (58 in, 58 discharged; a bucket-D item the beekeeper moves out is still a `reconcile_d` head, witnessed by his comment). The `strike_exit` contract is the auto-mode rule: the merge cap (`AUTO-MODE: ON`) is held, but non-exercisable until the strike's leg is a witnessed `Step[settled]`.

### B2. Edda-SHAPED pseudo-spec (GUESSED forms: `lock`, `legs`, `where{}`, `unlock`, `scope`, `evidence`)

```edda-pseudo
-- GUESSED: `lock { invariants }` is theory v0.3 §3.4 (not parsed); `legs`, `where{}`, `unlock`,
-- `scope`, `evidence` are invented here and are the asks to edda-implementor in (c).
lock qbp_housekeeping_sprint4_gate {
    thread:   "QBP#714"                       -- fed:thread; inter#194 QBP row
    warp:     JamesPagetButler/QBP @ master   -- fed:warp
    product:  qbp_at_sprint4_kickoff          -- fed:forging-product (the term)

    -- LEGS (D1 ruled, inter#196): every AC id of every bucket-A/B issue. Ids are positional
    -- over the issue body's checkbox lines (`#<issue>-AC<n>`), because 21 of 28 bodies use
    -- unnumbered `**AC:**` or bare boxes; where a body numbers its ACs the number is kept.
    legs: [
      -- Bucket A (60 legs; evidence = beekeeper close + the cited merged PR / evidence comment)
      #341-AC1..AC9  evidence: comment("Evidence for close", 2026-10-17) + PR#363@master,
      #385-AC1..AC3  evidence: comment(2026-10-17),
      #390-AC1..AC4  evidence: comment(2026-10-17) + PR#511, PR#534 @master,
      #457-AC1..AC5  evidence: comment(2026-10-17) + PR#458@master,
      #462-AC1..AC7  evidence: 6 ticked; AC6 = beekeeper RULING (nil, rides #494 LOOSE | keep),
      #466-AC1..AC9  evidence: comment(2026-10-17) + PR#585@master (item 3 -> #587),
      #488-AC1..AC5  evidence: PR#569@master + RULING (Crawl-complete | Toddle tracker),
      #494-AC1..AC2  evidence: ticked + comment(2026-10-22),
      #516-AC1..AC2  evidence: comment(2026-10-17) + probe PR#715 (1 fail = AC2 proven; close, not merge),
      #538-AC1..AC3  evidence: 2 ticked; AC3(stretch) = RULING (nil | add lint),
      #552-AC1..AC2  evidence: ticked; follow-on notifier gap -> separate issue,
      #576-AC1..AC4  evidence: comment(2026-10-17) `agda --version`,
      #577-AC1..AC3  evidence: comment(2026-10-17),
      #605-AC1..AC2  evidence: ticked + PR#728 merged @ <sha on master>,
      -- Bucket B (83 legs; evidence = merged PR @ master sha, or evidence comment, or ruling)
      #396-AC1..AC4  evidence: comment(2026-10-18) local-only,
      #507-AC1..AC17 evidence: PR#731 (PR A) @ <sha>; PR B legs wait on RULING §7 advisory|blocking,
      #543-AC1..AC5  evidence: PR#720@master; AC3 tick with evidence; AC5 nil -> #753,
      #674-AC1..AC2  evidence: AC1 = beekeeper RULING fail-closed y/n; AC2 = one PR if yes,
      #683-AC1..AC14 evidence: PR#733@master (docs part) + implementor ledger PRs + RULING (bridging rfl),
      #734-AC1..AC7  evidence: sizing record w/ deming + sprint_mode_workflow.md PR + revert-test log,
      #735-AC1..AC5  evidence: lean-prover.md PR + inter best-practices PR (crossing: inter's lock),
      #736-AC1..AC4  evidence: docs PR,
      #737-AC1..AC4  evidence: ticked + PR#740 @ <sha>,
      #738-AC1..AC4  evidence: PR#759 @ <sha>; AC3 = beekeeper repo-admin action (required check),
      #753-AC1..AC4  evidence: ticked + PR#760 @ <sha>,
      #755-AC1..AC6  evidence: proof module PR + CTH anchor (implementor side) + Tier-3 review record,
      #757-AC1..AC3  evidence: jobs PR + lint + one observed PR,
      #761-AC1..AC4  evidence: tenancy-xref-lint.yml PR after #759 lands
    ]
    -- Bucket C (10 issues) and D (20 issues) are on the thread but their legs enter only once
    -- the beekeeper's reconcile says "stays in gate" (D) / the ruling unblocks them (C).

    -- Evidence forms (pinned, witnessed; no runtime cth: queries — Edda v0.3 B2/B3):
    --   merged_pr(N) @ sha  : PR -> merge commit ON MASTER (follow the squash, inter#196 G4)
    --   comment(url)        : an evidence comment on the issue, by the lane owner
    --   ruling(url)         : a beekeeper comment (bucket-D reconcile; the rulings-owed list)

    -- Gate contracts: every strike's merge must satisfy all of these at its head sha.
    where {
        ci_green(pr)        := all check-runs at pr.headRefOid == success
        reviews_signed(pr)  := every named reviewer has a WRITTEN §I4 / APPROVE, or a linked written deferral
        boxes_closed(pr)    := no `- [ ]` merge-blocking box in pr.body (check_closing_acs.py predicate)
        clean(pr)           := pr.mergeStateStatus == CLEAN
        author_ne_merger(pr):= pr.author != merger   -- oppenheimer <-> implementor cross-merge
        in_scope(pr)        := `housekeeping` in pr.labels ∧ pr.baseRefName == master ∧ pr.tier != 3
    }

    -- The lock's OWN assertions, at the external interface (lock-scope rule):
    invariants: [
        gh api 'repos/JamesPagetButler/QBP/issues?labels=housekeeping&state=open' | length == 0
            -- or == |{items the beekeeper moved out by his own hand, each with ruling(url)}|,
        every leg in legs is settled with a resolvable evidence handle,
        no bucket-A/B issue was relabelled or closed without evidence (E4 balance above),
        #714 body carries the beekeeper's bucket-D reconcile comment URL
    ]

    -- Unlock:
    unlock := (∀ leg ∈ legs: settled(leg)) ∧ ruling(bucket_D_reconcile) recorded ∧ invariants green
    -- Loosening any criterion above needs a beekeeper-witnessed cap (content-addressed criteria).

    -- Scope of the auto-mode grant (fed:Capability = tool + authority + capacity):
    scope {
        tool:      gh pr merge
        authority: the beekeeper-written line `AUTO-MODE: ON — scope: housekeeping; target: master; from: <date>` on #714
        capacity:  label `housekeeping`; base master; theory-bearing Tier-3 PRs EXCLUDED;
                   merger := the lane the author is NOT in (qbp-oppenheimer <-> qbp-implementor);
                   `gh pr merge` on anything else stays per-action beekeeper confirmation
    }
}
```

## (c) Open questions for edda-implementor (bragi)

1. **Lock as a surface form.** Theory v0.3 §3.4 has `lock { invariants, annotation }` and `key : Key.For(lock)` but the stage-1 parser has no `lock` keyword. Is the §3.4 form the intended home for a forging lock, or should a lock lower to a `contract` as inter#197's table says (`contract` with `pre/post`)? Which one do I target?
2. **Legs.** Edda has no construct for "a set of externally-settled obligations" (`#466-AC3` etc.). Does a leg lower to `open`/`settle` per AC inside one contract body, and if so can a contract body hold ~143 open/settle pairs and one `exercise` that requires ALL witnesses (today `exercise g with s` takes one witness)? Or do legs stay in the YAML manifest (inter#196 Q1) with Edda referencing the manifest's witness hash?
3. **`where{}` / `pre` / `post` / `seam`.** The RFC grammar is unreviewed (inter#197 says "proposed"). Is any of it heading into stage-1b, or should gate contracts be written as `op control { gate }` junctions as in B1?
4. **Evidence handles.** How does a settled step name its evidence? Is `settle leg as w` meant to carry a provenance payload (PR merge sha, comment URL) under §11 witnessed provenance, or is that the inter#168 handle's job outside the language?
5. **`requires: cth:`.** inter#197 lists it as proposed; v0.3 B3 says admission weights are witnessed, never declared. Confirm that a lock must NOT query CTH at runtime and that the right form is a pinned PA-record / handle. If so, the RFC row should be marked rejected in the lowering table.
6. **Capability triple.** Is `requires: cap(merge_housekeeping, scope = qbp.master)` the right spelling of the AUTO-MODE grant, and where does its *capacity* (label/base/from-date, Tier-3 exclusion) go, given `[budget: …]` on skills is also only proposed?
7. **Stable AC ids.** 21 of 28 bucket-A/B bodies use unnumbered `**AC:**` or bare `- [ ]` boxes, so leg ids here are positional. inter#196 Q1 wants stable ids; does Edda want them as identifiers (`leg_466_ac3`) or strings? This also answers qbp-architecture's Q2 question to qbp-implementor about the `- [ ] **AC` parser.
8. **E4 as the anti-relabel rule.** Is reading mass-balance (58 in == 58 discharged) as "nothing relabelled or closed to shrink the count" a legitimate use of conservation, or an abuse of the construct?

Checker used: `go run ./cmd/edda-stage-1 check <file>` on an `origin/Main` snapshot (9d571a5) extracted to the scratchpad; builds and runs in seconds; `anatomy` verb shows the ICOM projection of the skill.
