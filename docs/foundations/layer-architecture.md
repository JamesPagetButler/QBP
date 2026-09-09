# QBP Layer Architecture: Substrate / Foundations / Physics

**Status:** RATIFIED by beekeeper 2026-06-04 ("no changes, assemble the PR").
**Provenance:** unanimous Q4 ruling of the CONJ-crystallisation deliberation and
the O2 structured debate (both theory teams, independent argument lines):
*"Physics instantiates the algebra; it does not redefine it."*
**Gate:** PATTERN-01 lesson — rules without mechanical gates get bypassed; this
architecture ships with an import linter (see §5).

## 1. Three layers, three namespaces, one aggregator root each

```
proofs/QBP/
├── Foundations.lean        ← aggregator root (single build/gate target)
│   └── Foundations/        namespace QBP.Foundations — the tower: numbers + operations
├── Physics.lean            ← aggregator root (follow-up; see §6)
│   └── Physics/            namespace QBP.Physics — predictions
│       Cosmo/  Experiments/  Optics/  Oracle/  Units/
├── Substrate.lean          ← aggregator root (since 2026-09-07)
│   └── Substrate/          namespace QBP.Substrate — the hosting definition ONLY
                            (beekeeper lift 2026-09-07, #473 issuecomment-5574256922:
                            AC1-hosting scope; every file states what it HOSTS and
                            what it does NOT DERIVE and cites the lift — enforced by
                            scripts/check_layer_imports.py rule 4; still no sorried
                            scaffolding — the #471 lesson stands)
```

| Layer | Contents | Ground truth |
|---|---|---|
| Foundations | Cayley-Dickson construction, per-level algebras, operations-complete matrix, subalgebra counts, zero-divisor witnesses | Lean kernel |
| Physics | thresholds (M_seed, ladder), crystallisation regimes, experiment formalizations, oracle | Experiment |
| Substrate | the hosting definition (#639): state sphere, potential, universes vs in-flight region, a universe's hosted quaternion algebra — hosts the tower, does not derive it (job A closed: KILLED-locale-forcing-route) | Lean kernel (Hosting.lean, on top of Foundations/CrystalHosting) |

One aggregator per layer ⇒ one `lake build` target and one CI gate surface per
layer. This also closes the build-invisibility gap (#481 residual): a layer file
not imported by its aggregator fails the aggregator-completeness check.

## 2. The import DAG

| Layer | May import | Must NEVER import |
|---|---|---|
| Foundations | Mathlib only | Physics, Substrate |
| Physics | Foundations, Mathlib | Substrate (until a bridge is ratified) |
| Substrate (future) | Foundations, Mathlib | Physics (except via ratified bridge files) |

**The counterintuitive rule:** conceptually the substrate is the onion around
everything, but in the import DAG it sits at the TOP, not the bottom. Substrate
files *import* Foundations and prove enrichment statements ("the tower, placed in
condensed/locale context, gains property X"). The conceptual nesting and the
dependency arrow point in opposite directions — deliberately. If Foundations
imported Substrate, napkin-level mathematics would become load-bearing under every
kernel-checked theorem. The algebra must build standalone, forever.

## 3. The Foundations → Physics interface contract

1. Physics consumes Foundations theorems **by name** (e.g.
   `alternative_hyperplane_count_eq_eight`, `crossing_pass_iff_discriminator`). Physics never
   states an `axiom` about a foundation object — any algebraic fact it needs is
   proven in Foundations first, then cited (the claim→lemma map).
2. Foundations never mentions energy, mass, time, temperature, or crystallisation
   in **types or theorem statements**. Physics gestures are allowed in
   doc-comments only.
3. Boundary rule of thumb settled by (2): `ln 7` as combinatorics (selection
   count) is Foundations; `M_seed` (the S_BH bridge to mass) is Physics.
   (`FanoChoiceInformation` splits accordingly when next touched.)
4. **Truth-in-labelling (no name-smuggling):** Foundations identifiers (defs,
   theorems) must state exactly what the kernel proves. Cited-but-unproved
   classifications (e.g. Hurwitz/Zorn "alternative + 8-dim + positive norm ⟹ 𝕆")
   may appear in docstrings WITH the explicit "cited, not proved in Lean" caveat,
   but never in identifiers — a name is an interface, and an unproven claim in a
   name crosses the Foundations→Physics boundary with credibility it hasn't
   earned. (Added per PR #497 Tier-3 Gemini review, finding G2.)

## 4. Crystallisation is configuration, not conditional mathematics

The mathematics does not melt. The tower is proven **level-complete and
unconditional** — every rung, every operation, every counterexample, always.
"The tower is defined down to level n" is a *physics statement about which rungs
are physically instantiated*, carried physics-side as data:

```lean
-- QBP/Physics (only when a physics theorem first needs it — no scaffolding ahead)
structure CrystallisationRegime where
  level     : ℕ        -- which rung is frozen
  threshold : ℝ        -- decrystallisation scale (compactness, per the O1 ladder)
  selection : ...      -- which subalgebra copy (Fano choice / one of the 8 / ...)
```

Consequences: (a) CONJ-crystallisation-energy-level-equilibrium can die without a
single Foundations file changing; (b) `CrystallisationRegime` is introduced only
on first genuine use, per its NASCENT status.

## 5. Mechanical enforcement

`scripts/check_layer_imports.py` (wired into the lean-foundations workflow):
- FAIL if any file under `Foundations/` imports `QBP.Physics` or `QBP.Substrate`.
- FAIL if any Physics-layer file imports `QBP.Substrate`.
- FAIL if a `.lean` file under `Foundations/` or `Substrate/` is not reachable
  from its aggregator root (build-invisibility check), unless listed in the
  explicit quarantine table inside the aggregator file with a tracking issue.
- FAIL if a `.lean` file under a **physics dir** (`Experiments/`, `Optics/`,
  `Cosmo/`, `Oracle/`, `Units/`, …) or the **Sprint12 corpus**
  (`Sprint12-Inherited/`) is **build-invisible** — reachable from no
  `@[default_target]` root (the `QBP` lean_lib root and the Sprint12 lib roots).
  "Visible" means *CI compiles it*: CI runs bare `lake build`, which builds only
  the `@[default_target]`s, so a file reachable only via a **non-default** target
  (a `lean_exe`) is invisible to CI too and is not treated as visible (that corpus
  is tracked in #646). These dirs have no single per-dir aggregator (files are
  wired straight into `QBP.lean`, `Cosmo` has its own aggregator, `Oracle`/`Units`
  files hang off `lean_exe` roots, Sprint12 files are each a lib root), so the
  check uses the REAL import graph (default-target roots + transitive closure)
  rather than one aggregator file. This closes the gap that let
  `Experiments/General3D.lean` be committed build-broken **and** build-invisible
  while `lake build` stayed green (#625, surfaced by the #619 orphan sweep).

  A file that is intentionally outside the build graph for now is listed in the
  shrink-only, issue-linked quarantine `proofs/QBP/.build-visibility-quarantine.json`
  (schema: `{"file", "reason", "issue"}` per entry). The gate hard-fails on a new
  invisible file that is not listed, on a listed file that became visible again or
  no longer exists (stale — remove it), and on any entry missing its tracking
  issue. Adding an entry is a visible, reviewed commit that names an open issue —
  never a silent CI baseline bump. The gate ships with an adversarial self-test
  (`scripts/test_check_layer_imports.py`) that plants a build-invisible file and
  asserts the gate catches it.

## 6. Migration plan (follow-up housekeeping, NOT this PR)

This PR lands the architecture doc, the Foundations aggregator, and the linter
scope for Foundations. The physical moves (`Cosmo/ → Physics/Cosmo/` etc.), the
Physics aggregator, and lakefile root updates are a separate housekeeping PR —
mechanical, reviewable in isolation, gated by the same linter.

**480-B resolution (beekeeper ruling 2026-06-04, option c):**
`Foundations/{Breakdown,Sedenion,CayleyDickson,Octonion}.lean` (the #471
skeletons shipped orphaned via #480) were DELETED; their intended-theorem
inventory is preserved as the rebuild plan of record in issue #503. The ratchet
baseline is zeroed in the same change — the Foundations gate enforces
ZERO sorry / ZERO vacuous-True permanently.
