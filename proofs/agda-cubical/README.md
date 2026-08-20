cubical-0.9 (agda/cubical, pinned by commit in CI)

# Library-dependent Cubical Agda (the Buchholtz–Rijke S³ port — COMPLETE)

Unlike `proofs/agda/` (builtins-only, self-contained), these files depend on the
**agda/cubical** library and are type-checked under `--safe` with it.

**The port is complete: `S³-HSpace : HSpace (S₊∙ 3)` (S3FromCD.agda), `--safe`,
0 holes, 0 postulates, end to end.** Port of Buchholtz–Rijke (arXiv:1610.01134)
"The Cayley-Dickson Construction in HoTT", faithful to their Lean-2 HoTT
formalization (vendored, Apache 2.0, in `analysis/drive-agda-sketch-vv/port/br-lean2-source/`).

## The chain (checked in this order by dependency)

| File | BR source | Content |
|---|---|---|
| `Diamond.agda` | join.hlean | diamonds in joins: `degSquare`/`hdegSquare` (J), `diamond`, `vdiamond`/`hdiamond`, `symmDiamond`, `twistDiamond`, `apDiamond` (a one-liner — `push` is a binary constructor) |
| `CDJoinBR.agda` | imaginaroid.hlean | `negS`/`starS` on `Susp A₀`, the `CDLaws` record, BR lemmas 1–4, `genDiamond` (suspension induction — the step that closes the coherence square that resisted 7 direct attempts), `cd-mul`, `CDJoin-HSpace : HSpace (join S S , inl 1)` |
| `CDLawsBool.agda` | quaternionic_hopf.hlean | `A₀ = Bool`, `neg₀ = not`: mult = S¹ multiplication conjugated along `S¹IsoSuspBool`; laws via `negS-id`, `star-to`, `rotInv-1/2`, `S1-AssocHSpace` ⇒ `HSpace (join SuspBool SuspBool)` |
| `QBPS3HSpace.agda` | — | the reduction: `HSpace≃` (pointed univalence transport) + `S³-HSpace-from-join : HSpace (join∙ S¹ S¹) → HSpace (S₊∙ 3)` (`IsoSphereJoin 1 1`) |
| `S3FromCD.agda` | — | the wiring: `Iso→joinIso` join congruence, `JoinS¹-HSpace : HSpace (join∙ (S₊∙ 1) (S₊∙ 1))`, **`S³-HSpace : HSpace (S₊∙ 3)`** |

## Axiom cleanliness (#578 AC4)

Agda's `--safe` is transitively enforced (a `--safe` module may only import
`--safe` modules), so the successful check certifies the entire dependency
closure free of `postulate`/`primTrustMe`/`REWRITE`/positivity- and
termination-escapes. Only the cubical primitives (`hcomp`/`transp`/`Glue`)
remain.

## Convention note (#578 AC5)

This port uses **Baez's** CD convention `(a,b)(c,d) = (ac − db*, a*d + cb)`
(faithful to BR). The Lean #474 foundation (`proofs/QBP/Foundations/CDAlg.lean`)
uses **Schafer's** `(ac − d̄b, da + bc̄)`. Both standard; canonically isomorphic
via `φ(a,b) = (a, b*)`. Do not identify components across the two without
routing through φ. Full derivation: `analysis/drive-agda-sketch-vv/port/REFINEMENT-LOG.md`
iteration 13.

Provenance trail (iterations 0–13, including the ~7 failed direct square
attempts and why BR's corner-unification is the only route):
`analysis/drive-agda-sketch-vv/port/REFINEMENT-LOG.md`.

Local toolchain: Agda 2.8.0 + agda/cubical @ 7b9019b (see CI for the pinned setup).
