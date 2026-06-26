cubical-0.9 (agda/cubical, pinned by commit in CI)

# Library-dependent Cubical Agda (the Buchholtz–Rijke S³ port)

Unlike `proofs/agda/` (builtins-only, self-contained), these files depend on the
**agda/cubical** library and are type-checked under `--safe` with it.

- `QBPS3HSpace.agda` — port of Buchholtz–Rijke (arXiv:1610.01134) "Cayley-Dickson
  in HoTT". Proves, fully `--safe`:
  - `HSpace≃` — an H-space transports across a pointed equivalence;
  - `S³-HSpace-from-join : HSpace (join∙ S¹ S¹) → HSpace (S₊∙ 3)` — BR's reduction
    (the structure on S³ comes from the join via the library's `IsoSphereJoin`).
  This **reduces** the S³ H-space port to one obligation — `HSpace (join∙ S¹ S¹)`,
  the Cayley-Dickson join multiplication — which is BR's core and remains open.

Local toolchain: Agda 2.8.0 + agda/cubical (see CI for the pinned setup).

## Progress on the remaining obligation `HSpace (join∙ S¹ S¹)` (the join μ)

The Cayley-Dickson multiplication μ : join S¹ S¹ → join S¹ S¹ → join S¹ S¹ has been
driven (see `analysis/drive-agda-sketch-vv/port/MulProbe.agda`, a WIP probe — `--cubical`,
one hole by design, NOT `--safe`, NOT claimed complete) to:

- **All 8 point + 1-cell cases type-check and are mutually consistent** (corners via the
  S¹ product `_·_` and conjugation `invLooper`; the 1-cells via `push`/`sym push`).
- **The entire μ is reduced to ONE explicit coherence square** — `μ (push a b i) (push c d k)` —
  with a fully documented boundary (four faces). This square is **confirmed non-trivial**
  (naive connection/hcomp fillers fail): it is Buchholtz–Rijke's irreducible 2-cell.

So the port stands at: the reduction `HSpace (join∙ S¹ S¹) → HSpace (S₊∙ 3)` is **proven
and CI-verified** (`QBPS3HSpace.agda`); the join μ is **reduced to a single documented
coherence square**, which (together with verifying the corner formula is the true
quaternion product) is the remaining BR core. Not faked: the square is an open hole.
