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
