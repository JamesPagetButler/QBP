# The substrate as the arena of crystallisation — hosting definition v0.1 (2026-09-07)

**Status:** definition v0.1 for #639 (AC1-hosting) under the beekeeper's 2026-09-07 rulings — Lean groundwork landed (`proofs/QBP/Foundations/CrystalHosting.lean`, 98 axiom-clean declarations; `proofs/QBP/Substrate/Hosting.lean` is the definition file, the first in `Substrate/`); DERIV-holographic theorem parts landed (`HolographicSubalgebra.lean`, 45 theorems): the empty-`Substrate/` rule is lifted for this definition; the working frame is *the substrate is what allows crystallisation; a crystallisation enables one specific instance of the Cayley–Dickson tower, bounded by the boundary of that universe; "universe" = one crystallised instance, ours being one.* Every claim below is tagged with its source: a Lean theorem, an Agda theorem, a numerical script, a CTH ledger entry (with its status), or a beekeeper ruling. Nothing here is FORCED unless the tag says theorem; the interpretive reading of the crystal's ℍ as "the observer's" (DERIV-holographic) is **not** used — pending flag 3.

## 1. The objects, with sources

| Object | Definition | Source and status |
|---|---|---|
| **Substrate 𝒮** | the state sphere S¹⁴ ⊂ Im𝕊 with the metric N, the potential V = δ² = ‖[a, b]‖², the initial ensemble = N's surface measure, and the rule | N: theorem (PROOF-normed-division-tower-existence; positive-definite at 16). V: theorem (PROOF-delta-landscape-descent). Ensemble: beekeeper ruling, horn 1, PERMITTED (MaxEnt with N's geometry as reference). Rule: postulate (#635), currently first-order overdamped descent |
| **Space of universes 𝓤** | the vacuum manifold {V = 0} ∩ S¹⁴ modulo G₂: a 2-sphere with coordinates (θ mod 180°, b₀); modulo the S₃ of Aut(𝕊), the orbifold S²(2,2,3) | parametrisation: **Lean** `CrystalHosting.vacuum_iff_parametrised` (a = α·u, Im b = γ·u, b₀; the poles u = 0 handled: `vacuum_pole_of_dir_zero`), `vacuum_norm_parametrised` (N = α² + γ² + b₀²); topology (suspension of ℝP¹ ≅ S²): elementary + numerical (`orbit_space.py`, `lmaps_check.py`); S₃ action: exact numerical (`aut_s3.py`) |
| **A universe U(s)** | a crystal s ∈ {V = 0} together with the quaternion subalgebra it generates with ℓ, ℍ_s = span{1, u, ℓ, uℓ} (u the common direction of its parallel components), and the physics hosted on the unit sphere of ℍ_s (an S³) | quaternion subalgebra: **Lean** `CrystalHosting.vacuum_hosts_quaternion` (every word in {1, s, ℓ} lies in span{1, u, ℓ, ℓu}), `crystal_quaternion_table` (the ℍ relations), `crystal_quatSpan_independent` (exactly 4-dim), `quatSpan_dir_proper` (a proper part of 𝕊); at the poles ±ℓ the hosted algebra is span{1, ℓ} ≅ ℂ (`vacuum_pole_of_dir_zero`); uniqueness of ℓ's role: `assoc_self_zero_iff`; S³ H-space: Agda `S3FromCD.S³-HSpace` (--safe). Orientation note: k = ℓu vs k = uℓ are the same 4-space with opposite k; not fixed by the landscape — a theory convention to fix if chirality ever matters |
| **Boundary of a universe** | the boundary encoding is 𝕆 (AXIOM-2); 𝕊 is the inter-universe structure (DERIV-sedenion, layer 1); the seams are the zero-divisor locus V = 1 | AXIOM-2 (axiom); DERIV-sedenion (derived principle; **flag 1 open**: "information CAN be destroyed" vs AXIOM-1); ZD ridge: Lean `PROOF-sedenion-zero-divisor-witnesses`, numerical `generic_maps_check.py` (layer 3: the algebra's own maps run to the seams) |
| **Pre-universe (in-flight region)** | {V > 0}: states whose components do not commute, hence generate no associative algebra; crystallisation = the rule's flow from the ensemble to a crystal | Lean: vacuum ⇔ components commute (PROOF-alternator-vanishes-iff-commute) ⇔ −L_s² = N(s)·id exactly (`CrystalHosting.left_mul_sq_scalar_iff_vacuum`; `vacuum_eigenvalue_unique`: N(s) is the only eigenvalue) — so "not yet crystallised" is the theorem "the scalar spectrum fails", and off a vacuum the alternator is exactly first order (`alternator_expansion_off_vacuum`); flow: numerical (#629, `flow_big.py`); endpoint statistics: numerical (0.146 quench; ≈ 1/3 anneal; 1 ℓ-axis) |
| **Our universe** | one point of 𝓤, with a b₀ to be identified observationally | #637 (open); kill tests by support (ℓ-axis rule dies if |b₀| < 1 is measured) |

## 2. The hosting clauses, restated on these objects

| Clause | Statement on the objects | Witness / status |
|---|---|---|
| (a) Existence | an entity in U(s) is a persistent configuration: a map into the unit sphere S³ of ℍ_s with a topological charge | Agda: baryon number = degree, B(hedgehog) = 1, π₃(S³) ≅ ℤ (`SkyrmionCharge.agda`) |
| (b) Behaviour | an interaction is a morphism of U(s): the H-space product μ on S³; charges add | Agda: B(f ⋆ g) = B f + B g (`SubstrateCharge.agda`, PROOF-substrate-baryon-additive) |
| (c) Coming into being | crystallisation is the rule's flow in 𝒮 from the in-flight region to a point of 𝓤; the in-flight regime is the part of 𝒮 where no associative algebra exists yet | Lean: the descent of V to the orbit invariants (PROOF-delta-landscape-descent); flow: numerical; the "pointless" description of the in-flight region: open (CONJ-condensed-math-for-transition-state, marginal) |
| (d) Reviewable standard | each clause machine-checked or scripted, with a kill condition | this document + `proofs/QBP/Substrate/Hosting.lean` (the first file in `Substrate/`, per the beekeeper's lift): `StateSphere`, `potential` (= V, `potential_eq_zero_iff_isVacuum`), `UniverseSpace` / `InFlight` (a partition: `universeSpace_union_inFlight`, disjoint), `structure Universe` with `hosted` = the algebra the crystal generates with ℓ; `universe_hosts_quaternion`, `universe_hosted_proper`, `pole_hosts_complex` (poles host ℂ, an equality), `local_spectrum_at_universe` (s(sx) = −x on the sphere), `hosting_equivariant`, `inFlight_no_quaternion_closure` ⇔ `mem_universeSpace_iff_complex_structure` (the two regions separated by an iff); non-vacuity: `universeSpace_nonpole`, `inFlight_nonempty`. 58 axiom checks clean |
| (e) Crystal-covariance | (a)–(c) hold at every s ∈ 𝓤; S₃-equivalent crystals are identical physics | ℍ_s is defined for every crystal (`vacuum_hosts_quaternion`); equivariance under every ℓ-fixing automorphism — the G₂ side — is **Lean** (`CrystalHosting.aut_hosting_equivariant`, `aut_image_quatSpan` onto; `CDAut` with map_one/map_re/map_N derived, populated by `cdLift`); the S₃ side (ℓ ↦ −ℓ, `gradeAut`) is equivariant only up to the sign of ℓ, exact numerically (`aut_s3.py`); the S³ H-space transports to every unit sphere of ℍ_s (Agda wiring, to do) |

## 3. What this definition does not claim

- It does not derive ℝ, the doubling, the measure class, or the rule (job A, closed negative: KILLED-locale-forcing-route; Prop 12 ratified). The substrate hosts; circularity with the algebra is permitted.
- It does not identify ℍ_s with "the observer's ℍ" (DERIV-holographic, flag 3). The theorem parts are now proved (`HolographicSubalgebra.lean`: L_xL_y = L_{xy} exactly on associative sets; quaternion frames are associative subalgebras; no associative subalgebra of 𝕆 properly contains a quaternion frame; codimension 4 — frame-relative, the honest ceiling until an inner product is registered as its own foundational PR); the postulate "observers require associativity" stays a postulate; "holographic boundary" is interpretation, to be defined and discussed next.
- It does not resolve flag 1 (DERIV-sedenion vs AXIOM-1). The seams are where the algebra's own maps go (layer 3); what happens to information there is the open constitutional question.
- It does not yet say what the in-flight region *is* as a space with configurations (clause (c)'s pointless half). That is the question for the Gemini conversation.

## 4. Kill conditions

| Clause | Kill |
|---|---|
| (a) | no persistent configuration can be exhibited on some ℍ_s unit sphere (impossible if T1 + Agda transport hold for all s) |
| (b) | the H-space product fails to be a morphism of U(s) for some s |
| (c) | the rule's flow fails to converge to 𝓤 from generic initial data (numerically it does; a Łojasiewicz-type argument is owed) |
| (e) | a construction in (a)–(c) that works at one crystal only, or distinguishes S₃-equivalent crystals |

## 5. Open questions for the definition conversation (to be run after the Lean lands)

1. Is "universe = crystal + ℍ_s + hosted S³ physics" the right unit, or must a universe include its in-flight history (the path in 𝒮)?
2. The boundary: AXIOM-2 says the boundary encoding is 𝕆, while the crystal's algebra is ℍ_s ⊂ 𝕆 ⊕ 𝕆ℓ. Where in 𝒮 is the boundary of U(s) — the 𝕆 containing u, the seams, or the complement of ℍ_s in 𝕊?
3. The in-flight region as a space: which of {the orbit-space flow as a process, a locale/condensed object, a limit of finite approximations} is a definition rather than a description?
4. What is measurable across 𝓤 (b₀; the S₃ class; the local spectrum) and where does our universe sit?

## 6. Two honest degrees of freedom left open in the Lean

- **Orientation of the hosted ℍ.** k = ℓ·u and k = u·ℓ span the same 4-space with opposite sign (`inQuatSpan_ell_right`); nothing in the landscape fixes it, so every statement is orientation-neutral. If chirality ever becomes load-bearing, this is a convention theory must fix, not Lean.
- **The direction u of a crystal is not proved canonical.** `Universe.dir` is a `Classical.choose`; uniqueness of u up to sign for a non-pole crystal is presumably true and not proved. Needed before a map 𝓤 → S² is defined in Lean; to be filed under #634/#639.
