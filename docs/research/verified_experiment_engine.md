# Research Report: Verified Experiment Engine (Lean 4) and 3D Visualization

**Research Sprint:** 0R
**Issues:** #123, #203
**Date:** 2026-02-11
**Status:** Complete

## Executive Summary

This report investigates two infrastructure enhancements for QBP:
1. **Lean 4 as Verified Experiment Engine** — Using proven-correct Lean code as test oracles for Python simulations
2. **3D Interactive Visualization** — Evaluating Go game engines vs. alternatives for proof visualization

**Key Findings:**
- Lean 4 verified oracle is **highly feasible** (5-7 weeks effort) using the Cedar pattern
- Go 3D engines are **not recommended** — current C/Raylib approach is superior
- **Three.js** is the best alternative if web-native iteration speed is desired

---

## Part 1: Lean 4 as Verified Experiment Engine (#123)

### 1.1 The Cedar Pattern

Amazon's Cedar project (policy authorization) demonstrates a production-proven approach:

1. **Write executable formal model in Lean** — Small, readable, provably correct
2. **Implement production code in Rust/Python** — Optimized for performance
3. **Differential testing** — Generate millions of random inputs, compare outputs
4. **Key metric:** Lean executes at 5 microseconds/test (100M+ tests nightly feasible)

**Results:** 25 bugs found — 4 via proofs, 21 via differential testing

### 1.2 QBP Architecture

```
┌─────────────────────────────────────────────────────────┐
│  Lean 4 (Verified Oracle)                               │
│  ┌─────────────────────┐  ┌─────────────────────────┐   │
│  │ Proofs (Real)       │  │ Computation (Float)     │   │
│  │ - prob_up_angle     │  │ - probUpFloat           │   │
│  │ - quaternion_props  │→→│ - floatQuaternion       │   │
│  └─────────────────────┘  └──────────┬──────────────┘   │
│                                      │ JSON output       │
└──────────────────────────────────────┼──────────────────┘
                                       ↓
┌──────────────────────────────────────┼──────────────────┐
│  Python Simulation                   │                  │
│  ┌─────────────────────┐  ┌─────────┴────────────────┐  │
│  │ qphysics.py         │←←│ Differential Comparator  │  │
│  │ - spin states       │  │ - compare outputs        │  │
│  │ - measurement       │  │ - flag divergences       │  │
│  └─────────────────────┘  └──────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
```

### 1.3 Technical Details

**Quaternion Support:** Mathlib4 provides comprehensive quaternion algebra:
- `Ring ℍ[R]`, `StarRing ℍ[R]`, `DivisionRing ℍ[R]`
- All definitions are computable
- Already used in QBP proofs: `abbrev Q := Quaternion ℝ`

**Floating-Point Handling:**
- Proofs use symbolic `Real` (ℝ) — kernel cannot reduce floats
- Computation uses `Float` (64-bit IEEE 754) — full arithmetic support
- Solution: Parallel implementation with Float that mirrors proof structure

**Python Interop:**
- JSON interchange (simplest, no FFI complexity)
- LeanInteract library (experimental Python-Lean bridge)
- Future: FFI roadmap in Lean FRO Year 3 (2025-2026)

### 1.4 Existing Resources

| Resource | Status | Relevance |
|----------|--------|-----------|
| **SciLean** | Early-stage | ODE solving, auto-diff, OpenBLAS |
| **PhysLean** | Active (40 contributors) | QM formalization, Maxwell's equations |
| **Mathlib Quaternion** | Mature | Full algebra, ready to use |
| **QBP Proofs** | Complete | AngleDependent.lean, SternGerlach.lean |

### 1.5 Implementation Plan

| Phase | Effort | Description |
|-------|--------|-------------|
| **1. Float Oracle** | 1-2 weeks | `Float` versions of probability calculations |
| **2. JSON Export** | 3 days | Lean outputs predictions to JSON |
| **3. Python Harness** | 1 week | Differential testing framework |
| **4. Property Tests** | 2-3 weeks | Random input generation, edge cases |
| **5. CI Integration** | 1 week | Automated regression in GitHub Actions |

**Total: 5-7 weeks**

### 1.6 Recommendation

**Proceed with Phase 4b implementation.** The Cedar pattern is proven, our Lean infrastructure exists, and the effort is bounded. This provides:
- Mathematical guarantee that test oracle is correct
- Automated detection of Python implementation bugs
- Higher confidence in published results

---

## Part 2: 3D Interactive Visualization (#203)

### 2.1 Go Game Engine Evaluation

| Engine | 3D | WASM | Maturity | Verdict |
|--------|-----|------|----------|---------|
| **Ebitengine** | No | Yes | Excellent | 2D only — unusable |
| **g3n** | Yes | 90% | Stalled (2021) | Incomplete WASM — not recommended |
| **raylib-go** | Yes | External | Good | No advantage over C/raylib |
| **Webzen** | ? | Yes | Archived | Dead project |

**Conclusion:** Go 3D ecosystem is not mature enough for production WebAssembly.

### 2.2 Current QBP Architecture

From `src/viz/interactive/`:

| Metric | Value |
|--------|-------|
| **WASM size** | 217 KB |
| **JS loader** | 216 KB |
| **Total** | ~772 KB |

Features:
- Custom scene graph with proof node hierarchy
- Pan/zoom camera controls
- 4-level layered descriptions (L1-L4)
- JSON proof loading (cJSON)
- Experiment switching

**Assessment:** Current C/Raylib/Emscripten approach is well-designed and efficient.

### 2.3 Alternative Comparison

| Option | Bundle Size | 3D | Iteration Speed | Recommendation |
|--------|-------------|-----|-----------------|----------------|
| **C/Raylib (current)** | 217 KB | Yes | Slow (compile) | **Keep** |
| **Three.js** | ~150 KB | Yes | Fast (JS) | **Consider for future** |
| **Bevy (Rust)** | 5-10 MB | Yes | Medium | For compute-heavy |
| **Godot** | 20+ MB | Yes | Visual editor | Overkill |
| **Go engines** | 5+ MB | Limited | Medium | **Not recommended** |

### 2.4 Three.js Migration Path (If Desired)

1. Keep JSON proof format unchanged
2. Use [3d-force-graph](https://github.com/vasturiano/3d-force-graph) for node visualization
3. Add OrbitControls for camera
4. CSS overlays for 4-level description panels
5. Zero compilation step for iteration

### 2.5 Recommendation

**Keep current C/Raylib/Emscripten approach.** It's efficient (217 KB) and works well.

**Consider Three.js for Phase 4d** if:
- Faster iteration on visualization is needed
- Web UI integration becomes important
- Richer interactivity is desired

**Do not pursue Go game engines.** The ecosystem is immature for 3D WebAssembly.

---

## Part 3: Phase 4d Proposal

### 3.1 Definition

**Phase 4d: Verified Differential Testing**

After formal proofs (4a) and proof review (4b) and proof visualization (4c), Phase 4d validates that the Python implementation matches the proven-correct Lean model.

### 3.2 Workflow Integration

```
Phase 4: Formal Verification
├── 4a: Formal Proof (Lean 4)           — Prove physics theorems
├── 4b: Proof Review (Claude/Gemini)    — Verify proof quality
├── 4c: Interactive Proof Visualization — Communicate proof structure
└── 4d: Verified Differential Testing   — Validate Python matches Lean
```

### 3.3 Phase 4d Process

1. **Lean Oracle Export**
   - Compile `Float`-based computation from proof structure
   - Generate test predictions for parameter space
   - Output as JSON: `{theta: 45, expected_prob: 0.8536, tolerance: 1e-6}`

2. **Python Comparison**
   - Load Lean predictions
   - Run same parameters through `qphysics.py`
   - Report divergences exceeding tolerance

3. **Property Testing**
   - Random parameter generation (angles, states)
   - Edge cases (0°, 90°, 180°, 360°)
   - Statistical validation (1M trials, 3σ criterion)

4. **CI Integration**
   - GitHub Action runs on PR
   - Fails if divergence detected
   - Reports: "0 divergences in 10,000 test cases"

### 3.4 Exit Criteria

- [ ] Lean Float oracle compiles and runs
- [ ] JSON export of test predictions works
- [ ] Python differential testing harness implemented
- [ ] 0 divergences for all experiments
- [ ] CI pipeline integrated

---

## References

### Lean 4 / Verified Computing
- [Lean Cedar Case Study](https://lean-lang.org/use-cases/cedar/)
- [Amazon Science: Building Cedar](https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing)
- [SciLean](https://github.com/lecopivo/SciLean)
- [PhysLean](https://physlean.com/)
- [Mathlib Quaternion](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Quaternion.html)

### Visualization
- [Ebitengine](https://ebitengine.org/)
- [g3n Engine](https://github.com/g3n/engine)
- [Three.js](https://threejs.org/)
- [3d-force-graph](https://github.com/vasturiano/3d-force-graph)
- [Bevy](https://bevyengine.org/)

### QBP Implementation
- Current proofs: `proofs/QBP/Experiments/`
- Current viz: `src/viz/interactive/`
- Python simulation: `src/qphysics.py`
