# QBP Interactive Proof Visualization

Browser-based interactive visualization of the Stern-Gerlach formal proofs. Step through the proof dependency tree and see how axioms connect to experiment-specific theorems, with physical meaning shown at each step.

## Architecture

The visualization is built with **C + raylib**, compiled to **WASM via Emscripten** for browser deployment.

```
export_data.py ──► data/experiment_01.json ──► C reads JSON
                                                    │
proofs/QBP/Basic.lean ───┐                          ▼
proofs/QBP/Experiments/  ├─► (proof metadata)   Interactive WASM app
  SternGerlach.lean ─────┘                      (proof tree + annotations)
```

## Directory Layout

```
src/viz/interactive/
├── README.md           ← you are here
├── CMakeLists.txt      ← CMake build configuration
├── Makefile            ← convenience wrapper
├── shell.html          ← Emscripten HTML template
├── export_data.py      ← Lean → JSON parser
├── src/
│   ├── main.c          ← entry point, scene dispatch
│   ├── qphysics.c/h    ← C port of quaternion math
│   ├── proof_graph.c/h ← proof tree data + navigation + rendering
│   ├── scene.h         ← scene interface (init/update/draw/cleanup)
│   ├── theme.h         ← QBP steampunk color palette
│   └── scenes/
│       └── experiment_01_stern_gerlach.c
├── data/
│   └── experiment_01.json
├── build/              ← .gitignore'd
└── dist/               ← .gitignore'd
```

## Prerequisites

### Native build (development)
- CMake >= 3.16
- gcc or clang
- raylib 5.0+ (system install or source)

### WASM build (deployment)
- [Emscripten SDK](https://emscripten.org/docs/getting_started/downloads.html)
- raylib source (for cross-compilation)

## Build

### Generate proof data

```bash
python3 export_data.py
```

### Native (desktop window)

```bash
# With system-installed raylib:
make native

# With raylib from source:
make native RAYLIB_SRC=/path/to/raylib
```

### WASM (browser)

```bash
# Activate emsdk first:
source /path/to/emsdk/emsdk_env.sh

# Build:
make wasm RAYLIB_SRC=/path/to/raylib

# Serve:
python3 -m http.server -d dist
```

## Controls

| Key | Action |
|-----|--------|
| `→` / `↓` / `Space` / `Enter` | Step forward |
| `←` / `↑` / `Backspace` | Step back |
| `R` / `Home` | Reset to beginning |
| Click | Jump to node |

## Proof Dependency Tree (12 nodes)

```
Axioms (Basic.lean)                     Experiment Setup (SternGerlach.lean)
─────────────────                       ────────────────────────────────────
isUnitQuaternion ──┐                    spinXState := SPIN_X
isPureQuaternion ──┤                    spinZObservable := SPIN_Z
                   │                           │
                   ├── spin_x_is_pure ─────────┤
                   ├── spin_z_is_pure ─────────┤
                   │                           │
                   │   vecDot ─────────────────┤
                   │         │                 │
                   │         ↓                 ↓
                   │    x_z_orthogonal: vecDot(i,k) = 0
                   │         │
                   ↓         ↓
        expectation_orthogonal_is_zero
                   │
                   ↓
        expectation_x_measured_z_is_zero: ⟨O_z⟩ = 0
                   │
            ┌──────┴──────┐
            ↓             ↓
  prob_up = 1/2    prob_down = 1/2
```

## Adding New Experiments

1. Create `src/scenes/experiment_NN_name.c` implementing the `Scene` interface
2. Add a `ProofGraph` initializer with the experiment's proof tree
3. Update `export_data.py` to handle the new Lean files
4. Register the scene in `main.c`
5. Add source files to `CMakeLists.txt`
