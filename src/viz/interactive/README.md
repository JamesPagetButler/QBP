# QBP Interactive Proof Visualization

Browser-based interactive visualization of the Stern-Gerlach formal proofs. Step through the proof dependency tree and see how axioms connect to experiment-specific theorems, with physical meaning shown at each step.

## Architecture

The visualization is built with **C + raylib**, compiled to **WASM via Emscripten** for browser deployment.

```
proofs/QBP/Basic.lean ───┐
proofs/QBP/Experiments/  ├─► export_data.py ──► data/proof_graph_01.json
  SternGerlach.lean ─────┘         │                    │
                                   │                    │
                                   │                    ▼
                                   │            (data exchange format,
                                   │             documentation)
                                   │
                                   └──► C hardcoded graph ──► Interactive WASM app
                                       (proof_graph.c)        (proof tree + annotations)
```

**Note:** The C code uses a hardcoded proof graph for simplicity. The JSON file serves as
a portable data exchange format and documentation. The C code does not parse JSON at runtime.
The hardcoded graph and generated JSON must be kept in sync manually.

## Directory Layout

```
src/viz/interactive/
├── README.md           ← you are here
├── CMakeLists.txt      ← CMake build configuration
├── Makefile            ← convenience wrapper
├── shell.html          ← Emscripten HTML template
├── export_data.py      ← Lean → JSON parser (stdlib-only, no simulation deps)
├── src/
│   ├── main.c          ← entry point, scene dispatch
│   ├── qphysics.c/h    ← C port of quaternion math (scaffolding for future)
│   ├── proof_graph.c/h ← hardcoded proof tree + navigation + rendering
│   ├── scene.h         ← scene interface (init/update/draw/cleanup)
│   ├── theme.h         ← QBP steampunk color palette
│   └── scenes/
│       └── experiment_01_stern_gerlach.c
├── data/
│   └── proof_graph_01.json
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
cd src/viz/interactive
python3 export_data.py
```

### Native (desktop window)

```bash
cd src/viz/interactive

# With system-installed raylib:
make native

# With raylib from source:
make native RAYLIB_SRC=/path/to/raylib
```

### WASM (browser)

```bash
cd src/viz/interactive

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

## Proof Dependency Tree (13 nodes)

```
Definitions (Basic.lean)              Experiment Setup (SternGerlach.lean)
────────────────────────              ────────────────────────────────────
isPureQuaternion ────┐                spinXState := SPIN_X
                     │                spinZObservable := SPIN_Z
vecDot ──────────────┤                      │           │
                     │                      │           │
                     │                      ▼           ▼
                     ├─► spin_x_is_pure ──► spinXState_is_pure
                     │                              │
                     ├─► spin_z_is_pure ──► spinZObservable_is_pure
                     │                              │
                     │                              ▼
                     │   x_z_orthogonal ◄──────────┘
                     │         │
                     ▼         ▼
    expectation_orthogonal_is_zero
                     │
                     ▼
    expectation_x_measured_z_is_zero ◄── spinXState_is_pure
                     │                  ◄── spinZObservable_is_pure
                     │                  ◄── x_z_orthogonal
            ┌────────┴────────┐
            ▼                 ▼
    prob_up = 1/2      prob_down = 1/2
```

The key insight: `expectation_x_measured_z_is_zero` explicitly passes
`spinXState_is_pure` and `spinZObservable_is_pure` as arguments to the
general theorem, making them formal dependencies.

## Adding New Experiments

1. Create `src/scenes/experiment_NN_name.c` implementing the `Scene` interface
2. Add a `ProofGraph` initializer with the experiment's proof tree (update `proof_graph.c`)
3. Update `export_data.py` to handle the new Lean files
4. Register the scene in `main.c`
5. Add source files to `CMakeLists.txt`
6. Run `python3 export_data.py` to regenerate JSON
7. **Important:** Keep the C hardcoded graph and JSON in sync
