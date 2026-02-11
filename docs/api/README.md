# QBP API Documentation

This directory contains API reference documentation for the libraries developed in the QBP project.

## Libraries

### Python

| Library | Description |
|---------|-------------|
| [qphysics](qphysics.md) | Core quaternion physics engine — states, observables, evolution, measurement, rotation |

### C (WASM)

| Library | Description |
|---------|-------------|
| [proof_graph](proof_graph.md) | Interactive proof visualization — graph layout, navigation, pan/zoom, 4-level descriptions |

## Quick Links

**qphysics** — The computational core:
- `create_state()` / `create_state_from_vector()` — Prepare quantum states
- `SPIN_X`, `SPIN_Y`, `SPIN_Z` — Pre-defined spin observables
- `expectation_value()` / `measure()` — Measurement operations
- `rotate_observable()` / `rotate_state()` — Quaternion rotations

**proof_graph** — Interactive visualization:
- `graph_load_json()` — Load from data file
- `graph_layout()` — Automatic positioning
- `graph_viewport_update()` — Pan/zoom controls
- `graph_draw()` / `graph_draw_info_panel()` — Rendering

## Data Files

Proof visualization data is stored as JSON in `data/`:
- `stern_gerlach.viz.json` — Experiment 01 (Stern-Gerlach)
- `angle_dependent.viz.json` — Experiment 01b (Angle-Dependent)

See [proof_graph.md](proof_graph.md) for JSON schema documentation.
