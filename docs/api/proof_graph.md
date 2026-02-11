# proof_graph API Reference

**Module:** `src/viz/interactive/src/proof_graph.c/h`

Interactive proof dependency visualization library built on raylib. Renders formal mathematical proofs as navigable graphs with four levels of explanation.

## Overview

The proof_graph library provides:
- **Graph data structure** for proof dependency trees
- **Automatic layout algorithm** (topological levels + barycenter ordering)
- **Viewport pan/zoom** for navigating large proof graphs
- **JSON loading** for data-driven content
- **Four-level descriptions** (Formal → Mathematical → Physical → Intuitive)

---

## Data Structures

### ProofNode

Represents a single node (theorem, definition, or axiom) in the proof tree.

```c
typedef struct {
    int         id;
    char        name[64];           /* Internal identifier (from Lean) */
    char        display_name[128];  /* Human-readable title */
    NodeKind    kind;               /* NODE_AXIOM, NODE_DEFINITION, NODE_THEOREM */

    /* Layered descriptions */
    char        level4_formal[256];     /* Lean syntax */
    char        level3_math[256];       /* Conventional notation */
    char        level2_physical[512];   /* Physics interpretation */
    char        level1_intuitive[512];  /* Plain English */
    char        key_insight[256];       /* One-sentence summary */

    int         deps[6];      /* IDs of nodes this depends on */
    int         dep_count;
    Vector2     pos;          /* Layout position (set by graph_layout) */
} ProofNode;
```

### NodeKind

```c
typedef enum {
    NODE_AXIOM,       /* Foundational assumptions */
    NODE_DEFINITION,  /* Named concepts */
    NODE_THEOREM      /* Proven results */
} NodeKind;
```

### ProofGraph

Container for the entire proof dependency tree.

```c
typedef struct {
    ProofNode   nodes[32];
    int         node_count;
    int         walk_order[32];   /* Order to visit nodes in walkthrough */
    int         walk_len;
    int         current_step;     /* 0-based index into walk_order */

    /* Viewport state */
    float       viewport_x;       /* Pan offset X */
    float       viewport_y;       /* Pan offset Y */
    float       viewport_zoom;    /* Zoom factor (1.0 = 100%) */
    Rectangle   graph_bounds;     /* Bounding box of all nodes */
    Rectangle   view_area;        /* Visible area on screen */
} ProofGraph;
```

---

## Initialization

### `graph_load_json(ProofGraph *g, const char *json_path) -> int`

Load a proof graph from a JSON file. **Preferred method.**

| Parameter | Type | Description |
|-----------|------|-------------|
| `g` | ProofGraph* | Graph to populate |
| `json_path` | const char* | Path to JSON file |

**Returns:** 0 on success, -1 on error.

**JSON Schema:**
```json
{
  "experiment_id": "01_stern_gerlach",
  "title": "Stern-Gerlach Experiment",
  "walk_order": ["isPureQuaternion", "vecDot", "spin_x_is_pure", ...],
  "nodes": {
    "isPureQuaternion": {
      "display_name": "Pure Quaternion Definition",
      "kind": "definition",
      "L4_formal": "def isPureQuaternion (q : H) : Prop := q.re = 0",
      "L3_math": "A quaternion q = a + bi + cj + dk is pure iff a = 0",
      "L2_physical": "Pure quaternions represent physical directions...",
      "L1_intuitive": "Think of a pure quaternion as a 3D arrow...",
      "key_insight": "Pure quaternions are directions, not scalars.",
      "depends_on": []
    },
    ...
  }
}
```

### `graph_init_stern_gerlach(ProofGraph *g)`

**Deprecated.** Hardcoded initialization for Stern-Gerlach. Kept as fallback.

### `graph_viewport_init(ProofGraph *g)`

Initialize viewport state to default (no pan, zoom = 1.0).

---

## Layout

### `graph_layout(ProofGraph *g, Rectangle area)`

Compute node positions using automatic layout algorithm.

| Parameter | Type | Description |
|-----------|------|-------------|
| `g` | ProofGraph* | Graph to layout |
| `area` | Rectangle | Available screen area for the graph |

**Algorithm:**
1. **Topological levels**: Roots at level 0, each node's level = max(dependency levels) + 1
2. **Barycenter ordering**: Nodes at each level sorted by average parent X position
3. **No-overlap guarantee**: Computes actual node widths, positions with sufficient spacing
4. **Virtual canvas**: Graph bounds may exceed view area (use pan/zoom to navigate)

**Example:**
```c
ProofGraph g;
graph_load_json(&g, "/data/angle_dependent.viz.json");
graph_viewport_init(&g);
graph_layout(&g, (Rectangle){20, 60, 800, 500});
```

---

## Viewport Control

### `graph_viewport_update(ProofGraph *g)`

Handle per-frame input for pan/zoom. Call in your update loop.

**Controls:**
- Mouse wheel: Vertical scroll
- Shift + wheel: Horizontal scroll
- Ctrl + wheel: Zoom in/out
- Middle mouse drag: Pan

### `graph_pan(ProofGraph *g, float dx, float dy)`

Pan the viewport by (dx, dy) in graph coordinates. Clamped to bounds.

### `graph_zoom(ProofGraph *g, float delta, Vector2 focus)`

Zoom by delta (positive = zoom in) around focus point. Range: 0.5x to 2.0x.

### `graph_reset_viewport(ProofGraph *g)`

Reset to initial state (no pan, zoom = 1.0).

---

## Navigation

### `graph_step_forward(ProofGraph *g)`

Move to next step in the proof walkthrough.

### `graph_step_back(ProofGraph *g)`

Move to previous step.

### `graph_reset(ProofGraph *g)`

Reset to first step.

### `graph_current_node(const ProofGraph *g) -> const ProofNode*`

Get the currently highlighted node.

### `graph_is_active(const ProofGraph *g, int node_id) -> int`

Returns 1 if node_id is the currently active (highlighted) node.

### `graph_is_dependency(const ProofGraph *g, int node_id) -> int`

Returns 1 if node_id is a direct dependency of the active node.

### `graph_node_bounds(const ProofGraph *g, int node_id) -> Rectangle`

Get screen-space bounding rectangle for a node (for click detection).

---

## Drawing

### `graph_draw(const ProofGraph *g)`

Draw the proof graph with:
- Edges between dependent nodes
- Rounded node rectangles with kind badges (AXM/DEF/THM)
- Scroll indicators when content extends beyond view
- Zoom level indicator when zoomed

**Must call between raylib's BeginDrawing() and EndDrawing().**

### `graph_draw_info_panel(const ProofGraph *g, Rectangle panel)`

Draw the info panel for the current node showing:
- Display name and internal Lean name
- Kind badge (colored: Axiom=crimson, Definition=amber, Theorem=teal)
- Four description levels (Formal → Mathematical → Physical → Intuitive)
- Key insight
- Dependencies list
- Overflow indicator if content exceeds panel height

### `graph_draw_step_bar(const ProofGraph *g, Rectangle bar)`

Draw the step navigation bar with:
- Current step indicator ("Step 3/13 -- Node Name")
- Prev/Next navigation buttons

---

## Color Scheme (from theme.h)

| State | Color |
|-------|-------|
| Active node | `QBP_NODE_ACTIVE` (bright gold) |
| Dependency | `QBP_NODE_DEP` (blue-green) |
| Visited | `QBP_VERDIGRIS` (teal) |
| Unvisited | `QBP_NODE_IDLE` (dark slate) |
| Edges (active) | `QBP_EDGE` (gold) |
| Edges (inactive) | `QBP_STEEL` (gray) |

---

## Usage Example

```c
#include "proof_graph.h"
#include "json_loader.h"
#include "raylib.h"

int main(void) {
    InitWindow(1200, 800, "QBP Proof Viz");
    SetTargetFPS(60);

    ProofGraph graph;
    graph_load_json(&graph, "/data/stern_gerlach.viz.json");
    graph_viewport_init(&graph);
    graph_layout(&graph, (Rectangle){20, 60, 700, 650});

    while (!WindowShouldClose()) {
        // Update
        graph_viewport_update(&graph);
        if (IsKeyPressed(KEY_RIGHT)) graph_step_forward(&graph);
        if (IsKeyPressed(KEY_LEFT)) graph_step_back(&graph);
        if (IsKeyPressed(KEY_R)) {
            graph_reset(&graph);
            graph_reset_viewport(&graph);
        }

        // Draw
        BeginDrawing();
        ClearBackground((Color){13, 27, 42, 255});

        graph_draw(&graph);
        graph_draw_info_panel(&graph, (Rectangle){740, 60, 440, 650});
        graph_draw_step_bar(&graph, (Rectangle){0, 740, 1200, 56});

        EndDrawing();
    }

    CloseWindow();
    return 0;
}
```

---

## Creating New Visualizations

To add a new experiment visualization:

1. **Create JSON file** in `data/` (e.g., `data/new_experiment.viz.json`)
2. **Define nodes** with all four description levels
3. **Specify walk_order** for the proof walkthrough sequence
4. **Add scene file** in `src/scenes/` following existing patterns

**Four-Level Description Guide:**

| Level | Audience | Style | Example |
|-------|----------|-------|---------|
| L4 Formal | Lean users | Exact syntax | `def isPure (q : H) := q.re = 0` |
| L3 Math | Physicists | Standard notation | `q = a + bi + cj + dk is pure iff a = 0` |
| L2 Physical | Students | Physics concepts | "Pure quaternions represent directions in 3D" |
| L1 Intuitive | General | Plain English | "Think of it as a 3D arrow" |

---

## Build Requirements

- **raylib** (WASM-compatible)
- **cJSON** (for JSON parsing)
- **Emscripten** (for web builds)

Build command:
```bash
cd src/viz/interactive
make clean && make
```

Output: `build/wasm/index.html` (open in browser)
