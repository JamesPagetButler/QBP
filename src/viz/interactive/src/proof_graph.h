/*
 * proof_graph.h — Proof dependency tree for interactive visualization.
 *
 * Each ProofNode represents a theorem/definition from the Lean proofs.
 * The tree is navigated step-by-step, highlighting the active node
 * and its dependencies at each step.
 *
 * Descriptions are provided at 4 levels of detail:
 *   L4 (Formal):      Lean syntax, for proof assistant users
 *   L3 (Mathematical): Conventional notation, for physicists/mathematicians
 *   L2 (Physical):     Physics interpretation, for students/enthusiasts
 *   L1 (Intuitive):    Plain English, for general audience (NYT readers)
 */

#ifndef QBP_PROOF_GRAPH_H
#define QBP_PROOF_GRAPH_H

#include "raylib.h"

#define MAX_DEPS 6
#define MAX_NODES 128
#define MAX_NAME_LEN 64
#define MAX_DISPLAY_NAME_LEN 128
#define MAX_FORMAL_LEN 256
#define MAX_MATH_LEN 256
#define MAX_PHYSICAL_LEN 512
#define MAX_INTUITIVE_LEN 512
#define MAX_INSIGHT_LEN 256
#define MAX_TAGS_LEN 256

typedef enum {
    NODE_AXIOM,
    NODE_DEFINITION,
    NODE_THEOREM
} NodeKind;

typedef struct {
    int         id;
    char        name[MAX_NAME_LEN];           /* Internal identifier */
    char        display_name[MAX_DISPLAY_NAME_LEN]; /* Human-readable title */
    NodeKind    kind;

    /* Layered descriptions (top to bottom in panel) */
    char        level4_formal[MAX_FORMAL_LEN];      /* Lean syntax */
    char        level3_math[MAX_MATH_LEN];          /* Conventional notation */
    char        level2_physical[MAX_PHYSICAL_LEN];  /* Physics interpretation */
    char        level1_intuitive[MAX_INTUITIVE_LEN];/* Plain English */
    char        key_insight[MAX_INSIGHT_LEN];       /* One-sentence "aha" */

    int         deps[MAX_DEPS];      /* ids of nodes this depends on */
    int         dep_count;
    Vector2     pos;                 /* layout position (set by graph_layout) */

    /* Tags for filtering/highlighting (#228, #229) */
    char        tags[MAX_TAGS_LEN];  /* comma-separated tags from JSON */
    int         has_tag_angle;       /* precomputed: 1 if "angle" tag present */
    char        proof_role[32];      /* "goal", "lemma", "utility", "" */
} ProofNode;

typedef struct {
    ProofNode   nodes[MAX_NODES];
    int         node_count;
    int         walk_order[MAX_NODES]; /* order to visit nodes in walkthrough */
    int         walk_len;
    int         current_step;          /* 0-based index into walk_order */

    /* Viewport state for pan/zoom */
    float       viewport_x;            /* Pan offset X (positive = graph shifted left) */
    float       viewport_y;            /* Pan offset Y (positive = graph shifted up) */
    float       viewport_zoom;         /* Zoom factor (1.0 = 100%) */
    Rectangle   graph_bounds;          /* Computed bounding box of all nodes */
    Rectangle   view_area;             /* Visible area on screen */

    /* Display modes (#228, #229) */
    int         angle_highlight;       /* 1 = emphasize angle-dependent nodes */
    int         overview_mode;         /* 1 = show overview panel instead of graph */
    int         panel_hidden;          /* 1 = info panel hidden; graph takes the full width (#261 HVR) */
} ProofGraph;

/* Initialize the Stern-Gerlach proof graph (hardcoded from Lean files) */
void graph_init_stern_gerlach(ProofGraph *g);

/* Compute layout positions for all nodes given canvas area */
void graph_layout(ProofGraph *g, Rectangle area);

/* Navigation */
void graph_step_forward(ProofGraph *g);
void graph_step_back(ProofGraph *g);
void graph_reset(ProofGraph *g);

/* Query highlight state */
int graph_is_active(const ProofGraph *g, int node_id);
int graph_is_dependency(const ProofGraph *g, int node_id);

/* Get the currently active node */
const ProofNode *graph_current_node(const ProofGraph *g);

/* Get the bounding rectangle for a node (for click detection) */
Rectangle graph_node_bounds(const ProofGraph *g, int node_id);

/* Draw the proof graph */
void graph_draw(const ProofGraph *g);

/* Draw the info panel for the current node (layered descriptions) */
void graph_draw_info_panel(const ProofGraph *g, Rectangle panel);

/* Draw the step indicator at the bottom */
void graph_draw_step_bar(const ProofGraph *g, Rectangle bar);

/* Draw overview panel showing proof structure summary (#228) */
void graph_draw_overview(const ProofGraph *g, Rectangle panel);

/* Toggle angle-dependent node emphasis (#229) */
void graph_toggle_angle_highlight(ProofGraph *g);

/* Toggle overview mode (#228) */
void graph_toggle_overview(ProofGraph *g);

/* #261 HVR (beekeeper, 2026-10-22): the info panel must never crowd the graph.
 * One shared layout: graph region on the left, panel on the right, computed
 * from the screen size and the panel state; the scenes no longer hardcode it.
 * graph_layout_regions() returns both rectangles (panel is zero-width when hidden);
 * graph_toggle_panel() flips the panel and RE-LAYS-OUT the graph into the new region. */
#define QBP_PANEL_WIDTH   360   /* was 440: ~40% of an 1100-px window read as "half the view" */
#define QBP_BAR_HEIGHT     56
#define QBP_TITLE_HEIGHT   60
void graph_layout_regions(const ProofGraph *g, int sw, int sh, Rectangle *graph_area, Rectangle *panel);
void graph_toggle_panel(ProofGraph *g, int sw, int sh);

/* Check if a node has a specific tag */
int graph_node_has_tag(const ProofNode *n, const char *tag);

/* Viewport control for pan/zoom */
void graph_viewport_init(ProofGraph *g);
void graph_viewport_update(ProofGraph *g);  /* Call each frame to handle input */
void graph_pan(ProofGraph *g, float dx, float dy);
void graph_zoom(ProofGraph *g, float delta, Vector2 focus);
void graph_reset_viewport(ProofGraph *g);

#endif /* QBP_PROOF_GRAPH_H */
