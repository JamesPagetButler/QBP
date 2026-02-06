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
#define MAX_NODES 16
#define MAX_NAME_LEN 64
#define MAX_DISPLAY_NAME_LEN 128
#define MAX_FORMAL_LEN 256
#define MAX_MATH_LEN 256
#define MAX_PHYSICAL_LEN 512
#define MAX_INTUITIVE_LEN 512
#define MAX_INSIGHT_LEN 256

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
} ProofNode;

typedef struct {
    ProofNode   nodes[MAX_NODES];
    int         node_count;
    int         walk_order[MAX_NODES]; /* order to visit nodes in walkthrough */
    int         walk_len;
    int         current_step;          /* 0-based index into walk_order */
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

#endif /* QBP_PROOF_GRAPH_H */
