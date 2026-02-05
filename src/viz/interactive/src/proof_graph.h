/*
 * proof_graph.h — Proof dependency tree for interactive visualization.
 *
 * Each ProofNode represents a theorem/definition from the Lean proofs.
 * The tree is navigated step-by-step, highlighting the active node
 * and its dependencies at each step.
 */

#ifndef QBP_PROOF_GRAPH_H
#define QBP_PROOF_GRAPH_H

#include "raylib.h"

#define MAX_DEPS 6
#define MAX_NODES 16
#define MAX_NAME_LEN 64
#define MAX_STATEMENT_LEN 256
#define MAX_MEANING_LEN 256

typedef enum {
    NODE_AXIOM,
    NODE_DEFINITION,
    NODE_THEOREM
} NodeKind;

typedef struct {
    int         id;
    char        name[MAX_NAME_LEN];
    char        statement[MAX_STATEMENT_LEN];
    char        physical_meaning[MAX_MEANING_LEN];
    NodeKind    kind;
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

/* Draw the proof graph */
void graph_draw(const ProofGraph *g);

/* Draw the info panel for the current node */
void graph_draw_info_panel(const ProofGraph *g, Rectangle panel);

/* Draw the step indicator at the bottom */
void graph_draw_step_bar(const ProofGraph *g, Rectangle bar);

#endif /* QBP_PROOF_GRAPH_H */
