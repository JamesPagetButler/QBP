/*
 * proof_graph.c — Proof dependency tree for Stern-Gerlach experiment.
 *
 * The graph is hardcoded from:
 *   proofs/QBP/Basic.lean
 *   proofs/QBP/Experiments/SternGerlach.lean
 *
 * Each node has 4 levels of description:
 *   L4 (Formal):      Lean syntax
 *   L3 (Mathematical): Conventional notation
 *   L2 (Physical):     Physics interpretation
 *   L1 (Intuitive):    Plain English (NYT readers)
 */

#include "proof_graph.h"
#include "theme.h"
#include "fonts.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ------------------------------------------------------------------ */
/*  Node IDs — 13 nodes for the Stern-Gerlach proof chain             */
/* ------------------------------------------------------------------ */
enum {
    N_IS_PURE = 0,       /* isPureQuaternion — def */
    N_VEC_DOT,           /* vecDot — def */
    N_SPIN_X_PURE,       /* spin_x_is_pure — thm */
    N_SPIN_Z_PURE,       /* spin_z_is_pure — thm */
    N_SG_STATE,          /* spinXState — def */
    N_SG_OBS,            /* spinZObservable — def */
    N_SG_STATE_IS_PURE,  /* spinXState_is_pure — thm */
    N_SG_OBS_IS_PURE,    /* spinZObservable_is_pure — thm */
    N_X_Z_ORTHO,         /* x_z_orthogonal — thm */
    N_EXP_ORTHO_ZERO,    /* expectation_orthogonal_is_zero — thm */
    N_EXP_XZ_ZERO,       /* expectation_x_measured_z_is_zero — thm */
    N_PROB_UP,           /* prob_up_x_measured_z_is_half — thm */
    N_PROB_DOWN,         /* prob_down_x_measured_z_is_half — thm */
    N_COUNT              /* = 13 */
};

/* Helper to add a node with all 4 description levels */
static void add_node(ProofGraph *g, int id,
                     const char *name, const char *display_name, NodeKind kind,
                     const char *l4_formal, const char *l3_math,
                     const char *l2_physical, const char *l1_intuitive,
                     const char *insight,
                     const int *deps, int dep_count)
{
    ProofNode *n = &g->nodes[id];
    n->id = id;
    n->kind = kind;
    snprintf(n->name, MAX_NAME_LEN, "%s", name);
    snprintf(n->display_name, MAX_DISPLAY_NAME_LEN, "%s", display_name);
    snprintf(n->level4_formal, MAX_FORMAL_LEN, "%s", l4_formal);
    snprintf(n->level3_math, MAX_MATH_LEN, "%s", l3_math);
    snprintf(n->level2_physical, MAX_PHYSICAL_LEN, "%s", l2_physical);
    snprintf(n->level1_intuitive, MAX_INTUITIVE_LEN, "%s", l1_intuitive);
    snprintf(n->key_insight, MAX_INSIGHT_LEN, "%s", insight);
    n->dep_count = dep_count;
    for (int i = 0; i < dep_count; i++) n->deps[i] = deps[i];
}

/*
 * DEPRECATED: Use graph_load_json() from json_loader.h instead.
 *
 * This hardcoded initialization is kept as a fallback during the
 * transition to data-driven loading. Once JSON loading is proven
 * stable, this function should be removed.
 *
 * See: data/stern_gerlach.viz.json for the data-driven version.
 */
void graph_init_stern_gerlach(ProofGraph *g)
{
    memset(g, 0, sizeof(*g));
    g->node_count = N_COUNT;

    /* ================================================================ */
    /*  NODE 1: isPureQuaternion                                        */
    /* ================================================================ */
    add_node(g, N_IS_PURE,
        "isPureQuaternion",
        "Pure Quaternion Definition",
        NODE_DEFINITION,
        /* L4 Formal */
        "def isPureQuaternion (q : H) : Prop := q.re = 0",
        /* L3 Mathematical */
        "A quaternion q = a + bi + cj + dk is pure iff a = 0",
        /* L2 Physical */
        "Pure quaternions represent physical directions in 3D space. "
        "They're the 'arrows' we use to describe spin orientations "
        "and measurement axes.",
        /* L1 Intuitive */
        "Think of a pure quaternion as a 3D arrow with no 'extra "
        "dimension.' It's the mathematical way to point in a direction "
        "- like pointing your finger at something in the room.",
        /* Key Insight */
        "Pure quaternions are directions, not scalars.",
        NULL, 0);

    /* ================================================================ */
    /*  NODE 2: vecDot                                                  */
    /* ================================================================ */
    add_node(g, N_VEC_DOT,
        "vecDot",
        "Vector Dot Product",
        NODE_DEFINITION,
        /* L4 Formal */
        "def vecDot (a b : H) : R := a.imI*b.imI + a.imJ*b.imJ + a.imK*b.imK",
        /* L3 Mathematical */
        "<a, b> = a_i*b_i + a_j*b_j + a_k*b_k  (Euclidean inner product)",
        /* L2 Physical */
        "Measures how aligned two directions are. Zero means perpendicular; "
        "maximum means parallel. This is the key to determining quantum "
        "measurement probabilities.",
        /* L1 Intuitive */
        "The dot product asks: 'How much do these two arrows point the "
        "same way?' If they're at right angles, the answer is zero. If "
        "they point the same direction, it's maximum.",
        /* Key Insight */
        "Alignment between state and measurement determines randomness.",
        NULL, 0);

    /* ================================================================ */
    /*  NODE 3: spin_x_is_pure                                          */
    /* ================================================================ */
    {
        int deps[] = { N_IS_PURE };
        add_node(g, N_SPIN_X_PURE,
            "spin_x_is_pure",
            "X-Axis is a Valid Direction",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl",
            /* L3 Mathematical */
            "Re(i) = 0, confirming SPIN_X = i is pure",
            /* L2 Physical */
            "The x-direction is a legitimate physical direction - it "
            "lives purely in 3D space with no scalar component.",
            /* L1 Intuitive */
            "'Pointing along the x-axis' is a valid direction in space. "
            "Nothing exotic here - just confirming our sideways direction "
            "is well-defined.",
            /* Key Insight */
            "The x-axis is a proper direction for spin.",
            deps, 1);
    }

    /* ================================================================ */
    /*  NODE 4: spin_z_is_pure                                          */
    /* ================================================================ */
    {
        int deps[] = { N_IS_PURE };
        add_node(g, N_SPIN_Z_PURE,
            "spin_z_is_pure",
            "Z-Axis is a Valid Direction",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem spin_z_is_pure : isPureQuaternion SPIN_Z := rfl",
            /* L3 Mathematical */
            "Re(k) = 0, confirming SPIN_Z = k is pure",
            /* L2 Physical */
            "The z-direction is a legitimate physical direction - it "
            "lives purely in 3D space with no scalar component.",
            /* L1 Intuitive */
            "'Pointing up' (along the z-axis) is a valid direction in "
            "space. We're confirming our vertical axis is well-defined.",
            /* Key Insight */
            "The z-axis (vertical) is a proper direction for measurement.",
            deps, 1);
    }

    /* ================================================================ */
    /*  NODE 5: spinXState                                              */
    /* ================================================================ */
    add_node(g, N_SG_STATE,
        "spinXState",
        "The Particle's State: Spin-X",
        NODE_DEFINITION,
        /* L4 Formal */
        "def spinXState : H := SPIN_X  -- the quaternion i",
        /* L3 Mathematical */
        "|psi_x> = i = <0, 1, 0, 0>, spin-up eigenstate along x-axis",
        /* L2 Physical */
        "A particle prepared with its spin pointing along the positive "
        "x-axis. If you measured it along x, it would definitely give 'up.'",
        /* L1 Intuitive */
        "Imagine a tiny compass needle pointing firmly to the right. "
        "This is our particle's spin state - it's committed to the "
        "x-direction, like a stubborn arrow pointing sideways.",
        /* Key Insight */
        "The particle 'knows' it's pointing right (x-direction).",
        NULL, 0);

    /* ================================================================ */
    /*  NODE 6: spinZObservable                                         */
    /* ================================================================ */
    add_node(g, N_SG_OBS,
        "spinZObservable",
        "The Detector: Measuring Z",
        NODE_DEFINITION,
        /* L4 Formal */
        "def spinZObservable : H := SPIN_Z  -- the quaternion k",
        /* L3 Mathematical */
        "O_z = k = <0, 0, 0, 1>, spin measurement along z-axis",
        /* L2 Physical */
        "A measuring device oriented vertically. It asks the particle: "
        "'Is your spin pointing up or down along the z-axis?'",
        /* L1 Intuitive */
        "Picture a detector that only cares about vertical: 'Are you "
        "pointing up toward the ceiling, or down toward the floor?' "
        "It can't ask about sideways - only up or down.",
        /* Key Insight */
        "The detector asks 'up or down?' - not 'left or right?'",
        NULL, 0);

    /* ================================================================ */
    /*  NODE 7: spinXState_is_pure                                      */
    /* ================================================================ */
    {
        int deps[] = { N_SG_STATE, N_SPIN_X_PURE };
        add_node(g, N_SG_STATE_IS_PURE,
            "spinXState_is_pure",
            "Spin-X State is Valid",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem spinXState_is_pure : isPureQuaternion spinXState := spin_x_is_pure",
            /* L3 Mathematical */
            "Re(|psi_x>) = 0, the state vector has no scalar part",
            /* L2 Physical */
            "The spin-x state represents a genuine direction in physical "
            "space - it's a valid quantum state we can prepare in the lab.",
            /* L1 Intuitive */
            "Our 'pointing right' state is mathematically well-formed. "
            "It's a proper arrow, not something weird or broken. We can "
            "actually create particles in this state.",
            /* Key Insight */
            "The state we're testing is legitimate.",
            deps, 2);
    }

    /* ================================================================ */
    /*  NODE 8: spinZObservable_is_pure                                 */
    /* ================================================================ */
    {
        int deps[] = { N_SG_OBS, N_SPIN_Z_PURE };
        add_node(g, N_SG_OBS_IS_PURE,
            "spinZObservable_is_pure",
            "Z-Measurement is Valid",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem spinZObservable_is_pure : isPureQuaternion spinZObservable := spin_z_is_pure",
            /* L3 Mathematical */
            "Re(O_z) = 0, the observable has no scalar part",
            /* L2 Physical */
            "The z-measurement axis represents a genuine direction in "
            "physical space - it's a valid observable we can measure.",
            /* L1 Intuitive */
            "Our 'vertical detector' is mathematically well-formed. It "
            "measures a real direction in space - up versus down. This "
            "is a legitimate question to ask of a particle.",
            /* Key Insight */
            "The measurement we're doing is legitimate.",
            deps, 2);
    }

    /* ================================================================ */
    /*  NODE 9: x_z_orthogonal                                          */
    /* ================================================================ */
    {
        int deps[] = { N_VEC_DOT, N_SG_STATE, N_SG_OBS };
        add_node(g, N_X_Z_ORTHO,
            "x_z_orthogonal",
            "X and Z are Perpendicular",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0",
            /* L3 Mathematical */
            "<psi_x | O_z> = <i, k> = 0 (orthogonal vectors)",
            /* L2 Physical */
            "The x-direction and z-direction are perpendicular. A "
            "particle pointing along x has no component along z - it's "
            "neither 'up' nor 'down', it's exactly in between.",
            /* L1 Intuitive */
            "Right and up are at right angles. If you're pointing "
            "sideways, you're not pointing up or down - you're exactly "
            "in between. Like asking someone facing East: 'Are you "
            "facing North or South?' Neither!",
            /* Key Insight */
            "Perpendicular directions share no information.",
            deps, 3);
    }

    /* ================================================================ */
    /*  NODE 10: expectation_orthogonal_is_zero                         */
    /* ================================================================ */
    {
        int deps[] = { N_IS_PURE, N_VEC_DOT };
        add_node(g, N_EXP_ORTHO_ZERO,
            "expectation_orthogonal_is_zero",
            "Perpendicular Means Zero Average",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem expectation_orthogonal_is_zero (psi O : H) :\n"
            "  vecDot psi O = 0 -> expectationValue psi O = 0",
            /* L3 Mathematical */
            "<psi|O> = 0  =>  <O>_psi = 0  (orthogonality implies zero expectation)",
            /* L2 Physical */
            "When a quantum state is perpendicular to a measurement axis, "
            "the average outcome is zero - neither +1 nor -1 dominates. "
            "This is a general principle of quantum mechanics.",
            /* L1 Intuitive */
            "If you're pointing sideways and I ask 'are you pointing up "
            "or down?', the fairest answer is 'equally up and down' - "
            "averaging to zero. You have no preference either way.",
            /* Key Insight */
            "No alignment means no bias in the measurement.",
            deps, 2);
    }

    /* ================================================================ */
    /*  NODE 11: expectation_x_measured_z_is_zero                       */
    /* ================================================================ */
    {
        int deps[] = { N_EXP_ORTHO_ZERO, N_SG_STATE_IS_PURE, N_SG_OBS_IS_PURE, N_X_Z_ORTHO };
        add_node(g, N_EXP_XZ_ZERO,
            "expectation_x_measured_z_is_zero",
            "Average Measurement is Zero",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem expectation_x_measured_z_is_zero :\n"
            "  expectationValue spinXState spinZObservable = 0",
            /* L3 Mathematical */
            "<O_z>_{psi_x} = 0, applying the general theorem to our specific case",
            /* L2 Physical */
            "When you measure a spin-x particle along z, the results "
            "are +1 and -1 with equal frequency. The average is zero - "
            "no bias toward 'up' or 'down'.",
            /* L1 Intuitive */
            "Our rightward-pointing particle, when asked 'up or down?', "
            "has absolutely no preference. If you measured a million "
            "particles, you'd get equal numbers of 'up' and 'down' answers. "
            "The particle genuinely doesn't know!",
            /* Key Insight */
            "The particle has no information about up vs. down.",
            deps, 4);
    }

    /* ================================================================ */
    /*  NODE 12: prob_up_x_measured_z_is_half                           */
    /* ================================================================ */
    {
        int deps[] = { N_EXP_XZ_ZERO };
        add_node(g, N_PROB_UP,
            "prob_up_x_measured_z_is_half",
            "50% Chance of 'Up'",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem prob_up_x_measured_z_is_half :\n"
            "  probUp spinXState spinZObservable = 1/2",
            /* L3 Mathematical */
            "P(+1 | psi_x, O_z) = 1/2, from the Born rule: P(+) = (1 + <O>)/2",
            /* L2 Physical */
            "A spin-x particle measured along z has exactly 50% chance "
            "of registering 'spin-up'. Not approximately - exactly.",
            /* L1 Intuitive */
            "The coin flip: point sideways, ask 'up or down?' - exactly "
            "half the time, the answer is 'up.' This isn't fuzzy or "
            "approximate. The math proves it's precisely 50%, every time, "
            "forever.",
            /* Key Insight */
            "Quantum randomness is mathematically perfect.",
            deps, 1);
    }

    /* ================================================================ */
    /*  NODE 13: prob_down_x_measured_z_is_half                         */
    /* ================================================================ */
    {
        int deps[] = { N_EXP_XZ_ZERO };
        add_node(g, N_PROB_DOWN,
            "prob_down_x_measured_z_is_half",
            "50% Chance of 'Down'",
            NODE_THEOREM,
            /* L4 Formal */
            "theorem prob_down_x_measured_z_is_half :\n"
            "  probDown spinXState spinZObservable = 1/2",
            /* L3 Mathematical */
            "P(-1 | psi_x, O_z) = 1/2, from the Born rule: P(-) = (1 - <O>)/2",
            /* L2 Physical */
            "A spin-x particle measured along z has exactly 50% chance "
            "of registering 'spin-down'. Combined with spin-up, that's 100%.",
            /* L1 Intuitive */
            "The other side of the coin: the remaining half of the time, "
            "the answer is 'down.' Together with 'up', that's 100%. "
            "We've just proven that quantum mechanics forces a perfect "
            "50/50 split - not by experiment, but by pure logic.",
            /* Key Insight */
            "Logic alone proves the 50/50 split - no experiments needed.",
            deps, 1);
    }

    /* Walk order: bottom-up through the proof tree */
    int order[] = {
        N_IS_PURE, N_VEC_DOT,
        N_SPIN_X_PURE, N_SPIN_Z_PURE,
        N_SG_STATE, N_SG_OBS,
        N_SG_STATE_IS_PURE, N_SG_OBS_IS_PURE,
        N_X_Z_ORTHO, N_EXP_ORTHO_ZERO,
        N_EXP_XZ_ZERO, N_PROB_UP, N_PROB_DOWN
    };
    g->walk_len = N_COUNT;
    for (int i = 0; i < N_COUNT; i++) g->walk_order[i] = order[i];
    g->current_step = 0;
}

/* ------------------------------------------------------------------ */
/*  Layout: position nodes in a logical tree arrangement              */
/* ------------------------------------------------------------------ */
/*
 * LIMITATION: This layout is hardcoded for the Stern-Gerlach experiment.
 *
 * The node positions are manually specified for the 13-node proof tree.
 * Adding new experiments will require either:
 *   1. Adding experiment-specific layout code, OR
 *   2. Generalizing to automatic layout (topological sort + level assignment)
 *
 * Phase 4c should address this with a proper graph layout algorithm that
 * derives positions from the dependency structure automatically.
 *
 * See GitHub issue for details on planned improvements.
 */

/*
 * Automatic graph layout using topological levels.
 *
 * Algorithm:
 * 1. Compute "level" for each node (longest path from any root)
 *    - Roots (nodes with no dependencies) get level 0
 *    - Each node's level = max(dependency levels) + 1
 *    - Uses fixed-point iteration: repeat until no levels change
 *
 * 2. Group nodes by level and assign horizontal index within level
 *
 * 3. Distribute nodes:
 *    - Vertically: evenly spaced rows, one per level (roots at top)
 *    - Horizontally: centered within row, evenly spaced
 *    - Formula: x = area_x + area_width * (index + 0.5) / count_at_level
 *
 * Example with 5 nodes (A,B depend on nothing; C depends on A; D,E depend on C):
 *
 *     Level 0:  [A]     [B]      <- roots, 2 nodes, each at 1/4 and 3/4 width
 *     Level 1:      [C]          <- 1 node, centered at 1/2 width
 *     Level 2:  [D]     [E]      <- 2 nodes, at 1/4 and 3/4 width
 *
 * This enables new experiments to be visualized without hardcoded positions.
 */
/* Forward declaration for calc_node_width */
static float calc_node_width(const ProofNode *n);

/* Barycenter pair for qsort-based ordering (replaces O(n²) bubble sort) */
typedef struct { float bc; int node_id; } BcPair;

static int cmp_bc_pair(const void *a, const void *b) {
    float fa = ((const BcPair *)a)->bc;
    float fb = ((const BcPair *)b)->bc;
    /* NaN-safe: treat NaN as +∞ so qsort gets a total order */
    if (isnan(fa)) return isnan(fb) ? 0 : 1;
    if (isnan(fb)) return -1;
    return (fa > fb) - (fa < fb);
}

void graph_layout(ProofGraph *g, Rectangle area)
{
    if (g->node_count == 0) return;

    /* Store view area for viewport calculations */
    g->view_area = area;

    /* Step 1: Compute levels using longest-path from roots */
    int levels[MAX_NODES] = {0};
    int max_level = 0;

    for (int iter = 0; iter < g->node_count; iter++) {
        for (int i = 0; i < g->node_count; i++) {
            ProofNode *n = &g->nodes[i];
            for (int d = 0; d < n->dep_count; d++) {
                int dep_id = n->deps[d];
                if (dep_id >= 0 && dep_id < g->node_count) {
                    if (levels[i] <= levels[dep_id]) {
                        levels[i] = levels[dep_id] + 1;
                    }
                }
            }
            if (levels[i] > max_level) max_level = levels[i];
        }
    }

    /* Step 2: Collect nodes per level and compute actual widths needed */
    int level_counts[MAX_NODES] = {0};
    int nodes_at_level[MAX_NODES][MAX_NODES];
    float level_widths[MAX_NODES] = {0};  /* Total width needed per level */

    #define NODE_H 44
    #define NODE_MARGIN 20  /* Minimum gap between nodes */

    for (int i = 0; i < g->node_count; i++) {
        int lvl = levels[i];
        nodes_at_level[lvl][level_counts[lvl]] = i;
        level_counts[lvl]++;
    }

    /* Compute required width for each level (sum of node widths + margins) */
    for (int lvl = 0; lvl <= max_level; lvl++) {
        float total = 0;
        for (int idx = 0; idx < level_counts[lvl]; idx++) {
            int node_id = nodes_at_level[lvl][idx];
            total += calc_node_width(&g->nodes[node_id]) + NODE_MARGIN;
        }
        level_widths[lvl] = total;
    }

    /* Find max width needed across all levels */
    float max_width_needed = area.width;
    for (int lvl = 0; lvl <= max_level; lvl++) {
        if (level_widths[lvl] > max_width_needed) {
            max_width_needed = level_widths[lvl];
        }
    }

    /* Compute required height */
    float row_height = NODE_H + 40;  /* Node height + vertical gap */
    float total_height_needed = row_height * (max_level + 1) + 40;
    if (total_height_needed < area.height) {
        total_height_needed = area.height;
    }

    /* Store graph bounds (the virtual canvas size) */
    g->graph_bounds = (Rectangle){
        0, 0,
        max_width_needed + 40,  /* Add padding */
        total_height_needed
    };

    /* Step 3: Position nodes with barycenter ordering, NO OVERLAP */
    float center_x = g->graph_bounds.width / 2.0f;

    /* Position level 0 first */
    if (level_counts[0] > 0) {
        float total_w = level_widths[0];
        float start_x = center_x - total_w / 2.0f;
        float cur_x = start_x;
        for (int idx = 0; idx < level_counts[0]; idx++) {
            int node_id = nodes_at_level[0][idx];
            float nw = calc_node_width(&g->nodes[node_id]);
            g->nodes[node_id].pos = (Vector2){
                cur_x + nw / 2.0f,
                row_height * 0.5f + 20
            };
            cur_x += nw + NODE_MARGIN;
        }
    }

    /* Position subsequent levels with barycenter ordering */
    for (int lvl = 1; lvl <= max_level; lvl++) {
        int count = level_counts[lvl];
        if (count == 0) continue;

        /* Compute barycenter for each node */
        float barycenters[MAX_NODES];
        for (int idx = 0; idx < count; idx++) {
            int node_id = nodes_at_level[lvl][idx];
            ProofNode *n = &g->nodes[node_id];

            if (n->dep_count == 0) {
                barycenters[idx] = center_x;
            } else {
                float sum_x = 0;
                for (int d = 0; d < n->dep_count; d++) {
                    sum_x += g->nodes[n->deps[d]].pos.x;
                }
                barycenters[idx] = sum_x / (float)n->dep_count;
            }
        }

        /* Sort by barycenter using paired sort (O(n log n) via qsort) */
        BcPair bc_pairs[MAX_NODES];
        for (int i = 0; i < count; i++) {
            bc_pairs[i].bc = barycenters[i];
            bc_pairs[i].node_id = nodes_at_level[lvl][i];
        }
        qsort(bc_pairs, (size_t)count, sizeof(BcPair), cmp_bc_pair);
        for (int i = 0; i < count; i++) {
            barycenters[i] = bc_pairs[i].bc;
            nodes_at_level[lvl][i] = bc_pairs[i].node_id;
        }

        /* Position nodes - compute total width first */
        float total_w = level_widths[lvl];
        float start_x = center_x - total_w / 2.0f;
        float cur_x = start_x;
        for (int idx = 0; idx < count; idx++) {
            int node_id = nodes_at_level[lvl][idx];
            float nw = calc_node_width(&g->nodes[node_id]);
            g->nodes[node_id].pos = (Vector2){
                cur_x + nw / 2.0f,
                row_height * ((float)lvl + 0.5f) + 20
            };
            cur_x += nw + NODE_MARGIN;
        }
    }

    #undef NODE_H
    #undef NODE_MARGIN
}

/* ------------------------------------------------------------------ */
/*  Viewport control for pan/zoom                                     */
/* ------------------------------------------------------------------ */

void graph_viewport_init(ProofGraph *g)
{
    g->viewport_x = 0;
    g->viewport_y = 0;
    g->viewport_zoom = 1.0f;
}

void graph_reset_viewport(ProofGraph *g)
{
    g->viewport_x = 0;
    g->viewport_y = 0;
    g->viewport_zoom = 1.0f;
}

void graph_pan(ProofGraph *g, float dx, float dy)
{
    g->viewport_x += dx;
    g->viewport_y += dy;

    /* Clamp to graph bounds */
    float max_pan_x = g->graph_bounds.width - g->view_area.width / g->viewport_zoom;
    float max_pan_y = g->graph_bounds.height - g->view_area.height / g->viewport_zoom;

    if (max_pan_x < 0) max_pan_x = 0;
    if (max_pan_y < 0) max_pan_y = 0;

    if (g->viewport_x < 0) g->viewport_x = 0;
    if (g->viewport_y < 0) g->viewport_y = 0;
    if (g->viewport_x > max_pan_x) g->viewport_x = max_pan_x;
    if (g->viewport_y > max_pan_y) g->viewport_y = max_pan_y;
}

void graph_zoom(ProofGraph *g, float delta, Vector2 focus)
{
    float old_zoom = g->viewport_zoom;
    g->viewport_zoom += delta * 0.1f;

    /* Clamp zoom */
    if (g->viewport_zoom < 0.5f) g->viewport_zoom = 0.5f;
    if (g->viewport_zoom > 2.0f) g->viewport_zoom = 2.0f;

    /* Adjust pan to keep focus point stable */
    float zoom_ratio = g->viewport_zoom / old_zoom;
    float focus_graph_x = g->viewport_x + (focus.x - g->view_area.x) / old_zoom;
    float focus_graph_y = g->viewport_y + (focus.y - g->view_area.y) / old_zoom;

    g->viewport_x = focus_graph_x - (focus.x - g->view_area.x) / g->viewport_zoom;
    g->viewport_y = focus_graph_y - (focus.y - g->view_area.y) / g->viewport_zoom;

    /* Re-clamp after zoom */
    graph_pan(g, 0, 0);
}

void graph_viewport_update(ProofGraph *g)
{
    Vector2 mouse = GetMousePosition();

    /* Only handle viewport input when mouse is in graph area */
    if (!CheckCollisionPointRec(mouse, g->view_area)) return;

    /* Mouse wheel: vertical scroll (Shift+wheel for horizontal) */
    float wheel = GetMouseWheelMove();
    if (wheel != 0) {
        if (IsKeyDown(KEY_LEFT_CONTROL) || IsKeyDown(KEY_RIGHT_CONTROL)) {
            /* Ctrl+wheel = zoom */
            graph_zoom(g, wheel, mouse);
        } else if (IsKeyDown(KEY_LEFT_SHIFT) || IsKeyDown(KEY_RIGHT_SHIFT)) {
            /* Shift+wheel = horizontal scroll */
            graph_pan(g, -wheel * 40.0f / g->viewport_zoom, 0);
        } else {
            /* Wheel = vertical scroll */
            graph_pan(g, 0, -wheel * 40.0f / g->viewport_zoom);
        }
    }

    /* Middle mouse drag for pan */
    if (IsMouseButtonDown(MOUSE_BUTTON_MIDDLE)) {
        Vector2 delta = GetMouseDelta();
        graph_pan(g, -delta.x / g->viewport_zoom, -delta.y / g->viewport_zoom);
    }
}

/* ------------------------------------------------------------------ */
/*  Navigation                                                        */
/* ------------------------------------------------------------------ */

void graph_step_forward(ProofGraph *g)
{
    if (g->current_step < g->walk_len - 1) g->current_step++;
}

void graph_step_back(ProofGraph *g)
{
    if (g->current_step > 0) g->current_step--;
}

void graph_reset(ProofGraph *g)
{
    g->current_step = 0;
}

int graph_is_active(const ProofGraph *g, int node_id)
{
    return g->walk_order[g->current_step] == node_id;
}

int graph_is_dependency(const ProofGraph *g, int node_id)
{
    int active_id = g->walk_order[g->current_step];
    const ProofNode *active = &g->nodes[active_id];
    for (int i = 0; i < active->dep_count; i++) {
        if (active->deps[i] == node_id) return 1;
    }
    return 0;
}

const ProofNode *graph_current_node(const ProofGraph *g)
{
    return &g->nodes[g->walk_order[g->current_step]];
}

/* ------------------------------------------------------------------ */
/*  Drawing                                                           */
/* ------------------------------------------------------------------ */

/* Node sizes - balanced for readability and fit */
#define NODE_MIN_W  140
#define NODE_H       44
#define FONT_SZ      14
#define BADGE_W      36
#define NODE_PAD     10  /* padding on each side of text */

/* Calculate node width based on display name text */
static float calc_node_width(const ProofNode *n)
{
    int text_w = MeasureTextQBP(n->display_name, FONT_SZ);
    float total_w = BADGE_W + NODE_PAD + text_w + NODE_PAD;
    return (total_w < NODE_MIN_W) ? NODE_MIN_W : total_w;
}

/* Get node rectangle in graph coordinates (before viewport transform) */
static Rectangle node_rect_graph(const ProofNode *n)
{
    float w = calc_node_width(n);
    return (Rectangle){
        n->pos.x - w/2.0f,
        n->pos.y - NODE_H/2.0f,
        w, NODE_H
    };
}

/* Transform graph coordinates to screen coordinates */
static Vector2 graph_to_screen(const ProofGraph *g, Vector2 pos)
{
    return (Vector2){
        g->view_area.x + (pos.x - g->viewport_x) * g->viewport_zoom,
        g->view_area.y + (pos.y - g->viewport_y) * g->viewport_zoom
    };
}

/* Transform screen coordinates to graph coordinates */
static Vector2 screen_to_graph(const ProofGraph *g, Vector2 pos)
{
    return (Vector2){
        g->viewport_x + (pos.x - g->view_area.x) / g->viewport_zoom,
        g->viewport_y + (pos.y - g->view_area.y) / g->viewport_zoom
    };
}

/* Get node rectangle in screen coordinates */
static Rectangle node_rect_screen(const ProofGraph *g, const ProofNode *n)
{
    Rectangle r = node_rect_graph(n);
    Vector2 top_left = graph_to_screen(g, (Vector2){r.x, r.y});
    return (Rectangle){
        top_left.x, top_left.y,
        r.width * g->viewport_zoom,
        r.height * g->viewport_zoom
    };
}

/* Public function for click detection (returns screen coordinates) */
Rectangle graph_node_bounds(const ProofGraph *g, int node_id)
{
    return node_rect_screen(g, &g->nodes[node_id]);
}

int graph_node_has_tag(const ProofNode *n, const char *tag)
{
    if (!n || !tag || n->tags[0] == '\0') return 0;
    const char *p = n->tags;
    int tag_len = (int)strlen(tag);
    while (*p) {
        if (strncmp(p, tag, tag_len) == 0 &&
            (p[tag_len] == ',' || p[tag_len] == '\0')) {
            return 1;
        }
        /* Skip to next comma */
        while (*p && *p != ',') p++;
        if (*p == ',') p++;
    }
    return 0;
}

static Color node_color(const ProofGraph *g, int id)
{
    /* Angle highlight mode: dim non-angle nodes */
    if (g->angle_highlight && !g->nodes[id].has_tag_angle) {
        if (graph_is_active(g, id)) return QBP_VERDIGRIS;
        return QBP_ANGLE_DIM;
    }
    if (g->angle_highlight && g->nodes[id].has_tag_angle) {
        if (graph_is_active(g, id)) return QBP_ANGLE_GLOW;
        return QBP_GOLD;
    }
    if (graph_is_active(g, id))     return QBP_NODE_ACTIVE;
    if (graph_is_dependency(g, id)) return QBP_NODE_DEP;
    for (int s = 0; s < g->current_step; s++) {
        if (g->walk_order[s] == id) return QBP_VERDIGRIS;
    }
    return QBP_NODE_IDLE;
}

static Color kind_badge_color(NodeKind kind)
{
    switch (kind) {
        case NODE_AXIOM:      return QBP_CRIMSON;
        case NODE_DEFINITION: return QBP_AMBER;
        case NODE_THEOREM:    return QBP_TEAL;
        default:              return QBP_STEEL;
    }
}

static const char *kind_label(NodeKind kind)
{
    switch (kind) {
        case NODE_AXIOM:      return "AXM";
        case NODE_DEFINITION: return "DEF";
        case NODE_THEOREM:    return "THM";
        default:              return "???";
    }
}

void graph_draw(const ProofGraph *g)
{
    /* Set up scissor to clip drawing to view area */
    BeginScissorMode((int)g->view_area.x, (int)g->view_area.y,
                     (int)g->view_area.width, (int)g->view_area.height);

    /* Draw scroll indicator background */
    DrawRectangleRec(g->view_area, QBP_BG);

    float zoom = g->viewport_zoom;
    int scaled_font = (int)(FONT_SZ * zoom);
    if (scaled_font < 8) scaled_font = 8;
    int scaled_badge_font = (int)(12 * zoom);
    if (scaled_badge_font < 6) scaled_badge_font = 6;

    /* Draw edges first (behind nodes) */
    for (int i = 0; i < g->node_count; i++) {
        const ProofNode *n = &g->nodes[i];
        for (int d = 0; d < n->dep_count; d++) {
            const ProofNode *dep = &g->nodes[n->deps[d]];
            Color c = QBP_STEEL;
            if (graph_is_active(g, i) && graph_is_dependency(g, n->deps[d])) {
                c = QBP_EDGE;
            }
            Vector2 p1 = graph_to_screen(g, dep->pos);
            Vector2 p2 = graph_to_screen(g, n->pos);
            DrawLineEx(p1, p2, 2.0f * zoom, c);
        }
    }

    /* Draw nodes */
    for (int i = 0; i < g->node_count; i++) {
        const ProofNode *n = &g->nodes[i];
        Rectangle r = node_rect_screen(g, n);
        Color bg = node_color(g, i);

        DrawRectangleRounded(r, 0.3f, 8, bg);
        DrawRectangleRoundedLinesEx(r, 0.3f, 8, 1.5f * zoom, QBP_BRASS);

        /* Kind badge */
        Color badge = kind_badge_color(n->kind);
        float badge_w = BADGE_W * zoom;
        Rectangle br = { r.x + 3*zoom, r.y + 3*zoom, badge_w, r.height - 6*zoom };
        DrawRectangleRounded(br, 0.3f, 4, badge);
        DrawTextQBP(kind_label(n->kind),
                 (int)(br.x + 4*zoom), (int)(br.y + (br.height - scaled_badge_font)/2),
                 scaled_badge_font, QBP_IVORY);

        /* Node display name (short, readable) */
        int text_x = (int)(r.x + badge_w + NODE_PAD*zoom/2);
        int text_y = (int)(r.y + (r.height - scaled_font) / 2);
        DrawTextQBP(n->display_name, text_x, text_y, scaled_font, QBP_TEXT_PRIMARY);
    }

    /* Draw scroll indicators if content extends beyond view */
    Color indicator = (Color){255, 255, 255, 60};
    float view_w = g->view_area.width;
    float view_h = g->view_area.height;

    if (g->viewport_x > 1) {
        /* Left arrow indicator */
        DrawTriangle(
            (Vector2){g->view_area.x + 15, g->view_area.y + view_h/2},
            (Vector2){g->view_area.x + 25, g->view_area.y + view_h/2 - 10},
            (Vector2){g->view_area.x + 25, g->view_area.y + view_h/2 + 10},
            indicator);
    }
    float max_x = g->graph_bounds.width - view_w / zoom;
    if (g->viewport_x < max_x - 1) {
        /* Right arrow indicator */
        DrawTriangle(
            (Vector2){g->view_area.x + view_w - 15, g->view_area.y + view_h/2},
            (Vector2){g->view_area.x + view_w - 25, g->view_area.y + view_h/2 + 10},
            (Vector2){g->view_area.x + view_w - 25, g->view_area.y + view_h/2 - 10},
            indicator);
    }
    if (g->viewport_y > 1) {
        /* Up arrow indicator */
        DrawTriangle(
            (Vector2){g->view_area.x + view_w/2, g->view_area.y + 15},
            (Vector2){g->view_area.x + view_w/2 + 10, g->view_area.y + 25},
            (Vector2){g->view_area.x + view_w/2 - 10, g->view_area.y + 25},
            indicator);
    }
    float max_y = g->graph_bounds.height - view_h / zoom;
    if (g->viewport_y < max_y - 1) {
        /* Down arrow indicator */
        DrawTriangle(
            (Vector2){g->view_area.x + view_w/2, g->view_area.y + view_h - 15},
            (Vector2){g->view_area.x + view_w/2 - 10, g->view_area.y + view_h - 25},
            (Vector2){g->view_area.x + view_w/2 + 10, g->view_area.y + view_h - 25},
            indicator);
    }

    EndScissorMode();

    /* Draw zoom level indicator */
    if (g->viewport_zoom != 1.0f) {
        char zoom_text[32];
        snprintf(zoom_text, sizeof(zoom_text), "%.0f%%", g->viewport_zoom * 100);
        DrawTextQBP(zoom_text, (int)(g->view_area.x + 8), (int)(g->view_area.y + 8),
                    12, QBP_TEXT_DIM);
    }
}

/* Helper to draw word-wrapped text, returns new y position.
 * use_mono: 1 = use monospace font (for Lean code), 0 = body font */
static float draw_wrapped_text_ex(const char *text, float x, float y,
                                  float max_w, int font_size, Color color,
                                  int use_mono)
{
    int line_h = font_size + 6;  /* +6 for 1.5x-ish line spacing (BDA) */
    int len = (int)strlen(text);
    int start = 0;
    /* Account for wider letter spacing with Atkinson */
    float char_w = use_mono ? (font_size * 0.65f) : (font_size * 0.55f);
    float chars_per_line = max_w / char_w;

    while (start < len) {
        int end = start;
        while (end < len && (end - start) < (int)chars_per_line) {
            if (text[end] == '\n') { end++; break; }
            end++;
        }
        if (end < len && end > start && text[end-1] != '\n') {
            int last_space = end;
            while (last_space > start && text[last_space] != ' ') last_space--;
            if (last_space > start) end = last_space + 1;
        }
        char buf[512];
        int chunk = end - start;
        if (chunk > 511) chunk = 511;
        memcpy(buf, text + start, chunk);
        buf[chunk] = '\0';
        /* Trim newline */
        if (chunk > 0 && buf[chunk-1] == '\n') buf[chunk-1] = '\0';
        if (use_mono)
            DrawTextQBPMono(buf, (int)x, (int)y, font_size, color);
        else
            DrawTextQBP(buf, (int)x, (int)y, font_size, color);
        y += line_h;
        start = end;
    }
    return y;
}

/* Convenience wrapper: body font */
static float draw_wrapped_text(const char *text, float x, float y,
                               float max_w, int font_size, Color color)
{
    return draw_wrapped_text_ex(text, x, y, max_w, font_size, color, 0);
}

/* Convenience wrapper: mono font (for L4 Lean code) */
static float draw_wrapped_text_mono(const char *text, float x, float y,
                                    float max_w, int font_size, Color color)
{
    return draw_wrapped_text_ex(text, x, y, max_w, font_size, color, 1);
}

void graph_draw_info_panel(const ProofGraph *g, Rectangle panel)
{
    const ProofNode *n = graph_current_node(g);

    /* Draw panel background and border */
    DrawRectangleRec(panel, QBP_PANEL_BG);
    DrawRectangleLinesEx(panel, 2.0f, QBP_BRASS);

    /* Font sizes — bumped +3px for readability (Atkinson Hyperlegible) */
    int title_font = 23;
    int header_font = 15;
    int body_font = 16;
    int section_gap = 10;

    float x = panel.x + 12;
    float y = panel.y + 10;
    float max_w = panel.width - 24;
    float panel_bottom = panel.y + panel.height - 4;

    /* Clip content to panel area */
    BeginScissorMode((int)panel.x + 2, (int)panel.y + 2,
                     (int)panel.width - 4, (int)panel.height - 4);

    /* Title: Display name */
    DrawTextQBP(n->display_name, (int)x, (int)y, title_font, QBP_GOLD);
    y += title_font + 6;

    /* Formal Lean name (smaller, dimmer) */
    DrawTextQBPMono(n->name, (int)x, (int)y, 13, QBP_TEXT_DIM);
    y += 17;

    /* Kind badge inline */
    const char *kind_str = (n->kind == NODE_AXIOM) ? "AXIOM" :
                           (n->kind == NODE_DEFINITION) ? "DEFINITION" : "THEOREM";
    DrawTextQBPBold(kind_str, (int)x, (int)y, 15, kind_badge_color(n->kind));
    y += 22;

    /* Separator */
    DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.0f, QBP_STEEL);
    y += 8;

    /* ============ LEVEL 4: FORMAL ============ */
    DrawTextQBP("FORMAL (Lean)", (int)x, (int)y, header_font, QBP_TEXT_DIM);
    y += header_font + 4;
    y = draw_wrapped_text(n->level4_formal, x, y, max_w, body_font, QBP_TEAL);
    y += section_gap;

    /* ============ LEVEL 3: MATHEMATICAL ============ */
    DrawTextQBP("MATHEMATICAL", (int)x, (int)y, header_font, QBP_TEXT_DIM);
    y += header_font + 4;
    y = draw_wrapped_text(n->level3_math, x, y, max_w, body_font, QBP_COPPER);
    y += section_gap;

    /* ============ LEVEL 2: PHYSICAL ============ */
    DrawTextQBP("PHYSICAL", (int)x, (int)y, header_font, QBP_TEXT_DIM);
    y += header_font + 4;
    y = draw_wrapped_text(n->level2_physical, x, y, max_w, body_font, QBP_AMBER);
    y += section_gap;

    /* ============ LEVEL 1: INTUITIVE ============ */
    DrawRectangle((int)(x - 4), (int)y - 2, (int)(max_w + 8), 22, QBP_DARK_SLATE);
    DrawTextQBPBold("INTUITIVE", (int)x, (int)y, 17, QBP_IVORY);
    y += 24;
    y = draw_wrapped_text(n->level1_intuitive, x, y, max_w, body_font + 1, QBP_IVORY);
    y += section_gap;

    /* ============ KEY INSIGHT ============ */
    if (strlen(n->key_insight) > 0) {
        DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.5f, QBP_GOLD);
        y += 6;
        DrawTextQBP("KEY INSIGHT", (int)x, (int)y, header_font, QBP_GOLD);
        y += header_font + 4;
        y = draw_wrapped_text(n->key_insight, x, y, max_w, body_font, QBP_GOLD);
    }

    /* Track if content overflowed */
    float content_bottom = y;

    /* Dependencies (if room remains) */
    if (n->dep_count > 0) {
        y += 8;
        DrawTextQBP("Depends on:", (int)x, (int)y, header_font, QBP_TEXT_DIM);
        y += header_font + 4;
        for (int i = 0; i < n->dep_count; i++) {
            char dep_buf[256];
            snprintf(dep_buf, sizeof(dep_buf), "-> %s", g->nodes[n->deps[i]].display_name);
            DrawTextQBP(dep_buf, (int)x, (int)y, 15, QBP_STEEL);
            y += 18;
        }
        content_bottom = y;
    }

    EndScissorMode();

    /* Draw "more content" indicator if content was clipped */
    if (content_bottom > panel_bottom) {
        /* Fade gradient at bottom */
        for (int i = 0; i < 20; i++) {
            Color fade = (Color){13, 27, 42, (unsigned char)(255 - i * 12)};
            DrawLine((int)panel.x + 4, (int)panel_bottom - 20 + i,
                     (int)(panel.x + panel.width - 4), (int)panel_bottom - 20 + i, fade);
        }
        /* Down arrow indicator */
        DrawTextQBP("...", (int)(panel.x + panel.width/2 - 8),
                    (int)(panel_bottom - 14), 12, QBP_TEXT_DIM);
    }
}

void graph_draw_step_bar(const ProofGraph *g, Rectangle bar)
{
    DrawRectangleRec(bar, QBP_PANEL_BG);
    DrawRectangleLinesEx(bar, 2.0f, QBP_BRASS);

    const ProofNode *n = graph_current_node(g);
    char buf[256];
    snprintf(buf, sizeof(buf), "Step %d/%d  --  %s",
             g->current_step + 1, g->walk_len, n->display_name);

    int text_w = MeasureTextQBP(buf, 20);
    float cx = bar.x + (bar.width - text_w) / 2;
    float cy = bar.y + (bar.height - 20) / 2;
    DrawTextQBP(buf, (int)cx, (int)cy, 20, QBP_TEXT_PRIMARY);

    /* Navigation buttons - larger and more visible */
    Rectangle prev_btn = { bar.x + 16, bar.y + 10, 120, bar.height - 20 };
    Rectangle next_btn = { bar.x + bar.width - 136, bar.y + 10, 120, bar.height - 20 };

    /* Draw button backgrounds */
    Color prev_col = (g->current_step > 0) ? QBP_STEEL : QBP_DARK_SLATE;
    Color next_col = (g->current_step < g->walk_len - 1) ? QBP_STEEL : QBP_DARK_SLATE;

    DrawRectangleRounded(prev_btn, 0.3f, 4, prev_col);
    DrawRectangleRounded(next_btn, 0.3f, 4, next_col);
    DrawRectangleRoundedLinesEx(prev_btn, 0.3f, 4, 2.0f, QBP_BRASS);
    DrawRectangleRoundedLinesEx(next_btn, 0.3f, 4, 2.0f, QBP_BRASS);

    /* Center text in buttons */
    int prev_tw = MeasureTextQBP("<< Prev", 18);
    int next_tw = MeasureTextQBP("Next >>", 18);
    DrawTextQBP("<< Prev", (int)(prev_btn.x + (prev_btn.width - prev_tw)/2),
             (int)(prev_btn.y + (prev_btn.height - 18)/2), 18, QBP_IVORY);
    DrawTextQBP("Next >>", (int)(next_btn.x + (next_btn.width - next_tw)/2),
             (int)(next_btn.y + (next_btn.height - 18)/2), 18, QBP_IVORY);
}

/* ------------------------------------------------------------------ */
/*  Toggle functions (#228, #229)                                      */
/* ------------------------------------------------------------------ */

void graph_toggle_angle_highlight(ProofGraph *g)
{
    g->angle_highlight = !g->angle_highlight;
}

void graph_toggle_overview(ProofGraph *g)
{
    g->overview_mode = !g->overview_mode;
}

/* ------------------------------------------------------------------ */
/*  Overview panel (#228)                                              */
/* ------------------------------------------------------------------ */

void graph_draw_overview(const ProofGraph *g, Rectangle panel)
{
    DrawRectangleRec(panel, QBP_PANEL_BG);
    DrawRectangleLinesEx(panel, 2.0f, QBP_BRASS);

    float x = panel.x + 12;
    float y = panel.y + 10;
    float max_w = panel.width - 24;

    BeginScissorMode((int)panel.x + 2, (int)panel.y + 2,
                     (int)panel.width - 4, (int)panel.height - 4);

    /* Title */
    DrawTextQBP("PROOF OVERVIEW", (int)x, (int)y, 20, QBP_GOLD);
    y += 26;

    /* Count by role */
    int n_axiom = 0, n_def = 0, n_thm = 0, n_angle = 0;
    for (int i = 0; i < g->node_count; i++) {
        switch (g->nodes[i].kind) {
            case NODE_AXIOM:      n_axiom++; break;
            case NODE_DEFINITION: n_def++; break;
            case NODE_THEOREM:    n_thm++; break;
        }
        if (g->nodes[i].has_tag_angle) n_angle++;
    }

    char buf[256];

    /* Summary stats */
    snprintf(buf, sizeof(buf), "Total nodes: %d", g->node_count);
    DrawTextQBP(buf, (int)x, (int)y, 14, QBP_TEXT_PRIMARY);
    y += 18;

    snprintf(buf, sizeof(buf), "  Axioms: %d", n_axiom);
    DrawTextQBP(buf, (int)x, (int)y, 13, QBP_CRIMSON);
    y += 16;

    snprintf(buf, sizeof(buf), "  Definitions: %d", n_def);
    DrawTextQBP(buf, (int)x, (int)y, 13, QBP_AMBER);
    y += 16;

    snprintf(buf, sizeof(buf), "  Theorems: %d", n_thm);
    DrawTextQBP(buf, (int)x, (int)y, 13, QBP_TEAL);
    y += 16;

    if (n_angle > 0) {
        snprintf(buf, sizeof(buf), "  Angle-dependent: %d", n_angle);
        DrawTextQBP(buf, (int)x, (int)y, 13, QBP_ANGLE_GLOW);
        y += 16;
    }

    y += 8;
    DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.0f, QBP_STEEL);
    y += 8;

    /* Proof structure: list nodes grouped by kind */
    DrawTextQBP("STRUCTURE", (int)x, (int)y, 14, QBP_TEXT_DIM);
    y += 18;

    /* Goal nodes (theorems at bottom of tree = highest level) */
    DrawTextQBP("Goal:", (int)x, (int)y, 13, QBP_GOLD);
    y += 16;
    for (int i = 0; i < g->node_count; i++) {
        if (g->nodes[i].kind != NODE_THEOREM) continue;
        /* Check if this theorem is depended on by anyone */
        int is_used = 0;
        for (int j = 0; j < g->node_count; j++) {
            for (int d = 0; d < g->nodes[j].dep_count; d++) {
                if (g->nodes[j].deps[d] == i) { is_used = 1; break; }
            }
            if (is_used) break;
        }
        if (!is_used) {
            /* Terminal theorem = goal */
            Color c = g->nodes[i].has_tag_angle ? QBP_ANGLE_GLOW : QBP_IVORY;
            snprintf(buf, sizeof(buf), "  %s", g->nodes[i].display_name);
            DrawTextQBP(buf, (int)x, (int)y, 12, c);
            y += 14;
        }
    }
    y += 4;

    /* Key lemmas (theorems that are used by other nodes) */
    DrawTextQBP("Key lemmas:", (int)x, (int)y, 13, QBP_TEAL);
    y += 16;
    for (int i = 0; i < g->node_count; i++) {
        if (g->nodes[i].kind != NODE_THEOREM) continue;
        int is_used = 0;
        for (int j = 0; j < g->node_count; j++) {
            for (int d = 0; d < g->nodes[j].dep_count; d++) {
                if (g->nodes[j].deps[d] == i) { is_used = 1; break; }
            }
            if (is_used) break;
        }
        if (is_used) {
            Color c = g->nodes[i].has_tag_angle ? QBP_ANGLE_GLOW : QBP_IVORY;
            snprintf(buf, sizeof(buf), "  %s", g->nodes[i].display_name);
            DrawTextQBP(buf, (int)x, (int)y, 12, c);
            y += 14;
        }
    }
    y += 4;

    /* Definitions */
    DrawTextQBP("Definitions:", (int)x, (int)y, 13, QBP_AMBER);
    y += 16;
    for (int i = 0; i < g->node_count; i++) {
        if (g->nodes[i].kind != NODE_DEFINITION) continue;
        Color c = g->nodes[i].has_tag_angle ? QBP_ANGLE_GLOW : QBP_TEXT_DIM;
        snprintf(buf, sizeof(buf), "  %s", g->nodes[i].display_name);
        DrawTextQBP(buf, (int)x, (int)y, 12, c);
        y += 14;
    }

    y += 8;
    DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.0f, QBP_STEEL);
    y += 8;

    /* Controls hint */
    DrawTextQBP("[O] Toggle overview", (int)x, (int)y, 11, QBP_TEXT_DIM);
    y += 14;
    DrawTextQBP("[T] Toggle angle emphasis", (int)x, (int)y, 11, QBP_TEXT_DIM);

    EndScissorMode();
}
