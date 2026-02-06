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

void graph_layout(ProofGraph *g, Rectangle area)
{
    float x0 = area.x;
    float y0 = area.y;
    float w  = area.width;
    float h  = area.height;

    float row_h = h / 7.0f;

    #define POS(row, col, ncols) \
        (Vector2){ x0 + w * ((col) + 0.5f) / (ncols), y0 + row_h * ((row) + 0.5f) }

    g->nodes[N_IS_PURE].pos     = POS(0, 0, 2);
    g->nodes[N_VEC_DOT].pos     = POS(0, 1, 2);

    g->nodes[N_SPIN_X_PURE].pos = POS(1, 0, 2);
    g->nodes[N_SPIN_Z_PURE].pos = POS(1, 1, 2);

    g->nodes[N_SG_STATE].pos    = POS(2, 0, 2);
    g->nodes[N_SG_OBS].pos      = POS(2, 1, 2);

    g->nodes[N_SG_STATE_IS_PURE].pos = POS(3, 0, 2);
    g->nodes[N_SG_OBS_IS_PURE].pos   = POS(3, 1, 2);

    g->nodes[N_X_Z_ORTHO].pos       = POS(4, 0, 2);
    g->nodes[N_EXP_ORTHO_ZERO].pos  = POS(4, 1, 2);

    g->nodes[N_EXP_XZ_ZERO].pos = POS(5, 0, 1);

    g->nodes[N_PROB_UP].pos     = POS(6, 0, 2);
    g->nodes[N_PROB_DOWN].pos   = POS(6, 1, 2);

    #undef POS
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

#define NODE_W  180
#define NODE_H   40
#define FONT_SZ   14

static Rectangle node_rect(const ProofNode *n)
{
    return (Rectangle){
        n->pos.x - NODE_W/2.0f,
        n->pos.y - NODE_H/2.0f,
        NODE_W, NODE_H
    };
}

static Color node_color(const ProofGraph *g, int id)
{
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
    /* Draw edges first (behind nodes) */
    for (int i = 0; i < g->node_count; i++) {
        const ProofNode *n = &g->nodes[i];
        for (int d = 0; d < n->dep_count; d++) {
            const ProofNode *dep = &g->nodes[n->deps[d]];
            Color c = QBP_STEEL;
            if (graph_is_active(g, i) && graph_is_dependency(g, n->deps[d])) {
                c = QBP_EDGE;
            }
            DrawLineEx(dep->pos, n->pos, 2.0f, c);
        }
    }

    /* Draw nodes */
    for (int i = 0; i < g->node_count; i++) {
        const ProofNode *n = &g->nodes[i];
        Rectangle r = node_rect(n);
        Color bg = node_color(g, i);

        DrawRectangleRounded(r, 0.3f, 8, bg);
        DrawRectangleRoundedLinesEx(r, 0.3f, 8, 1.5f, QBP_BRASS);

        /* Kind badge */
        Color badge = kind_badge_color(n->kind);
        float badge_w = 32;
        Rectangle br = { r.x + 2, r.y + 2, badge_w, NODE_H - 4 };
        DrawRectangleRounded(br, 0.3f, 4, badge);
        DrawText(kind_label(n->kind),
                 (int)(br.x + 3), (int)(br.y + (br.height - 10)/2),
                 10, QBP_IVORY);

        /* Node name */
        int text_x = (int)(r.x + badge_w + 8);
        int text_y = (int)(r.y + (NODE_H - FONT_SZ) / 2);
        DrawText(n->name, text_x, text_y, FONT_SZ, QBP_TEXT_PRIMARY);
    }
}

/* Helper to draw word-wrapped text, returns new y position */
static float draw_wrapped_text(const char *text, float x, float y,
                               float max_w, int font_size, Color color)
{
    int line_h = font_size + 4;
    int len = (int)strlen(text);
    int start = 0;
    float chars_per_line = max_w / (font_size * 0.6f);

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
        DrawText(buf, (int)x, (int)y, font_size, color);
        y += line_h;
        start = end;
    }
    return y;
}

void graph_draw_info_panel(const ProofGraph *g, Rectangle panel)
{
    const ProofNode *n = graph_current_node(g);

    DrawRectangleRec(panel, QBP_PANEL_BG);
    DrawRectangleLinesEx(panel, 1.0f, QBP_BRASS);

    float x = panel.x + 12;
    float y = panel.y + 10;
    float max_w = panel.width - 24;
    int section_gap = 12;

    /* Title: Display name */
    DrawText(n->display_name, (int)x, (int)y, 16, QBP_GOLD);
    y += 20;

    /* Kind badge inline */
    const char *kind_str = (n->kind == NODE_AXIOM) ? "AXIOM" :
                           (n->kind == NODE_DEFINITION) ? "DEFINITION" : "THEOREM";
    DrawText(kind_str, (int)x, (int)y, 10, kind_badge_color(n->kind));
    y += 16;

    /* Separator */
    DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.0f, QBP_STEEL);
    y += 8;

    /* ============ LEVEL 4: FORMAL ============ */
    DrawText("FORMAL (Lean)", (int)x, (int)y, 10, QBP_TEXT_DIM);
    y += 14;
    y = draw_wrapped_text(n->level4_formal, x, y, max_w, 11, QBP_TEAL);
    y += section_gap;

    /* ============ LEVEL 3: MATHEMATICAL ============ */
    DrawText("MATHEMATICAL", (int)x, (int)y, 10, QBP_TEXT_DIM);
    y += 14;
    y = draw_wrapped_text(n->level3_math, x, y, max_w, 11, QBP_COPPER);
    y += section_gap;

    /* ============ LEVEL 2: PHYSICAL ============ */
    DrawText("PHYSICAL", (int)x, (int)y, 10, QBP_TEXT_DIM);
    y += 14;
    y = draw_wrapped_text(n->level2_physical, x, y, max_w, 11, QBP_AMBER);
    y += section_gap;

    /* ============ LEVEL 1: INTUITIVE ============ */
    DrawRectangle((int)(x - 4), (int)y - 2, (int)(max_w + 8), 14, QBP_DARK_SLATE);
    DrawText("INTUITIVE (Plain English)", (int)x, (int)y, 10, QBP_IVORY);
    y += 16;
    y = draw_wrapped_text(n->level1_intuitive, x, y, max_w, 12, QBP_IVORY);
    y += section_gap;

    /* ============ KEY INSIGHT ============ */
    if (strlen(n->key_insight) > 0) {
        DrawLineEx((Vector2){x, y}, (Vector2){x + max_w, y}, 1.0f, QBP_GOLD);
        y += 6;
        DrawText("KEY INSIGHT", (int)x, (int)y, 9, QBP_GOLD);
        y += 12;
        y = draw_wrapped_text(n->key_insight, x, y, max_w, 11, QBP_GOLD);
    }

    /* Dependencies (if room remains) */
    if (n->dep_count > 0 && y < panel.y + panel.height - 60) {
        y += 8;
        DrawText("Depends on:", (int)x, (int)y, 10, QBP_TEXT_DIM);
        y += 14;
        for (int i = 0; i < n->dep_count && y < panel.y + panel.height - 20; i++) {
            char dep_buf[128];
            snprintf(dep_buf, sizeof(dep_buf), "  -> %s", g->nodes[n->deps[i]].display_name);
            DrawText(dep_buf, (int)x, (int)y, 10, QBP_STEEL);
            y += 12;
        }
    }
}

void graph_draw_step_bar(const ProofGraph *g, Rectangle bar)
{
    DrawRectangleRec(bar, QBP_PANEL_BG);
    DrawRectangleLinesEx(bar, 1.0f, QBP_BRASS);

    const ProofNode *n = graph_current_node(g);
    char buf[256];
    snprintf(buf, sizeof(buf), "Step %d/%d  --  %s",
             g->current_step + 1, g->walk_len, n->display_name);

    int text_w = MeasureText(buf, 14);
    float cx = bar.x + (bar.width - text_w) / 2;
    float cy = bar.y + (bar.height - 14) / 2;
    DrawText(buf, (int)cx, (int)cy, 14, QBP_TEXT_PRIMARY);

    /* Navigation buttons - now actual clickable areas */
    Rectangle prev_btn = { bar.x + 8, bar.y + 6, 70, bar.height - 12 };
    Rectangle next_btn = { bar.x + bar.width - 78, bar.y + 6, 70, bar.height - 12 };

    /* Draw button backgrounds */
    Color prev_col = (g->current_step > 0) ? QBP_STEEL : QBP_DARK_SLATE;
    Color next_col = (g->current_step < g->walk_len - 1) ? QBP_STEEL : QBP_DARK_SLATE;

    DrawRectangleRounded(prev_btn, 0.3f, 4, prev_col);
    DrawRectangleRounded(next_btn, 0.3f, 4, next_col);

    DrawText("< Prev", (int)(prev_btn.x + 10), (int)(prev_btn.y + 6), 12, QBP_IVORY);
    DrawText("Next >", (int)(next_btn.x + 10), (int)(next_btn.y + 6), 12, QBP_IVORY);
}
