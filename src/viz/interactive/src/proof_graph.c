/*
 * proof_graph.c — Proof dependency tree for Stern-Gerlach experiment.
 *
 * The graph is hardcoded from:
 *   proofs/QBP/Basic.lean
 *   proofs/QBP/Experiments/SternGerlach.lean
 */

#include "proof_graph.h"
#include "theme.h"
#include <string.h>
#include <stdio.h>

/* ------------------------------------------------------------------ */
/*  Node IDs (match walk_order indices for clarity)                   */
/* ------------------------------------------------------------------ */
enum {
    N_IS_UNIT = 0,
    N_IS_PURE,
    N_SPIN_X_PURE,
    N_SPIN_Z_PURE,
    N_VEC_DOT,
    N_SG_STATE,
    N_SG_OBS,
    N_X_Z_ORTHO,
    N_EXP_ORTHO_ZERO,
    N_EXP_XZ_ZERO,
    N_PROB_UP,
    N_PROB_DOWN,
    N_COUNT
};

/* Helper to add a node */
static void add_node(ProofGraph *g, int id, const char *name,
                     const char *statement, const char *meaning,
                     NodeKind kind, const int *deps, int dep_count)
{
    ProofNode *n = &g->nodes[id];
    n->id = id;
    snprintf(n->name, MAX_NAME_LEN, "%s", name);
    snprintf(n->statement, MAX_STATEMENT_LEN, "%s", statement);
    snprintf(n->physical_meaning, MAX_MEANING_LEN, "%s", meaning);
    n->kind = kind;
    n->dep_count = dep_count;
    for (int i = 0; i < dep_count; i++) n->deps[i] = deps[i];
}

void graph_init_stern_gerlach(ProofGraph *g)
{
    memset(g, 0, sizeof(*g));
    g->node_count = N_COUNT;

    /* --- Axioms (Basic.lean) --- */
    add_node(g, N_IS_UNIT,
        "isUnitQuaternion",
        "def isUnitQuaternion (q : Q) : Prop := q.normSq = 1",
        "Axiom 1: A quantum state is a unit quaternion (|psi|^2 = 1).",
        NODE_AXIOM, NULL, 0);

    add_node(g, N_IS_PURE,
        "isPureQuaternion",
        "def isPureQuaternion (q : Q) : Prop := q.re = 0",
        "Axiom 2: An observable is a pure quaternion (scalar part = 0).",
        NODE_AXIOM, NULL, 0);

    /* --- Theorems from Basic.lean --- */
    {
        int deps[] = { N_IS_PURE };
        add_node(g, N_SPIN_X_PURE,
            "spin_x_is_pure",
            "theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl",
            "SPIN_X = i is a valid observable (pure quaternion).",
            NODE_THEOREM, deps, 1);
    }
    {
        int deps[] = { N_IS_PURE };
        add_node(g, N_SPIN_Z_PURE,
            "spin_z_is_pure",
            "theorem spin_z_is_pure : isPureQuaternion SPIN_Z := rfl",
            "SPIN_Z = k is a valid observable (pure quaternion).",
            NODE_THEOREM, deps, 1);
    }

    /* vecDot definition */
    add_node(g, N_VEC_DOT,
        "vecDot",
        "def vecDot (q1 q2 : Q) : R := q1.imI*q2.imI + q1.imJ*q2.imJ + q1.imK*q2.imK",
        "Dot product of vector parts: measures alignment between states.",
        NODE_DEFINITION, NULL, 0);

    /* --- Experiment setup (SternGerlach.lean) --- */
    {
        int deps[] = { N_SPIN_X_PURE };
        add_node(g, N_SG_STATE,
            "spinXState",
            "def spinXState : Q := SPIN_X",
            "Experiment state: particle with spin along +x axis (quaternion i).",
            NODE_DEFINITION, deps, 1);
    }
    {
        int deps[] = { N_SPIN_Z_PURE };
        add_node(g, N_SG_OBS,
            "spinZObservable",
            "def spinZObservable : Q := SPIN_Z",
            "Measurement axis: spin measured along z axis (quaternion k).",
            NODE_DEFINITION, deps, 1);
    }

    /* Orthogonality proof */
    {
        int deps[] = { N_VEC_DOT, N_SG_STATE, N_SG_OBS };
        add_node(g, N_X_Z_ORTHO,
            "x_z_orthogonal",
            "theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0",
            "The x and z spin axes are perpendicular: their dot product is zero.",
            NODE_THEOREM, deps, 3);
    }

    /* General orthogonal expectation theorem */
    {
        int deps[] = { N_IS_PURE, N_VEC_DOT };
        add_node(g, N_EXP_ORTHO_ZERO,
            "expectation_orthogonal_is_zero",
            "theorem expectation_orthogonal_is_zero (psi O : Q) ... : expectationValue psi O = 0",
            "General principle: perpendicular states always give zero expectation.",
            NODE_THEOREM, deps, 2);
    }

    /* Main result */
    {
        int deps[] = { N_EXP_ORTHO_ZERO, N_SG_STATE, N_SG_OBS, N_X_Z_ORTHO };
        add_node(g, N_EXP_XZ_ZERO,
            "expectation_x_measured_z_is_zero",
            "theorem expectation_x_measured_z_is_zero :\n  expectationValue spinXState spinZObservable = 0",
            "Core result: <O_z> = 0 for spin-x state. Average measurement is zero.",
            NODE_THEOREM, deps, 4);
    }

    /* Probability corollaries */
    {
        int deps[] = { N_EXP_XZ_ZERO };
        add_node(g, N_PROB_UP,
            "prob_up = 1/2",
            "theorem prob_up_x_measured_z_is_half :\n  probUp spinXState spinZObservable = 1/2",
            "Probability of spin-up (+1) is exactly 50%.",
            NODE_THEOREM, deps, 1);
    }
    {
        int deps[] = { N_EXP_XZ_ZERO };
        add_node(g, N_PROB_DOWN,
            "prob_down = 1/2",
            "theorem prob_down_x_measured_z_is_half :\n  probDown spinXState spinZObservable = 1/2",
            "Probability of spin-down (-1) is exactly 50%.",
            NODE_THEOREM, deps, 1);
    }

    /* Walk order: bottom-up through the proof tree */
    int order[] = {
        N_IS_UNIT, N_IS_PURE, N_VEC_DOT,
        N_SPIN_X_PURE, N_SPIN_Z_PURE,
        N_SG_STATE, N_SG_OBS,
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
    /*
     * Layout rows (top to bottom):
     *   Row 0: Axioms        — isUnitQuaternion, isPureQuaternion
     *   Row 1: Basic thms    — spin_x_is_pure, spin_z_is_pure, vecDot
     *   Row 2: SG setup      — spinXState, spinZObservable, expectation_orthogonal_is_zero
     *   Row 3: Ortho proof   — x_z_orthogonal
     *   Row 4: Main result   — expectation_x_measured_z_is_zero
     *   Row 5: Corollaries   — prob_up, prob_down
     */
    float x0 = area.x;
    float y0 = area.y;
    float w  = area.width;
    float h  = area.height;

    /* Row heights */
    float row_h = h / 6.0f;

    /* Helper: position within a row */
    #define POS(row, col, ncols) \
        (Vector2){ x0 + w * ((col) + 0.5f) / (ncols), y0 + row_h * ((row) + 0.5f) }

    g->nodes[N_IS_UNIT].pos     = POS(0, 0, 2);
    g->nodes[N_IS_PURE].pos     = POS(0, 1, 2);

    g->nodes[N_SPIN_X_PURE].pos = POS(1, 0, 3);
    g->nodes[N_SPIN_Z_PURE].pos = POS(1, 1, 3);
    g->nodes[N_VEC_DOT].pos     = POS(1, 2, 3);

    g->nodes[N_SG_STATE].pos    = POS(2, 0, 3);
    g->nodes[N_SG_OBS].pos      = POS(2, 1, 3);
    g->nodes[N_EXP_ORTHO_ZERO].pos = POS(2, 2, 3);

    g->nodes[N_X_Z_ORTHO].pos   = POS(3, 0, 1);

    g->nodes[N_EXP_XZ_ZERO].pos = POS(4, 0, 1);

    g->nodes[N_PROB_UP].pos     = POS(5, 0, 2);
    g->nodes[N_PROB_DOWN].pos   = POS(5, 1, 2);

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

/* Node box dimensions */
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
    /* Already visited? */
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
    }
    return QBP_STEEL;
}

static const char *kind_label(NodeKind kind)
{
    switch (kind) {
        case NODE_AXIOM:      return "AXM";
        case NODE_DEFINITION: return "DEF";
        case NODE_THEOREM:    return "THM";
    }
    return "???";
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

void graph_draw_info_panel(const ProofGraph *g, Rectangle panel)
{
    const ProofNode *n = graph_current_node(g);

    DrawRectangleRec(panel, QBP_PANEL_BG);
    DrawRectangleLinesEx(panel, 1.0f, QBP_BRASS);

    float x = panel.x + 12;
    float y = panel.y + 12;
    int line_h = 18;

    /* Title */
    DrawText(n->name, (int)x, (int)y, 20, QBP_GOLD);
    y += 28;

    /* Kind */
    const char *kind_str = (n->kind == NODE_AXIOM) ? "Axiom" :
                           (n->kind == NODE_DEFINITION) ? "Definition" : "Theorem";
    DrawText(kind_str, (int)x, (int)y, 14, kind_badge_color(n->kind));
    y += 24;

    /* Statement */
    DrawText("Formal statement:", (int)x, (int)y, 12, QBP_TEXT_DIM);
    y += line_h;

    /* Word-wrap the statement into the panel width */
    float max_w = panel.width - 24;
    const char *text = n->statement;
    int len = (int)strlen(text);
    int start = 0;
    while (start < len) {
        /* Find how many chars fit */
        int end = start;
        while (end < len && (end - start) < (int)(max_w / 7.5f)) end++;
        /* Back up to space if we're mid-word */
        if (end < len && end > start) {
            int last_space = end;
            while (last_space > start && text[last_space] != ' ' && text[last_space] != '\n') last_space--;
            if (last_space > start) end = last_space + 1;
        }
        char buf[256];
        int chunk = end - start;
        if (chunk > 255) chunk = 255;
        memcpy(buf, text + start, chunk);
        buf[chunk] = '\0';
        DrawText(buf, (int)x, (int)y, 12, QBP_TEAL);
        y += line_h;
        start = end;
    }

    y += 8;

    /* Physical meaning */
    DrawText("Physical meaning:", (int)x, (int)y, 12, QBP_TEXT_DIM);
    y += line_h;

    text = n->physical_meaning;
    len = (int)strlen(text);
    start = 0;
    while (start < len) {
        int end = start;
        while (end < len && (end - start) < (int)(max_w / 7.0f)) end++;
        if (end < len && end > start) {
            int last_space = end;
            while (last_space > start && text[last_space] != ' ' && text[last_space] != '\n') last_space--;
            if (last_space > start) end = last_space + 1;
        }
        char buf[256];
        int chunk = end - start;
        if (chunk > 255) chunk = 255;
        memcpy(buf, text + start, chunk);
        buf[chunk] = '\0';
        DrawText(buf, (int)x, (int)y, 12, QBP_AMBER);
        y += line_h;
        start = end;
    }

    /* Dependencies */
    if (n->dep_count > 0) {
        y += 8;
        DrawText("Depends on:", (int)x, (int)y, 12, QBP_TEXT_DIM);
        y += line_h;
        for (int i = 0; i < n->dep_count; i++) {
            char dep_buf[128];
            snprintf(dep_buf, sizeof(dep_buf), "  -> %s", g->nodes[n->deps[i]].name);
            DrawText(dep_buf, (int)x, (int)y, 12, QBP_COPPER);
            y += line_h;
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
             g->current_step + 1, g->walk_len, n->name);

    int text_w = MeasureText(buf, 16);
    float cx = bar.x + (bar.width - text_w) / 2;
    float cy = bar.y + (bar.height - 16) / 2;
    DrawText(buf, (int)cx, (int)cy, 16, QBP_TEXT_PRIMARY);

    /* Navigation hints */
    DrawText("[<-] Prev", (int)(bar.x + 12), (int)cy, 14, QBP_TEXT_DIM);
    DrawText("Next [->]", (int)(bar.x + bar.width - 90), (int)cy, 14, QBP_TEXT_DIM);
}
