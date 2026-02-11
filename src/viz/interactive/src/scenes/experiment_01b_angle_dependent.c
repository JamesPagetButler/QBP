/*
 * experiment_01b_angle_dependent.c — Angle-dependent measurement proof visualization scene.
 *
 * Implements the Scene interface for the angle-dependent measurement experiment.
 * Users step through the proof dependency tree, seeing how the axioms and
 * trigonometric identities combine to prove P(+) = cos²(θ/2).
 */

#include "../scene.h"
#include "../proof_graph.h"
#include "../json_loader.h"
#include "../theme.h"
#include "../fonts.h"
#include "raylib.h"
#include <stdio.h>

static ProofGraph ad_graph;
static int screen_width;
static int screen_height;

/* Layout constants - larger for readability */
#define PANEL_WIDTH   440  /* Wider to fit 4-level descriptions */
#define BAR_HEIGHT     56
#define TITLE_HEIGHT   60

static void ad_init(int sw, int sh)
{
    screen_width = sw;
    screen_height = sh;

    /* Load from JSON - no hardcoded fallback for this experiment */
    if (graph_load_json(&ad_graph, "/data/angle_dependent.viz.json") != 0) {
        fprintf(stderr, "[ad_init] ERROR: Failed to load angle_dependent.viz.json\n");
        /* Initialize empty graph to prevent crashes */
        ad_graph.node_count = 0;
        ad_graph.walk_len = 0;
        ad_graph.current_step = 0;
    }

    /* Graph occupies left portion, panel on the right */
    Rectangle graph_area = {
        20,
        TITLE_HEIGHT,
        (float)(sw - PANEL_WIDTH - 40),
        (float)(sh - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };
    graph_viewport_init(&ad_graph);
    graph_layout(&ad_graph, graph_area);
}

static void ad_update(void)
{
    /* Handle viewport pan/zoom input */
    graph_viewport_update(&ad_graph);

    if (IsKeyPressed(KEY_RIGHT) || IsKeyPressed(KEY_DOWN) ||
        IsKeyPressed(KEY_SPACE) || IsKeyPressed(KEY_ENTER)) {
        graph_step_forward(&ad_graph);
    }
    if (IsKeyPressed(KEY_LEFT) || IsKeyPressed(KEY_UP) ||
        IsKeyPressed(KEY_BACKSPACE)) {
        graph_step_back(&ad_graph);
    }
    if (IsKeyPressed(KEY_R) || IsKeyPressed(KEY_HOME)) {
        graph_reset(&ad_graph);
        graph_reset_viewport(&ad_graph);
    }

    /* Handle mouse clicks */
    if (IsMouseButtonPressed(MOUSE_BUTTON_LEFT)) {
        Vector2 mouse = GetMousePosition();

        /* Check step bar buttons first - must match graph_draw_step_bar button sizes */
        Rectangle bar = { 0, (float)(screen_height - BAR_HEIGHT), (float)screen_width, BAR_HEIGHT };
        Rectangle prev_btn = { bar.x + 16, bar.y + 10, 120, bar.height - 20 };
        Rectangle next_btn = { bar.x + bar.width - 136, bar.y + 10, 120, bar.height - 20 };

        if (CheckCollisionPointRec(mouse, prev_btn)) {
            graph_step_back(&ad_graph);
        } else if (CheckCollisionPointRec(mouse, next_btn)) {
            graph_step_forward(&ad_graph);
        } else {
            /* Click on nodes to jump to them - use dynamic node bounds */
            for (int i = 0; i < ad_graph.node_count; i++) {
                Rectangle node_rect = graph_node_bounds(&ad_graph, i);
                if (CheckCollisionPointRec(mouse, node_rect)) {
                    /* Find this node in walk_order */
                    for (int s = 0; s < ad_graph.walk_len; s++) {
                        if (ad_graph.walk_order[s] == i) {
                            ad_graph.current_step = s;
                            break;
                        }
                    }
                    break;
                }
            }
        }
    }
}

static void ad_draw(void)
{
    /* Title - larger for readability */
    DrawTextQBP("QBP  |  Angle-Dependent Proof Visualization",
             24, 16, 28, QBP_GOLD);
    DrawTextQBP("Experiment 01b: P(+) = cos^2(theta/2) for state at angle theta",
             24, 44, 16, QBP_TEXT_DIM);

    /* Proof graph */
    graph_draw(&ad_graph);

    /* Info panel (right side) */
    Rectangle panel = {
        (float)(screen_width - PANEL_WIDTH - 10),
        TITLE_HEIGHT,
        PANEL_WIDTH,
        (float)(screen_height - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };
    graph_draw_info_panel(&ad_graph, panel);

    /* Step bar (bottom) */
    Rectangle bar = {
        0,
        (float)(screen_height - BAR_HEIGHT),
        (float)screen_width,
        BAR_HEIGHT
    };
    graph_draw_step_bar(&ad_graph, bar);
}

static void ad_cleanup(void)
{
    /* Nothing to free — all static data */
}

Scene scene_angle_dependent = {
    .init    = ad_init,
    .update  = ad_update,
    .draw    = ad_draw,
    .cleanup = ad_cleanup,
    .name    = "Angle-Dependent Proof Visualization"
};
