/*
 * experiment_03_double_slit.c — Double-slit proof visualization scene.
 *
 * Implements the Scene interface for the double-slit experiment.
 * Users step through the proof dependency tree, seeing how the
 * quaternionic coupling, Born rule, and visibility definitions
 * combine to prove V = 1 - eta (the central QBP prediction).
 */

#include "../scene.h"
#include "../proof_graph.h"
#include "../json_loader.h"
#include "../theme.h"
#include "../fonts.h"
#include "raylib.h"
#include <stdio.h>

static ProofGraph ds_graph;
static int screen_width;
static int screen_height;

/* Layout constants */
#define PANEL_WIDTH   440  /* Wider to fit 4-level descriptions */
#define BAR_HEIGHT     56
#define TITLE_HEIGHT   60

static void ds_init(int sw, int sh)
{
    screen_width = sw;
    screen_height = sh;

    /* Load from JSON - no hardcoded fallback for this experiment */
    if (graph_load_json(&ds_graph, "/data/doubleslit.viz.json") != 0) {
        fprintf(stderr, "[ds_init] ERROR: Failed to load doubleslit.viz.json\n");
        /* Initialize empty graph to prevent crashes */
        ds_graph.node_count = 0;
        ds_graph.walk_len = 0;
        ds_graph.current_step = 0;
    }

    /* Graph occupies left portion, panel on the right */
    Rectangle graph_area = {
        20,
        TITLE_HEIGHT,
        (float)(sw - PANEL_WIDTH - 40),
        (float)(sh - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };
    graph_viewport_init(&ds_graph);
    graph_layout(&ds_graph, graph_area);
}

static void ds_update(void)
{
    /* Handle viewport pan/zoom input */
    graph_viewport_update(&ds_graph);

    if (IsKeyPressed(KEY_RIGHT) || IsKeyPressed(KEY_DOWN) ||
        IsKeyPressed(KEY_SPACE) || IsKeyPressed(KEY_ENTER)) {
        graph_step_forward(&ds_graph);
    }
    if (IsKeyPressed(KEY_LEFT) || IsKeyPressed(KEY_UP) ||
        IsKeyPressed(KEY_BACKSPACE)) {
        graph_step_back(&ds_graph);
    }
    if (IsKeyPressed(KEY_R) || IsKeyPressed(KEY_HOME)) {
        graph_reset(&ds_graph);
        graph_reset_viewport(&ds_graph);
    }
    if (IsKeyPressed(KEY_O)) {
        graph_toggle_overview(&ds_graph);
    }
    if (IsKeyPressed(KEY_T)) {
        graph_toggle_angle_highlight(&ds_graph);
    }

    /* Handle mouse clicks */
    if (IsMouseButtonPressed(MOUSE_BUTTON_LEFT)) {
        Vector2 mouse = GetMousePosition();

        /* Check step bar buttons first - must match graph_draw_step_bar button sizes */
        Rectangle bar = { 0, (float)(screen_height - BAR_HEIGHT), (float)screen_width, BAR_HEIGHT };
        Rectangle prev_btn = { bar.x + 16, bar.y + 10, 120, bar.height - 20 };
        Rectangle next_btn = { bar.x + bar.width - 136, bar.y + 10, 120, bar.height - 20 };

        if (CheckCollisionPointRec(mouse, prev_btn)) {
            graph_step_back(&ds_graph);
        } else if (CheckCollisionPointRec(mouse, next_btn)) {
            graph_step_forward(&ds_graph);
        } else {
            /* Click on nodes to jump to them - use dynamic node bounds */
            for (int i = 0; i < ds_graph.node_count; i++) {
                Rectangle node_rect = graph_node_bounds(&ds_graph, i);
                if (CheckCollisionPointRec(mouse, node_rect)) {
                    /* Find this node in walk_order */
                    for (int s = 0; s < ds_graph.walk_len; s++) {
                        if (ds_graph.walk_order[s] == i) {
                            ds_graph.current_step = s;
                            break;
                        }
                    }
                    break;
                }
            }
        }
    }
}

static void ds_draw(void)
{
    /* Title */
    DrawTextQBP("QBP  |  Double-Slit Proof Visualization",
             24, 16, 28, QBP_GOLD);
    DrawTextQBP("Experiment 03: V = 1 - eta (quaternionic visibility bridge)",
             24, 44, 16, QBP_TEXT_DIM);

    /* Info panel area (right side) */
    Rectangle panel = {
        (float)(screen_width - PANEL_WIDTH - 10),
        TITLE_HEIGHT,
        PANEL_WIDTH,
        (float)(screen_height - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };

    if (ds_graph.overview_mode) {
        /* Overview replaces both graph and info panel */
        Rectangle overview = {
            20, TITLE_HEIGHT,
            (float)(screen_width - 40),
            (float)(screen_height - TITLE_HEIGHT - BAR_HEIGHT - 20)
        };
        graph_draw_overview(&ds_graph, overview);
    } else {
        /* Normal mode: proof graph + info panel */
        graph_draw(&ds_graph);
        graph_draw_info_panel(&ds_graph, panel);
    }

    /* Step bar (bottom) */
    Rectangle bar = {
        0,
        (float)(screen_height - BAR_HEIGHT),
        (float)screen_width,
        BAR_HEIGHT
    };
    graph_draw_step_bar(&ds_graph, bar);
}

static void ds_cleanup(void)
{
    /* Nothing to free — all static data */
}

Scene scene_double_slit = {
    .init    = ds_init,
    .update  = ds_update,
    .draw    = ds_draw,
    .cleanup = ds_cleanup,
    .name    = "Double-Slit Proof Visualization"
};
