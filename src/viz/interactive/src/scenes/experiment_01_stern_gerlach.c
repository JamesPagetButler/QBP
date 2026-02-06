/*
 * experiment_01_stern_gerlach.c — Stern-Gerlach proof visualization scene.
 *
 * Implements the Scene interface for the Stern-Gerlach experiment.
 * Users step through the proof dependency tree, seeing how axioms
 * connect to the 50/50 probability result.
 */

#include "../scene.h"
#include "../proof_graph.h"
#include "../json_loader.h"
#include "../theme.h"
#include "../fonts.h"
#include "raylib.h"
#include <stdio.h>

static ProofGraph sg_graph;
static int screen_width;
static int screen_height;

/* Layout constants - larger for readability */
#define PANEL_WIDTH   440  /* Wider to fit 4-level descriptions */
#define BAR_HEIGHT     56
#define TITLE_HEIGHT   60

static void sg_init(int sw, int sh)
{
    screen_width = sw;
    screen_height = sh;

    /* Try to load from JSON first (enables hot-reload) */
    if (graph_load_json(&sg_graph, "/data/stern_gerlach.viz.json") != 0) {
        /* Fallback to hardcoded data if JSON loading fails */
        fprintf(stderr, "[sg_init] JSON load failed, using hardcoded fallback\n");
        graph_init_stern_gerlach(&sg_graph);
    }

    /* Graph occupies left portion, panel on the right */
    Rectangle graph_area = {
        20,
        TITLE_HEIGHT,
        (float)(sw - PANEL_WIDTH - 40),
        (float)(sh - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };
    graph_layout(&sg_graph, graph_area);
}

static void sg_update(void)
{
    if (IsKeyPressed(KEY_RIGHT) || IsKeyPressed(KEY_DOWN) ||
        IsKeyPressed(KEY_SPACE) || IsKeyPressed(KEY_ENTER)) {
        graph_step_forward(&sg_graph);
    }
    if (IsKeyPressed(KEY_LEFT) || IsKeyPressed(KEY_UP) ||
        IsKeyPressed(KEY_BACKSPACE)) {
        graph_step_back(&sg_graph);
    }
    if (IsKeyPressed(KEY_R) || IsKeyPressed(KEY_HOME)) {
        graph_reset(&sg_graph);
    }

    /* Handle mouse clicks */
    if (IsMouseButtonPressed(MOUSE_BUTTON_LEFT)) {
        Vector2 mouse = GetMousePosition();

        /* Check step bar buttons first - must match graph_draw_step_bar button sizes */
        Rectangle bar = { 0, (float)(screen_height - BAR_HEIGHT), (float)screen_width, BAR_HEIGHT };
        Rectangle prev_btn = { bar.x + 16, bar.y + 10, 120, bar.height - 20 };
        Rectangle next_btn = { bar.x + bar.width - 136, bar.y + 10, 120, bar.height - 20 };

        if (CheckCollisionPointRec(mouse, prev_btn)) {
            graph_step_back(&sg_graph);
        } else if (CheckCollisionPointRec(mouse, next_btn)) {
            graph_step_forward(&sg_graph);
        } else {
            /* Click on nodes to jump to them - use dynamic node bounds */
            for (int i = 0; i < sg_graph.node_count; i++) {
                Rectangle node_rect = graph_node_bounds(&sg_graph, i);
                if (CheckCollisionPointRec(mouse, node_rect)) {
                    /* Find this node in walk_order */
                    for (int s = 0; s < sg_graph.walk_len; s++) {
                        if (sg_graph.walk_order[s] == i) {
                            sg_graph.current_step = s;
                            break;
                        }
                    }
                    break;
                }
            }
        }
    }
}

static void sg_draw(void)
{
    /* Title - larger for readability */
    DrawTextQBP("QBP  |  Stern-Gerlach Proof Visualization",
             24, 16, 28, QBP_GOLD);
    DrawTextQBP("Experiment 01: Spin-X state measured on Z-axis",
             24, 44, 16, QBP_TEXT_DIM);

    /* Proof graph */
    graph_draw(&sg_graph);

    /* Info panel (right side) */
    Rectangle panel = {
        (float)(screen_width - PANEL_WIDTH - 10),
        TITLE_HEIGHT,
        PANEL_WIDTH,
        (float)(screen_height - TITLE_HEIGHT - BAR_HEIGHT - 20)
    };
    graph_draw_info_panel(&sg_graph, panel);

    /* Step bar (bottom) */
    Rectangle bar = {
        0,
        (float)(screen_height - BAR_HEIGHT),
        (float)screen_width,
        BAR_HEIGHT
    };
    graph_draw_step_bar(&sg_graph, bar);
}

static void sg_cleanup(void)
{
    /* Nothing to free — all static data */
}

Scene scene_stern_gerlach = {
    .init    = sg_init,
    .update  = sg_update,
    .draw    = sg_draw,
    .cleanup = sg_cleanup,
    .name    = "Stern-Gerlach Proof Visualization"
};
