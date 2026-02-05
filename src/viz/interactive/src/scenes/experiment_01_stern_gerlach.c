/*
 * experiment_01_stern_gerlach.c — Stern-Gerlach proof visualization scene.
 *
 * Implements the Scene interface for the Stern-Gerlach experiment.
 * Users step through the proof dependency tree, seeing how axioms
 * connect to the 50/50 probability result.
 */

#include "../scene.h"
#include "../proof_graph.h"
#include "../theme.h"
#include "raylib.h"

static ProofGraph sg_graph;
static int screen_width;
static int screen_height;

/* Layout constants */
#define PANEL_WIDTH   320
#define BAR_HEIGHT     40
#define TITLE_HEIGHT   50

static void sg_init(int sw, int sh)
{
    screen_width = sw;
    screen_height = sh;

    graph_init_stern_gerlach(&sg_graph);

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

    /* Click on nodes to jump to them */
    if (IsMouseButtonPressed(MOUSE_BUTTON_LEFT)) {
        Vector2 mouse = GetMousePosition();
        for (int i = 0; i < sg_graph.node_count; i++) {
            Vector2 np = sg_graph.nodes[i].pos;
            if (mouse.x >= np.x - 90 && mouse.x <= np.x + 90 &&
                mouse.y >= np.y - 20 && mouse.y <= np.y + 20) {
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

static void sg_draw(void)
{
    /* Title */
    DrawText("QBP  |  Stern-Gerlach Proof Visualization",
             20, 14, 22, QBP_GOLD);
    DrawText("Experiment 01: Spin-X state measured on Z-axis",
             20, 36, 12, QBP_TEXT_DIM);

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
