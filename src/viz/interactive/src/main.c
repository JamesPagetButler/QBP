/*
 * main.c — QBP Interactive Proof Visualization
 *
 * Entry point for the raylib/Emscripten application.
 * Dispatches to experiment scenes via the Scene interface.
 *
 * Scene selection:
 *   Press '1' for Experiment 01 (Stern-Gerlach)
 *   Press '2' for Experiment 01b (Angle-Dependent)
 */

#include <stddef.h>

#include "raylib.h"
#include "scene.h"
#include "theme.h"
#include "fonts.h"

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#endif

/* --- Scene registry --- */
extern Scene scene_stern_gerlach;
extern Scene scene_angle_dependent;

static Scene *scenes[] = {
    &scene_stern_gerlach,
    &scene_angle_dependent,
};
static int scene_count = sizeof(scenes) / sizeof(scenes[0]);
static int current_scene_idx = 0;
static Scene *current_scene = NULL;

#define SCREEN_W 1100
#define SCREEN_H  700

static void switch_scene(int idx)
{
    if (idx < 0 || idx >= scene_count) return;
    if (idx == current_scene_idx && current_scene != NULL) return;

    /* Cleanup old scene */
    if (current_scene && current_scene->cleanup) {
        current_scene->cleanup();
    }

    /* Switch to new scene */
    current_scene_idx = idx;
    current_scene = scenes[idx];

    if (current_scene->init) {
        current_scene->init(SCREEN_W, SCREEN_H);
    }
}

static void frame_loop(void)
{
    /* Scene selection via number keys */
    if (IsKeyPressed(KEY_ONE) || IsKeyPressed(KEY_KP_1)) {
        switch_scene(0);  /* Stern-Gerlach */
    }
    if (IsKeyPressed(KEY_TWO) || IsKeyPressed(KEY_KP_2)) {
        switch_scene(1);  /* Angle-Dependent */
    }

    if (current_scene && current_scene->update) {
        current_scene->update();
    }

    BeginDrawing();
    ClearBackground(QBP_BG);

    if (current_scene && current_scene->draw) {
        current_scene->draw();
    }

    /* Draw scene selector hint at bottom-left */
    DrawTextQBP("[1] Stern-Gerlach  [2] Angle-Dependent",
                8, SCREEN_H - 20, 12, QBP_TEXT_DIM);

    EndDrawing();
}

int main(void)
{
    InitWindow(SCREEN_W, SCREEN_H, "QBP Interactive Proof Visualization");

    /* Initialize custom fonts */
    fonts_init();

#ifndef __EMSCRIPTEN__
    SetTargetFPS(60);
#endif

    /* Default to Stern-Gerlach scene */
    switch_scene(0);

#ifdef __EMSCRIPTEN__
    emscripten_set_main_loop(frame_loop, 0, 1);
#else
    while (!WindowShouldClose()) {
        frame_loop();
    }
#endif

    if (current_scene && current_scene->cleanup) {
        current_scene->cleanup();
    }

    /* Cleanup fonts */
    fonts_cleanup();

    CloseWindow();
    return 0;
}
