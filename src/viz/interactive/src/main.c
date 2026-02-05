/*
 * main.c — QBP Interactive Proof Visualization
 *
 * Entry point for the raylib/Emscripten application.
 * Dispatches to experiment scenes via the Scene interface.
 */

#include <stddef.h>

#include "raylib.h"
#include "scene.h"
#include "theme.h"

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#endif

/* --- Scene registry --- */
extern Scene scene_stern_gerlach;

static Scene *current_scene = NULL;

#define SCREEN_W 1100
#define SCREEN_H  700

static void frame_loop(void)
{
    if (current_scene && current_scene->update) {
        current_scene->update();
    }

    BeginDrawing();
    ClearBackground(QBP_BG);

    if (current_scene && current_scene->draw) {
        current_scene->draw();
    }

    EndDrawing();
}

int main(void)
{
    InitWindow(SCREEN_W, SCREEN_H, "QBP Interactive Proof Visualization");

#ifndef __EMSCRIPTEN__
    SetTargetFPS(60);
#endif

    /* Select scene — currently only Stern-Gerlach */
    current_scene = &scene_stern_gerlach;
    if (current_scene->init) {
        current_scene->init(SCREEN_W, SCREEN_H);
    }

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

    CloseWindow();
    return 0;
}
