/*
 * fonts.h — Custom font management for QBP visualization.
 *
 * Uses Exo 2, a clean readable font similar to Purista.
 */

#ifndef QBP_FONTS_H
#define QBP_FONTS_H

#include "raylib.h"

/* Global font instance */
extern Font g_font;
extern int g_font_loaded;

/* Initialize fonts - call after InitWindow() */
void fonts_init(void);

/* Cleanup fonts - call before CloseWindow() */
void fonts_cleanup(void);

/* Helper to draw text with our custom font */
static inline void DrawTextQBP(const char *text, int x, int y, int fontSize, Color color)
{
    if (g_font_loaded) {
        Vector2 pos = { (float)x, (float)y };
        DrawTextEx(g_font, text, pos, (float)fontSize, 1.0f, color);
    } else {
        DrawText(text, x, y, fontSize, color);
    }
}

/* Measure text width with our custom font */
static inline int MeasureTextQBP(const char *text, int fontSize)
{
    if (g_font_loaded) {
        Vector2 size = MeasureTextEx(g_font, text, (float)fontSize, 1.0f);
        return (int)size.x;
    } else {
        return MeasureText(text, fontSize);
    }
}

#endif /* QBP_FONTS_H */
