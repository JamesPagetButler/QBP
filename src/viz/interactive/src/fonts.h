/*
 * fonts.h — Custom font management for QBP visualization.
 *
 * Uses Atkinson Hyperlegible Next (body) and Atkinson Hyperlegible Mono (code).
 * Designed for maximum readability, especially for dyslexic users.
 * See: https://brailleinstitute.org/freefont
 */

#ifndef QBP_FONTS_H
#define QBP_FONTS_H

#include "raylib.h"

/* Global font instances */
extern Font g_font;          /* Body/UI: Atkinson Hyperlegible Next */
extern Font g_font_bold;     /* Bold:    Atkinson Hyperlegible Next Bold */
extern Font g_font_mono;     /* Code:    Atkinson Hyperlegible Mono */
extern int g_font_loaded;
extern int g_font_bold_loaded;
extern int g_font_mono_loaded;

/* Initialize fonts - call after InitWindow() */
void fonts_init(void);

/* Cleanup fonts - call before CloseWindow() */
void fonts_cleanup(void);

/* Letter spacing: +0.12em equivalent for readability (BDA recommendation).
 * raylib spacing param is in pixels, not em. At ~8px per em at 16px font,
 * 0.12em ≈ 2.0px. We use 2.0f as a good baseline. */
#define QBP_LETTER_SPACING 2.0f

/* Helper to draw text with body font (Atkinson Hyperlegible) */
static inline void DrawTextQBP(const char *text, int x, int y, int fontSize, Color color)
{
    if (g_font_loaded) {
        Vector2 pos = { (float)x, (float)y };
        DrawTextEx(g_font, text, pos, (float)fontSize, QBP_LETTER_SPACING, color);
    } else {
        DrawText(text, x, y, fontSize, color);
    }
}

/* Helper to draw text with bold font */
static inline void DrawTextQBPBold(const char *text, int x, int y, int fontSize, Color color)
{
    Font f = g_font_bold_loaded ? g_font_bold : g_font;
    if (g_font_loaded || g_font_bold_loaded) {
        Vector2 pos = { (float)x, (float)y };
        DrawTextEx(f, text, pos, (float)fontSize, QBP_LETTER_SPACING, color);
    } else {
        DrawText(text, x, y, fontSize, color);
    }
}

/* Helper to draw text with mono font (for Lean code / L4 formal) */
static inline void DrawTextQBPMono(const char *text, int x, int y, int fontSize, Color color)
{
    if (g_font_mono_loaded) {
        Vector2 pos = { (float)x, (float)y };
        DrawTextEx(g_font_mono, text, pos, (float)fontSize, QBP_LETTER_SPACING, color);
    } else {
        DrawTextQBP(text, x, y, fontSize, color);
    }
}

/* Measure text width with body font */
static inline int MeasureTextQBP(const char *text, int fontSize)
{
    if (g_font_loaded) {
        Vector2 size = MeasureTextEx(g_font, text, (float)fontSize, QBP_LETTER_SPACING);
        return (int)size.x;
    } else {
        return MeasureText(text, fontSize);
    }
}

/* Measure text width with mono font */
static inline int MeasureTextQBPMono(const char *text, int fontSize)
{
    if (g_font_mono_loaded) {
        Vector2 size = MeasureTextEx(g_font_mono, text, (float)fontSize, QBP_LETTER_SPACING);
        return (int)size.x;
    } else {
        return MeasureTextQBP(text, fontSize);
    }
}

#endif /* QBP_FONTS_H */
