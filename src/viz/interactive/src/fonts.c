/*
 * fonts.c — Custom font loading for QBP visualization.
 *
 * Loads Atkinson Hyperlegible Next (body + bold) and Mono (code).
 * Falls back to Exo 2, then raylib default.
 */

#include "fonts.h"
#include <stdio.h>

Font g_font = {0};
Font g_font_bold = {0};
Font g_font_mono = {0};
int g_font_loaded = 0;
int g_font_bold_loaded = 0;
int g_font_mono_loaded = 0;

/* Try loading a font from multiple paths (WASM, CWD, build dir) */
static int try_load_font(Font *out, const char *filename, const char *label)
{
    char path[256];
    static const char *prefixes[] = {
        "/assets/fonts/",       /* WASM virtual FS */
        "assets/fonts/",        /* CWD = project root */
        "../../assets/fonts/",  /* CWD = build/native/ */
        NULL
    };

    for (int i = 0; prefixes[i] != NULL; i++) {
        snprintf(path, sizeof(path), "%s%s", prefixes[i], filename);
        *out = LoadFontEx(path, 48, NULL, 0);
        if (out->texture.id > 0) {
            SetTextureFilter(out->texture, TEXTURE_FILTER_BILINEAR);
            fprintf(stderr, "[fonts] Loaded %s from %s\n", label, path);
            return 1;
        }
    }

    fprintf(stderr, "[fonts] Warning: Could not load %s (%s)\n", label, filename);
    return 0;
}

void fonts_init(void)
{
    /* Body font: Atkinson Hyperlegible Next, fallback to Exo 2 */
    g_font_loaded = try_load_font(&g_font,
        "AtkinsonHyperlegibleNext-Regular.ttf", "body font (Atkinson)");
    if (!g_font_loaded) {
        g_font_loaded = try_load_font(&g_font,
            "Exo2-Regular.ttf", "body font (Exo 2 fallback)");
    }

    /* Bold font */
    g_font_bold_loaded = try_load_font(&g_font_bold,
        "AtkinsonHyperlegibleNext-Bold.ttf", "bold font (Atkinson)");

    /* Mono font: Atkinson Hyperlegible Mono */
    g_font_mono_loaded = try_load_font(&g_font_mono,
        "AtkinsonHyperlegibleMono-Regular.ttf", "mono font (Atkinson)");
}

void fonts_cleanup(void)
{
    if (g_font_loaded) {
        UnloadFont(g_font);
        g_font_loaded = 0;
    }
    if (g_font_bold_loaded) {
        UnloadFont(g_font_bold);
        g_font_bold_loaded = 0;
    }
    if (g_font_mono_loaded) {
        UnloadFont(g_font_mono);
        g_font_mono_loaded = 0;
    }
}
