/*
 * fonts.c — Custom font loading for QBP visualization.
 */

#include "fonts.h"
#include <stdio.h>

Font g_font = {0};
int g_font_loaded = 0;

void fonts_init(void)
{
    /* Try multiple paths so the font loads regardless of CWD.
     * WASM: assets are preloaded at /assets/ via --preload-file.
     * Native: CWD may be project root or build/native/. */
    static const char *font_paths[] = {
        "/assets/fonts/Exo2-Regular.ttf",       /* WASM virtual FS */
        "assets/fonts/Exo2-Regular.ttf",         /* CWD = project root */
        "../../assets/fonts/Exo2-Regular.ttf",   /* CWD = build/native/ */
        NULL
    };

    for (int i = 0; font_paths[i] != NULL; i++) {
        g_font = LoadFontEx(font_paths[i], 48, NULL, 0);
        if (g_font.texture.id > 0) {
            g_font_loaded = 1;
            /* Enable bilinear filtering for smooth scaling */
            SetTextureFilter(g_font.texture, TEXTURE_FILTER_BILINEAR);
            printf("Loaded custom font: Exo 2 (from %s)\n", font_paths[i]);
            return;
        }
    }

    g_font_loaded = 0;
    printf("Warning: Could not load Exo 2 font, using raylib default\n");
}

void fonts_cleanup(void)
{
    if (g_font_loaded) {
        UnloadFont(g_font);
        g_font_loaded = 0;
    }
}
