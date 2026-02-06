/*
 * fonts.c — Custom font loading for QBP visualization.
 */

#include "fonts.h"
#include <stdio.h>

Font g_font = {0};
int g_font_loaded = 0;

void fonts_init(void)
{
    /* Load Exo 2 font at high resolution for crisp rendering at various sizes */
    g_font = LoadFontEx("/assets/fonts/Exo2-Regular.ttf", 48, NULL, 0);

    if (g_font.texture.id > 0) {
        g_font_loaded = 1;
        /* Enable bilinear filtering for smooth scaling */
        SetTextureFilter(g_font.texture, TEXTURE_FILTER_BILINEAR);
        printf("Loaded custom font: Exo 2\n");
    } else {
        g_font_loaded = 0;
        printf("Warning: Could not load custom font, using default\n");
    }
}

void fonts_cleanup(void)
{
    if (g_font_loaded) {
        UnloadFont(g_font);
        g_font_loaded = 0;
    }
}
