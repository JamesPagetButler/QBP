/*
 * QBP Design System: Futuristic Steampunk Theme
 *
 * C/raylib port of src/viz/theme.py
 * Colors as raylib Color structs (RGBA 0-255).
 */

#ifndef QBP_THEME_H
#define QBP_THEME_H

#include "raylib.h"

/* --- Primary: The Metals --- */
#define QBP_BRASS       (Color){ 212, 165, 116, 255 }  /* #D4A574 */
#define QBP_COPPER      (Color){ 184, 115,  51, 255 }  /* #B87333 */
#define QBP_BRONZE      (Color){ 205, 127,  50, 255 }  /* #CD7F32 */
#define QBP_STEEL       (Color){ 113, 121, 126, 255 }  /* #71797E */
#define QBP_GOLD        (Color){ 255, 215,   0, 255 }  /* #FFD700 */

/* --- Secondary: The Elements --- */
#define QBP_TEAL        (Color){  42, 157, 143, 255 }  /* #2A9D8F */
#define QBP_VERDIGRIS   (Color){  74, 118, 110, 255 }  /* #4A766E */
#define QBP_AMBER       (Color){ 244, 162,  97, 255 }  /* #F4A261 */
#define QBP_CRIMSON     (Color){ 155,  35,  53, 255 }  /* #9B2335 */
#define QBP_IVORY       (Color){ 255, 254, 240, 255 }  /* #FFFEF0 */

/* --- Backgrounds --- */
#define QBP_PARCHMENT   (Color){ 245, 230, 211, 255 }  /* #F5E6D3 */
#define QBP_DARK_SLATE  (Color){  26,  26,  46, 255 }  /* #1A1A2E */
#define QBP_MIDNIGHT    (Color){  13,  27,  42, 255 }  /* #0D1B2A */

/* --- Utility --- */
#define QBP_SHADOW      (Color){  44,  44,  44, 255 }  /* #2C2C2C */
#define QBP_LIGHT_GRAY  (Color){ 232, 228, 224, 255 }  /* #E8E4E0 */

/* --- Semantic aliases for proof visualization --- */
#define QBP_BG          QBP_DARK_SLATE
#define QBP_NODE_ACTIVE QBP_TEAL
#define QBP_NODE_DEP    QBP_BRASS
#define QBP_NODE_IDLE   QBP_STEEL
#define QBP_EDGE        QBP_COPPER
#define QBP_TEXT_PRIMARY QBP_IVORY
#define QBP_TEXT_DIM     QBP_LIGHT_GRAY
#define QBP_PANEL_BG    QBP_MIDNIGHT

/* --- Angle-emphasis highlight (#229) --- */
#define QBP_ANGLE_GLOW  (Color){ 255, 200,  60, 255 }  /* Warm gold for angle-dependent nodes */
#define QBP_ANGLE_EDGE  (Color){ 255, 180,  40, 200 }  /* Semi-transparent gold for angle edges */
#define QBP_ANGLE_DIM   (Color){  60,  60,  70, 255 }  /* Dimmed non-angle nodes when filter active */

#endif /* QBP_THEME_H */
