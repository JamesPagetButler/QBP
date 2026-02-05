/*
 * scene.h — Scene interface for experiment visualizations.
 *
 * Each experiment implements init/update/draw/cleanup.
 * New experiments add a .c file in scenes/ and register in main.c.
 */

#ifndef QBP_SCENE_H
#define QBP_SCENE_H

typedef struct {
    void (*init)(int screen_w, int screen_h);
    void (*update)(void);
    void (*draw)(void);
    void (*cleanup)(void);
    const char *name;
} Scene;

#endif /* QBP_SCENE_H */
