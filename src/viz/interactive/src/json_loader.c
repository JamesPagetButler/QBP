/*
 * json_loader.c — Load proof graphs from JSON files.
 *
 * Parses the .viz.json schema and populates a ProofGraph structure.
 * Separates data from code, enabling description edits without recompiling.
 */

#include "json_loader.h"
#include "../lib/cJSON.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Helper to safely copy string with truncation warning */
static void safe_strcpy(char *dest, size_t dest_size, const char *src, const char *field_name)
{
    if (!src) {
        dest[0] = '\0';
        return;
    }
    size_t len = strlen(src);
    if (len >= dest_size) {
        fprintf(stderr, "[json_loader] Warning: '%s' truncated from %zu to %zu chars\n",
                field_name ? field_name : "field", len, dest_size - 1);
        len = dest_size - 1;
    }
    memcpy(dest, src, len);
    dest[len] = '\0';
}

/* Helper to get string from cJSON object, returns empty string if missing */
static const char *get_string(const cJSON *obj, const char *key)
{
    const cJSON *item = cJSON_GetObjectItemCaseSensitive(obj, key);
    if (cJSON_IsString(item) && item->valuestring) {
        return item->valuestring;
    }
    return "";
}

/* Parse node kind from string */
static NodeKind parse_kind(const char *kind_str)
{
    if (!kind_str) return NODE_DEFINITION;
    if (strcmp(kind_str, "axiom") == 0) return NODE_AXIOM;
    if (strcmp(kind_str, "theorem") == 0) return NODE_THEOREM;
    return NODE_DEFINITION;
}

/* Find node ID by name in the graph */
static int find_node_by_name(const ProofGraph *g, const char *name)
{
    for (int i = 0; i < g->node_count; i++) {
        if (strcmp(g->nodes[i].name, name) == 0) {
            return i;
        }
    }
    return -1;
}

/* Read entire file into a string (caller must free) */
static char *read_file(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "[json_loader] Cannot open file: %s\n", path);
        return NULL;
    }

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (size <= 0 || size > 1024 * 1024) {  /* 1MB limit */
        fprintf(stderr, "[json_loader] File too large or empty: %s (%ld bytes)\n", path, size);
        fclose(f);
        return NULL;
    }

    char *buf = (char *)malloc(size + 1);
    if (!buf) {
        fprintf(stderr, "[json_loader] Memory allocation failed\n");
        fclose(f);
        return NULL;
    }

    size_t read_size = fread(buf, 1, size, f);
    fclose(f);

    if ((long)read_size != size) {
        fprintf(stderr, "[json_loader] Failed to read file: %s\n", path);
        free(buf);
        return NULL;
    }

    buf[size] = '\0';
    return buf;
}

int graph_load_json(ProofGraph *g, const char *json_path)
{
    /* Defensive null checks */
    if (!g || !json_path) {
        fprintf(stderr, "[json_loader] Error: null argument to graph_load_json\n");
        return -1;
    }

    /* Initialize graph */
    memset(g, 0, sizeof(*g));

    /* Read file */
    char *json_str = read_file(json_path);
    if (!json_str) {
        return -1;
    }

    /* Parse JSON */
    cJSON *root = cJSON_Parse(json_str);
    free(json_str);

    if (!root) {
        const char *err = cJSON_GetErrorPtr();
        fprintf(stderr, "[json_loader] JSON parse error: %s\n", err ? err : "unknown");
        return -1;
    }

    /* Get walk_order array - this defines both node order and which nodes exist */
    const cJSON *walk_order = cJSON_GetObjectItemCaseSensitive(root, "walk_order");
    if (!cJSON_IsArray(walk_order)) {
        fprintf(stderr, "[json_loader] Missing or invalid 'walk_order' array\n");
        cJSON_Delete(root);
        return -1;
    }

    int walk_len = cJSON_GetArraySize(walk_order);
    if (walk_len > MAX_NODES) {
        fprintf(stderr, "[json_loader] Too many nodes: %d (max %d)\n", walk_len, MAX_NODES);
        cJSON_Delete(root);
        return -1;
    }

    /* Get nodes object */
    const cJSON *nodes = cJSON_GetObjectItemCaseSensitive(root, "nodes");
    if (!cJSON_IsObject(nodes)) {
        fprintf(stderr, "[json_loader] Missing or invalid 'nodes' object\n");
        cJSON_Delete(root);
        return -1;
    }

    /* First pass: create nodes from walk_order to establish IDs */
    g->node_count = walk_len;
    g->walk_len = walk_len;

    const cJSON *walk_item;
    int node_id = 0;
    cJSON_ArrayForEach(walk_item, walk_order) {
        if (!cJSON_IsString(walk_item)) {
            fprintf(stderr, "[json_loader] walk_order item is not a string\n");
            cJSON_Delete(root);
            return -1;
        }

        const char *node_name = walk_item->valuestring;
        const cJSON *node_json = cJSON_GetObjectItemCaseSensitive(nodes, node_name);
        if (!node_json) {
            fprintf(stderr, "[json_loader] Node '%s' in walk_order not found in nodes\n", node_name);
            cJSON_Delete(root);
            return -1;
        }

        ProofNode *n = &g->nodes[node_id];
        n->id = node_id;

        /* Copy node name */
        safe_strcpy(n->name, MAX_NAME_LEN, node_name, "name");

        /* Copy display name */
        safe_strcpy(n->display_name, MAX_DISPLAY_NAME_LEN, get_string(node_json, "display_name"), "display_name");
        if (n->display_name[0] == '\0') {
            /* Fallback to node name if no display name */
            safe_strcpy(n->display_name, MAX_DISPLAY_NAME_LEN, node_name, "display_name");
        }

        /* Parse kind */
        n->kind = parse_kind(get_string(node_json, "kind"));

        /* Copy 4 levels of descriptions */
        safe_strcpy(n->level4_formal, MAX_FORMAL_LEN, get_string(node_json, "L4_formal"), "L4_formal");
        safe_strcpy(n->level3_math, MAX_MATH_LEN, get_string(node_json, "L3_math"), "L3_math");
        safe_strcpy(n->level2_physical, MAX_PHYSICAL_LEN, get_string(node_json, "L2_physical"), "L2_physical");
        safe_strcpy(n->level1_intuitive, MAX_INTUITIVE_LEN, get_string(node_json, "L1_intuitive"), "L1_intuitive");
        safe_strcpy(n->key_insight, MAX_INSIGHT_LEN, get_string(node_json, "key_insight"), "key_insight");

        /* Parse tags (comma-separated string or JSON array) */
        const cJSON *tags_json = cJSON_GetObjectItemCaseSensitive(node_json, "tags");
        if (cJSON_IsString(tags_json) && tags_json->valuestring) {
            safe_strcpy(n->tags, MAX_TAGS_LEN, tags_json->valuestring, "tags");
        } else if (cJSON_IsArray(tags_json)) {
            /* Join array elements with commas */
            n->tags[0] = '\0';
            int pos = 0;
            const cJSON *tag_item;
            cJSON_ArrayForEach(tag_item, tags_json) {
                if (cJSON_IsString(tag_item) && tag_item->valuestring) {
                    int len = (int)strlen(tag_item->valuestring);
                    if (pos + len + 2 < MAX_TAGS_LEN) {
                        if (pos > 0) n->tags[pos++] = ',';
                        memcpy(n->tags + pos, tag_item->valuestring, len);
                        pos += len;
                    }
                }
            }
            n->tags[pos] = '\0';
        } else {
            n->tags[0] = '\0';
        }

        /* Precompute angle tag flag */
        n->has_tag_angle = (strstr(n->tags, "angle") != NULL) ? 1 : 0;

        /* Parse proof_role */
        safe_strcpy(n->proof_role, sizeof(n->proof_role), get_string(node_json, "proof_role"), "proof_role");

        /* Set walk order */
        g->walk_order[node_id] = node_id;

        node_id++;
    }

    /* Second pass: resolve dependencies now that all nodes have IDs */
    node_id = 0;
    cJSON_ArrayForEach(walk_item, walk_order) {
        const char *node_name = walk_item->valuestring;
        const cJSON *node_json = cJSON_GetObjectItemCaseSensitive(nodes, node_name);
        ProofNode *n = &g->nodes[node_id];

        const cJSON *deps = cJSON_GetObjectItemCaseSensitive(node_json, "depends_on");
        if (cJSON_IsArray(deps)) {
            int dep_count = cJSON_GetArraySize(deps);
            if (dep_count > MAX_DEPS) {
                fprintf(stderr, "[json_loader] Warning: node '%s' has %d deps, truncating to %d\n",
                        node_name, dep_count, MAX_DEPS);
                dep_count = MAX_DEPS;
            }

            const cJSON *dep_item;
            int dep_idx = 0;
            cJSON_ArrayForEach(dep_item, deps) {
                if (dep_idx >= MAX_DEPS) break;
                if (cJSON_IsString(dep_item)) {
                    int dep_id = find_node_by_name(g, dep_item->valuestring);
                    if (dep_id >= 0) {
                        n->deps[dep_idx++] = dep_id;
                    } else {
                        /* Missing dependency is a fatal error - proof structure would be corrupted */
                        fprintf(stderr, "[json_loader] Error: dependency '%s' not found for node '%s'\n",
                                dep_item->valuestring, node_name);
                        cJSON_Delete(root);
                        return -1;
                    }
                }
            }
            n->dep_count = dep_idx;
        }

        node_id++;
    }

    g->current_step = 0;

    cJSON_Delete(root);

    fprintf(stderr, "[json_loader] Loaded %d nodes from %s\n", g->node_count, json_path);
    return 0;
}
