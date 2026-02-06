/*
 * json_loader.h — Load proof graphs from JSON files.
 *
 * Enables data-driven visualization: edit JSON files without recompiling.
 * Uses cJSON library for parsing.
 */

#ifndef QBP_JSON_LOADER_H
#define QBP_JSON_LOADER_H

#include "proof_graph.h"

/*
 * Load a proof graph from a JSON file.
 *
 * Expected JSON schema:
 * {
 *   "experiment_id": "01_stern_gerlach",
 *   "title": "...",
 *   "walk_order": ["node1", "node2", ...],
 *   "nodes": {
 *     "node1": {
 *       "display_name": "...",
 *       "kind": "definition|theorem|axiom",
 *       "L4_formal": "...",
 *       "L3_math": "...",
 *       "L2_physical": "...",
 *       "L1_intuitive": "...",
 *       "key_insight": "...",
 *       "depends_on": ["dep1", "dep2"]
 *     }
 *   }
 * }
 *
 * @param g         Pointer to ProofGraph to populate
 * @param json_path Path to the JSON file
 * @return 0 on success, -1 on error (file not found, parse error, etc.)
 */
int graph_load_json(ProofGraph *g, const char *json_path);

#endif /* QBP_JSON_LOADER_H */
