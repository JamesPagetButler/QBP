#!/usr/bin/env bash
# Engine Bake-Off Benchmark Runner
# Builds both prototypes, runs benchmarks, prints comparison table.
#
# Usage: cd src/bakeoff && bash run_benchmark.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
RAYLIB_DIR="$SCRIPT_DIR/raylib"
KAIJU_DIR="$SCRIPT_DIR/kaiju/engine/src"
RESULTS_DIR="$SCRIPT_DIR/bench_results"
mkdir -p "$RESULTS_DIR"

GO=/usr/local/go/bin/go

echo "═══════════════════════════════════════════════════════"
echo "  QBP Double-Slit Engine Bake-Off — Benchmark Suite"
echo "═══════════════════════════════════════════════════════"
echo ""

# ── Step 1: Physics Engine Benchmarks (pure Go, no GPU) ──────────────
echo "▸ Running physics engine benchmarks..."
cd "$SCRIPT_DIR"
$GO test -bench . -benchtime 3s -count 1 -v 2>&1 | tee "$RESULTS_DIR/physics_bench.txt"
echo ""

# ── Step 2: Build both prototypes ────────────────────────────────────
echo "▸ Building Raylib prototype..."
cd "$RAYLIB_DIR"
$GO build -o ds-bakeoff . 2>&1
echo "  ✓ Raylib built ($(du -h ds-bakeoff | cut -f1))"

echo "▸ Building Kaiju prototype..."
cd "$KAIJU_DIR"
CGO_LDFLAGS="-L$SCRIPT_DIR/kaiju/local_libs" $GO build -o doubleslit . 2>&1
echo "  ✓ Kaiju built ($(du -h doubleslit | cut -f1))"
echo ""

# ── Step 3: Run Raylib benchmark ─────────────────────────────────────
echo "▸ Running Raylib benchmark (uncapped FPS, auto-exit at 25K particles)..."
cd "$RAYLIB_DIR"
./ds-bakeoff --benchmark 2>&1 | tee "$RESULTS_DIR/raylib_output.txt"
cp bench_raylib.csv "$RESULTS_DIR/" 2>/dev/null || true
echo ""

# ── Step 4: Run Kaiju benchmark ──────────────────────────────────────
echo "▸ Running Kaiju benchmark..."
cd "$KAIJU_DIR"

# Try AMDVLK first (RADV crashes on gfx1201)
KAIJU_ENV=""
if [ -f /etc/vulkan/icd.d/amd_icd64.json ]; then
    KAIJU_ENV="VK_ICD_FILENAMES=/etc/vulkan/icd.d/amd_icd64.json"
elif [ -f /home/prime/.local/share/vulkan/icd.d/amd_icd64.json ]; then
    KAIJU_ENV="VK_ICD_FILENAMES=/home/prime/.local/share/vulkan/icd.d/amd_icd64.json"
elif [ -f /usr/share/vulkan/icd.d/amd_icd64.json ]; then
    KAIJU_ENV="VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/amd_icd64.json"
fi

if [ -n "$KAIJU_ENV" ]; then
    echo "  Using: $KAIJU_ENV"
    env $KAIJU_ENV QBP_BENCHMARK=1 LD_LIBRARY_PATH="$SCRIPT_DIR/kaiju/local_libs:${LD_LIBRARY_PATH:-}" \
        ./doubleslit 2>&1 | tee "$RESULTS_DIR/kaiju_output.txt"
else
    echo "  ⚠ No AMDVLK found — Kaiju may crash on RADV. Trying anyway..."
    QBP_BENCHMARK=1 LD_LIBRARY_PATH="$SCRIPT_DIR/kaiju/local_libs:${LD_LIBRARY_PATH:-}" \
        ./doubleslit 2>&1 | tee "$RESULTS_DIR/kaiju_output.txt"
fi
cp bench_kaiju.csv "$RESULTS_DIR/" 2>/dev/null || true
echo ""

# ── Step 5: Comparison Table ─────────────────────────────────────────
echo "═══════════════════════════════════════════════════════"
echo "  COMPARISON TABLE"
echo "═══════════════════════════════════════════════════════"
echo ""

RAYLIB_CSV="$RESULTS_DIR/bench_raylib.csv"
KAIJU_CSV="$RESULTS_DIR/bench_kaiju.csv"

if [ -f "$RAYLIB_CSV" ] && [ -f "$KAIJU_CSV" ]; then
    printf "%-12s │ %-12s %-12s │ %-12s %-12s │ %-8s\n" \
        "Particles" "Raylib FPS" "Kaiju FPS" "Raylib RSS" "Kaiju RSS" "Winner"
    printf "─────────────┼──────────────────────────┼──────────────────────────┼─────────\n"

    # Parse CSVs (skip header)
    paste -d'|' <(tail -n +2 "$RAYLIB_CSV") <(tail -n +2 "$KAIJU_CSV") | while IFS='|' read -r rline kline; do
        r_particles=$(echo "$rline" | cut -d, -f2)
        r_fps=$(echo "$rline" | cut -d, -f3)
        r_rss=$(echo "$rline" | cut -d, -f5)
        k_fps=$(echo "$kline" | cut -d, -f3)
        k_rss=$(echo "$kline" | cut -d, -f5)

        # Determine winner by FPS
        winner="tie"
        if command -v bc &>/dev/null; then
            cmp=$(echo "$r_fps > $k_fps" | bc -l 2>/dev/null || echo "0")
            if [ "$cmp" = "1" ]; then winner="Raylib"; else winner="Kaiju"; fi
        fi

        printf "%-12s │ %-12s %-12s │ %-12s %-12s │ %-8s\n" \
            "$r_particles" "$r_fps" "$k_fps" "${r_rss}MB" "${k_rss}MB" "$winner"
    done
elif [ -f "$RAYLIB_CSV" ]; then
    echo "Only Raylib results available (Kaiju benchmark failed):"
    echo ""
    printf "%-12s │ %-12s %-12s %-12s\n" "Particles" "FPS" "Frame(ms)" "RSS(MB)"
    printf "─────────────┼──────────────────────────────────────\n"
    tail -n +2 "$RAYLIB_CSV" | while IFS=, read -r eng particles fps ft rss; do
        printf "%-12s │ %-12s %-12s %-12s\n" "$particles" "$fps" "$ft" "$rss"
    done
else
    echo "No benchmark results found!"
fi

echo ""
echo "Raw results saved to: $RESULTS_DIR/"
echo "Done."
