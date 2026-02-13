#!/usr/bin/env bash
# Install system graphics libraries required for QBP Simulation Engine (Phase 4e)
# Usage: sudo bash scripts/install-graphics-deps.sh

set -euo pipefail

if [ "$(id -u)" -ne 0 ]; then
    echo "Error: This script must be run with sudo"
    exit 1
fi

echo "Installing graphics development libraries for raylib-go..."

apt-get update -qq
apt-get install -y \
    libgl1-mesa-dev \
    libxi-dev \
    libxcursor-dev \
    libxrandr-dev \
    libxinerama-dev \
    libwayland-dev \
    libxkbcommon-dev

echo ""
echo "Done. You can now build the simulation:"
echo "  cd src/simulation && go build -o qbp-sim . && ./qbp-sim"
