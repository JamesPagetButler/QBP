# QBP Verified Simulation Engine

Interactive 3D simulation of quantum physics experiments with real-time Verification & Validation (V&V) against Lean-proven physics oracle.

## Prerequisites

### Go (1.21+)

```bash
# Check version
go version

# If not installed or too old:
wget https://go.dev/dl/go1.23.6.linux-amd64.tar.gz
sudo tar -C /usr/local -xzf go1.23.6.linux-amd64.tar.gz
export PATH=$PATH:/usr/local/go/bin
```

### System Graphics Libraries

```bash
# Ubuntu/Debian
sudo apt-get install -y \
  libgl1-mesa-dev \
  libxi-dev \
  libxcursor-dev \
  libxrandr-dev \
  libxinerama-dev \
  libwayland-dev \
  libxkbcommon-dev

# Fedora/RHEL
sudo dnf install -y \
  mesa-libGL-devel \
  libXi-devel \
  libXcursor-devel \
  libXrandr-devel \
  libXinerama-devel \
  wayland-devel \
  libxkbcommon-devel
```

## Build & Run

```bash
cd src/simulation

# Download dependencies
go mod download

# Build
go build -o qbp-sim .

# Run
./qbp-sim
# or directly:
go run .
```

## Controls

| Input | Action |
|-------|--------|
| Mouse drag | Rotate camera |
| Scroll | Zoom in/out |
| Left/Right arrows | Fine-adjust angle |
| Slider | Set theta (0-180 degrees) |
| Space | Pause/Resume simulation |
| R | Reset statistics |
| H | Toggle help overlay |
| ESC | Quit |

## Architecture

```
src/simulation/
├── main.go              # Entry point, window setup, main loop
├── physics/
│   ├── oracle.go        # Lean oracle integration (JSON + analytical fallback)
│   ├── oracle_test.go   # Oracle verification tests
│   └── qbp_oracle.h     # C header for future FFI integration
├── scene/
│   ├── apparatus.go     # 3D Stern-Gerlach apparatus rendering
│   └── particles.go     # Particle stream simulation
└── ui/
    └── controls.go      # Parameter sliders, V&V status display
```

## Physics Oracle

The simulation uses a physics oracle derived from Lean 4 formal proofs:

1. **Primary:** Load committed `tests/oracle_predictions.json` (no Lean needed)
2. **Fallback:** Analytical formula cos²(θ/2) matching the proven result
3. **Future:** Direct FFI to Lean-compiled shared library

## V&V Methodology

The simulation enables human Verification & Validation:

1. **Setup Verification** — Inspect apparatus configuration
2. **Behavior Verification** — Watch particle dynamics
3. **Results Validation** — Compare simulation statistics to oracle predictions

See `docs/workflows/verification_validation.md` for full methodology.

## Running Tests

```bash
# Physics oracle tests (no graphics deps needed)
go test ./physics/ -v

# Full build (requires graphics libs)
go build .
```
