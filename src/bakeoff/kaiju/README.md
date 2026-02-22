# Kaiju Engine — QBP Virtual Lab

3D double-slit experiment visualization using the [Kaiju engine](https://github.com/KaijuEngine/kaiju) (Go/Vulkan).

## Directory Layout

```
kaiju/
├── game/           # QBP lab game source (tracked in this repo)
├── engine/         # Kaiju engine clone (gitignored, see Setup)
├── local_libs/     # Symlinked Vulkan/ALSA .so files (gitignored)
├── kaiju-ds        # Built binary (gitignored)
└── content -> engine/src/content
```

## Setup

```bash
# 1. Clone Kaiju engine into engine/
cd src/bakeoff/kaiju
git clone --depth 1 https://github.com/KaijuEngine/kaiju.git engine

# 2. Copy game source files into engine src (they build alongside engine code)
cp game/*.go engine/src/

# 3. Symlink Vulkan and ALSA libraries
mkdir -p local_libs
ln -sf /usr/lib/x86_64-linux-gnu/libvulkan.so local_libs/libvulkan.so
ln -sf /usr/lib/x86_64-linux-gnu/libasound.so local_libs/libasound.so

# 4. Symlink content directory
ln -sf engine/src/content content

# 5. Build
cd engine/src
CGO_LDFLAGS="-L$(pwd)/../../local_libs -Wl,-rpath,$(pwd)/../../local_libs" \
  go build -tags '!editor' -o ../../kaiju-ds .

# 6. Run
cd ../..
QBP_LAB=1 LD_LIBRARY_PATH=./local_libs ./kaiju-ds
```

## Controls

### Desk Controls (FPS crosshair — aim + click)
- **START/STOP**: Toggle particle emitter
- **RATE +/-**: Adjust emission rate (×10 / ÷10)
- **RESET**: Clear detector
- **ORACLE**: Toggle measurement overlay
- **Presets**: Bach, Zeilinger, Tonomura, QBP-weak, QBP-strong
- **SLIT dial**: Click-lock, scroll to adjust slit separation

### Keyboard Shortcuts
- `Enter` — Start/Stop emitter
- `Space` — Freeze particles
- `+/-` — Rate up/down
- `5-9` — Presets
- `O` — Oracle toggle
- `R` — Reset detector
- `Q` — Sit/Stand
- `H` — Toggle hotkey help strip
- `ESC` — Quit
