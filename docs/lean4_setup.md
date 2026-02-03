# Lean 4 Setup for QBP Formal Verification

This guide covers installing Lean 4 and building the QBP formal proofs project.

## Prerequisites

- Linux (Ubuntu/Debian or similar)
- `curl` and `git` installed
- Internet connection for downloading dependencies

## Installation

### Step 1: Install elan (Lean version manager)

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Follow the prompts to complete installation. The default options are recommended.

### Step 2: Activate elan

Either restart your terminal, or run:

```bash
source ~/.elan/env
```

### Step 3: Verify installation

```bash
lean --version
```

Expected output: `Lean (version 4.x.x, ...)`

## Building the QBP Proofs Project

### Step 1: Navigate to the proofs directory

```bash
cd proofs
```

### Step 2: Update dependencies

```bash
lake update
```

This downloads mathlib4 and other dependencies. First run may take several minutes.

### Step 3: Get mathlib cache (recommended)

```bash
lake exe cache get
```

This downloads precompiled mathlib binaries, significantly speeding up the build.

### Step 4: Build the project

```bash
lake build
```

Expected output: `Build completed successfully`

## VS Code Extension (Recommended)

For the best development experience, install the Lean 4 extension for VS Code:

1. Open VS Code
2. Go to Extensions (Ctrl+Shift+X)
3. Search for "Lean 4"
4. Install "lean4" by leanprover

The extension provides:
- Syntax highlighting
- Interactive proof state display
- Error messages inline
- Go-to-definition

## Project Structure

```
proofs/
├── QBP.lean              # Root module
├── QBP/
│   ├── Basic.lean        # Core axiom definitions
│   └── Experiments/      # Experiment-specific proofs
├── lakefile.lean         # Build configuration
└── lean-toolchain        # Lean version specification
```

## Troubleshooting

### "lake: command not found"

Ensure elan is in your PATH:

```bash
source ~/.elan/env
```

Or add to your `.bashrc` / `.zshrc`:

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### Build errors after updating mathlib

Clear the build cache and rebuild:

```bash
lake clean
lake exe cache get
lake build
```

### Slow builds

Ensure you've downloaded the mathlib cache:

```bash
lake exe cache get
```

Building mathlib from source can take hours; the cache reduces this to minutes.

### "error: no such file or directory" for QBP.lean

Ensure you're in the `proofs/` directory when running `lake build`.

## Next Steps

After setup is complete:

1. Read `QBP/Basic.lean` to understand the core axiom definitions
2. See `docs/gemini_phase4_guide.md` for the formal verification workflow
3. Start with Issue #55 (Stern-Gerlach formal proof) as the first experiment

## Useful Commands

| Command | Description |
|---------|-------------|
| `lake build` | Build all project files |
| `lake clean` | Remove build artifacts |
| `lake exe cache get` | Download mathlib cache |
| `lake update` | Update dependencies |
| `lean --version` | Check Lean version |
| `elan --version` | Check elan version |
