# Visualization Guide

## Overview

This project uses visualization to:
- Demonstrate quaternion rotations and physics
- Verify simulations against physical intuition
- Provide accessible, animation-based output (motion over dense text)

## Stack

| Tool | Purpose | Output |
|------|---------|--------|
| **vpython** | Interactive 3D physics | Browser (localhost) |
| **matplotlib** | Static plots, simple animations | PNG, GIF, inline |

## Quick Start

```bash
# Install dependencies
uv sync --extra dev

# Run quaternion rotation demo
uv run python src/viz/quaternion_rotation.py
```

Opens browser with interactive 3D visualization.

## Usage in Code

```python
from viz.quaternion_rotation import visualize_rotation

# Visualize rotation by 90 degrees around z-axis
visualize_rotation(axis=[0, 0, 1], angle_degrees=90)
```

## Adding New Visualizations

1. Create script in `src/viz/`
2. Use vpython for 3D interactive, matplotlib for 2D/static
3. Document with docstring explaining the physics

## Accessibility Notes

- Prefer animation over text-heavy output
- Use high contrast colors (defaults: white background, bold primary colors)
- Label axes and objects clearly
- Keep frame rates smooth (30+ fps)
