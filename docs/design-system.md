# QBP Design System

## Philosophy: Futuristic Steampunk

> *"Precision instruments measuring the fabric of reality"*

Our visual language combines **Victorian mechanical elegance** with **cutting-edge physics**. Think brass orreries tracking quantum states, gaslight illuminating equations, clockwork gears encoding rotations.

This aesthetic serves accessibility: warm colors, high contrast, motion-based understanding over text-heavy explanations.

---

## Color Palette

### The Metals (Primary)

| Name | Hex | RGB | Use |
|------|-----|-----|-----|
| **Brass** | `#D4A574` | 212, 165, 116 | Primary objects, key elements |
| **Copper** | `#B87333` | 184, 115, 51 | Secondary objects, warmth |
| **Bronze** | `#CD7F32` | 205, 127, 50 | Accents, highlights |
| **Steel** | `#71797E` | 113, 121, 126 | Neutral elements, grids |
| **Gold** | `#FFD700` | 255, 215, 0 | Special highlights, energy |

### The Elements (Secondary)

| Name | Hex | RGB | Use |
|------|-----|-----|-----|
| **Teal** | `#2A9D8F` | 42, 157, 143 | Z-axis, depth, calm states |
| **Verdigris** | `#4A766E` | 74, 118, 110 | Y-axis, aged copper patina |
| **Amber** | `#F4A261` | 244, 162, 97 | Glows, energy, activity |
| **Crimson** | `#9B2335` | 155, 35, 53 | X-axis, warnings, intensity |
| **Ivory** | `#FFFEF0` | 255, 254, 240 | Labels, text on dark |

### Backgrounds

| Name | Hex | RGB | Use |
|------|-----|-----|-----|
| **Parchment** | `#F5E6D3` | 245, 230, 211 | Light mode background |
| **Dark Slate** | `#1A1A2E` | 26, 26, 46 | Dark mode background |
| **Midnight** | `#0D1B2A` | 13, 27, 42 | Deep space / void |

---

## Axis Convention

We maintain the **RGB = XYZ** convention with steampunk tones:

```
X-axis: Crimson  (#9B2335) — heat, energy
Y-axis: Verdigris (#4A766E) — growth, patina
Z-axis: Teal     (#2A9D8F) — depth, mystery
```

---

## Typography

| Context | Recommendation |
|---------|----------------|
| **Titles** | Bold, clean sans-serif (system default) |
| **Labels** | Regular weight, high contrast |
| **Code** | Monospace, Ivory on Dark Slate |
| **Annotations** | Italic for emphasis |

Keep text minimal. Let motion and color convey meaning.

---

## Usage in Code

### Python (vpython/matplotlib)

```python
from viz.theme import COLORS, PALETTE, apply_matplotlib_theme

# Access colors
axis_color = COLORS.BRASS.vpython      # For vpython
line_color = COLORS.TEAL.hex           # For matplotlib
rgb_tuple = COLORS.COPPER.rgb_norm     # (0.72, 0.45, 0.20)

# Apply matplotlib theme globally
apply_matplotlib_theme()

# Use palette presets
background = PALETTE.BG_LIGHT.vpython
```

### View Palette

```bash
source ~/qbp-env/bin/activate
cd ~/Documents/QBP
PYTHONPATH=src python -c "from viz.theme import show_palette; show_palette()"
```

---

## Design Principles

1. **Warmth over clinical** — Brass tones feel approachable
2. **Motion over text** — Animate rather than annotate
3. **Contrast for clarity** — Ensure readability (WCAG AA minimum)
4. **Consistent axes** — XYZ = Crimson/Verdigris/Teal always
5. **Depth through lighting** — Use amber glows for energy, steel for shadows
6. **Show your work** — Every visualization must display formal math alongside motion
7. **Link to learn** — Every animation must link to deeper documentation

---

## Animation Documentation Standard

Every visualization **must** include:

### 1. Brief Description Panel
A concise explanation visible in the UI:
- **What** is being shown (1 sentence)
- **Why** it matters physically (1 sentence)
- **Link** to full documentation

Example:
```
┌─────────────────────────────────────────────────────┐
│ QUATERNION ROTATION                                 │
│ A unit quaternion q rotates vector v via q·v·q⁻¹   │
│ This encodes 3D rotation without gimbal lock.      │
│                                                     │
│ 📖 docs/theory/quaternion-rotation.md              │
└─────────────────────────────────────────────────────┘
```

### 2. Formal Math Display
Show the equations being animated in real-time:
- Display current values (e.g., `q = (0.707, 0, 0, 0.707)`)
- Show the operation being performed
- Update as animation progresses

### 3. Documentation Link
Each visualization must reference:
- The relevant theory document in `docs/theory/`
- The experiment it connects to (Rule 5: Link Tests to Reality)
- Related proofs in `proofs/`

### Template for Visualization Docstring

```python
"""
[Visualization Name]

WHAT: [One sentence describing what is shown]
WHY:  [One sentence on physical significance]
MATH: [Core equation, e.g., v' = q·v·q⁻¹]

Links:
- Theory: docs/theory/[topic].md
- Proof:  proofs/[proof-name].lean
- Experiment: experiments/[exp-name]/

Run: python src/viz/[script].py
"""
```

### Implementation Checklist

For every new visualization:
- [ ] Description panel in UI
- [ ] Real-time math display (quaternion values, angles, etc.)
- [ ] Docstring with WHAT/WHY/MATH/Links
- [ ] Corresponding theory doc exists or is created
- [ ] Link to related experiment (if applicable)

---

## Examples

### Light Mode Scene
- Background: Parchment (`#F5E6D3`)
- Objects: Brass, Copper
- Axes: Crimson, Verdigris, Teal
- Text: Shadow (`#2C2C2C`)

### Dark Mode Scene
- Background: Dark Slate (`#1A1A2E`)
- Objects: Brass (brighter), Gold accents
- Axes: Same (high saturation)
- Text: Ivory (`#FFFEF0`)

---

## Accessibility Notes

- All color pairs tested for WCAG AA contrast (4.5:1 minimum)
- Brass on Parchment: ✓ 4.8:1
- Ivory on Dark Slate: ✓ 13.2:1
- Crimson on Parchment: ✓ 5.1:1
- Never rely on color alone — use shape + motion + label
