# QBP Design System

## Philosophy: Academic Steampunk → Solarpunk

> *"Brass orreries in a greenhouse"*

Our visual language bridges **Victorian mechanical precision** with **organic, nature-inspired optimism**. The aesthetic tells the story of QBP: moving from "broken theories" (industrial complexity) toward "working theories" (elegant natural truth).

**Academic Approach:** Colors are named after natural materials and historical pigments (Sage, Patina, Clay, Ochre, Sienna). Muted tones enhance rather than distract from rigorous mathematics and physics — approachable yet credible for academic audiences.

Think brass instruments illuminated by sunlight filtering through leaves. The machinery of discovery growing into understanding.

### The Narrative

| Element | Steampunk (Legacy) | Solarpunk (QBP) |
|---------|-------------------|-----------------|
| **Feel** | Industrial, mechanical | Organic, elegant |
| **Metals** | Brass, copper, bronze | Brass with sage/patina accents |
| **Accents** | Crimson, amber | Clay, sage, patina |
| **Background** | Dark Slate (industrial) | Verdant Night (green-tinted) |
| **Mood** | Nostalgic, mysterious | Hopeful, illuminated |
| **Naming** | Vivid colors | Natural materials & pigments |

---

## Accessibility Commitment

**WCAG 2.1 Compliance:** All text colors meet AA minimum contrast ratios.

| Level | Normal Text | Large Text (18pt+ or 14pt+ bold) |
|-------|-------------|----------------------------------|
| AA (required) | 4.5:1 | 3:1 |
| AAA (enhanced) | 7:1 | 4.5:1 |

Use the `TEXT` hierarchy from `viz/theme.py` to ensure compliance. Run `python src/viz/theme.py` to see the contrast report.

---

## Color Palette

### Legacy Metals — The Precision Instruments We Inherited

| Name | Hex | Use | Verdant Night | Parchment |
|------|-----|-----|---------------|-----------|
| **Brass** | `#D4A574` | Primary objects, key elements | 7.0:1 AAA | 1.8:1 -- |
| **Copper** | `#B87333` | Secondary objects, warmth | 4.3:1 AA | 3.1:1 -- |
| **Bronze** | `#CD7F32` | Accents, mechanisms | 5.2:1 AA | 2.4:1 -- |
| **Steel** | `#71797E` | Muted elements, grids | 3.5:1 -- | 3.6:1 -- |

### Solar Light — Illumination and Understanding

| Name | Hex | Use | Verdant Night | Parchment |
|------|-----|-----|---------------|-----------|
| **Gold** | `#FFD700` | Vibrant highlights, key emphasis | 11.2:1 AAA | 1.4:1 -- |
| **Ochre** | `#D4AA5A` | Earth pigment, warm academic tone | 7.1:1 AAA | 1.9:1 -- |
| **Amber** | `#F4A261` | Warnings, attention | 7.6:1 AAA | 1.7:1 -- |
| **Sienna** | `#C9956A` | Burnt earth, warm accent | 5.8:1 AA | 2.2:1 -- |

### Academic Greens — Natural Materials & Aged Surfaces

| Name | Hex | Use | Verdant Night | Parchment |
|------|-----|-----|---------------|-----------|
| **Sage** | `#3D8B6E` | Muted green, Y-axis base | 4.5:1 AA | 2.8:1 -- |
| **Sage Light** | `#5BA88A` | Y-axis on dark | 5.5:1 AA | 2.3:1 -- |
| **Patina** | `#5A9E94` | Z-axis on dark, aged copper-green | 5.0:1 AA | 2.5:1 -- |
| **Verdigris** | `#3D7A73` | Z-axis base, aged copper | 3.7:1 -- | 3.4:1 -- |

### Earth & Sky — Natural Pigments

| Name | Hex | Use | Verdant Night | Parchment |
|------|-----|-----|---------------|-----------|
| **Terracotta** | `#C4785A` | X-axis base, baked earth | 4.9:1 AA | 2.6:1 -- |
| **Clay** | `#D9956E` | X-axis on dark, warm earth | 6.3:1 AA | 2.0:1 -- |
| **Sky** | `#87CEEB` | Openness, possibility | 10.0:1 AAA | 1.5:1 -- |
| **Ivory** | `#FFFEF0` | Warm labels, accent text | 15.4:1 AAA | 1.1:1 -- |

### Academic Axis Colors (Accessible on Dark)

For axis elements on dark backgrounds, use these muted academic tones:

| Name | Hex | Use | Verdant Night |
|------|-----|-----|---------------|
| **Clay** | `#D9956E` | X-axis on dark | 6.3:1 AA |
| **Sage Light** | `#5BA88A` | Y-axis on dark | 5.5:1 AA |
| **Patina** | `#5A9E94` | Z-axis on dark | 5.0:1 AA |

### Legacy Colors (For Backward Compatibility)

| Name | Hex | Use | Verdant Night |
|------|-----|-----|---------------|
| **Jade** | `#00A86B` | Legacy Y-axis (vivid) | 5.3:1 AA |
| **Teal** | `#2A9D8F` | Legacy Z-axis (vivid) | 4.7:1 AA |
| **Coral** | `#E07B53` | Legacy X-axis (vivid) | 5.1:1 AA |
| **Crimson** | `#9B2335` | Legacy warnings | 2.0:1 -- |

### Backgrounds

| Name | Hex | RGB | Use |
|------|-----|-----|-----|
| **Parchment** | `#F5E6D3` | 245, 230, 211 | Light mode background |
| **Verdant Night** | `#0D2820` | 13, 40, 32 | Dark mode (solarpunk, primary) |
| **Dark Slate** | `#1A1A2E` | 26, 26, 46 | Dark mode (steampunk, legacy) |
| **Midnight** | `#0D1B2A` | 13, 27, 42 | Deep space black |

---

## Text Hierarchy

**Always use the `TEXT` class for text colors** to ensure accessibility compliance.

### Text on Dark Backgrounds (Verdant Night)

```python
from viz.theme import TEXT

# On VERDANT_NIGHT or DARK_SLATE backgrounds:
TEXT.DARK.PRIMARY    # #F5F5F5 Cloud   - Main body text (14.4:1)
TEXT.DARK.SECONDARY  # #B8B8B8 Silver  - Supporting text (7.9:1)
TEXT.DARK.TERTIARY   # #9A9A9A Ash     - Captions, hints (5.6:1)
TEXT.DARK.ACCENT     # #FFFEF0 Ivory   - Warm emphasis, titles (15.4:1)
TEXT.DARK.MUTED      # #71797E Steel   - Large text only (3.5:1)
```

| Level | Color | Hex | Ratio | WCAG | Use |
|-------|-------|-----|-------|------|-----|
| PRIMARY | Cloud | `#F5F5F5` | 14.4:1 | AAA | Main body text, formulas |
| SECONDARY | Silver | `#B8B8B8` | 7.9:1 | AAA | Supporting info, labels |
| TERTIARY | Ash | `#9A9A9A` | 5.6:1 | AA | Captions, hints, metadata |
| ACCENT | Ivory | `#FFFEF0` | 15.4:1 | AAA | Titles, warm emphasis |
| MUTED | Steel | `#71797E` | 3.5:1 | -- | Large text only (18pt+) |

### Text on Light Backgrounds (Parchment)

```python
from viz.theme import TEXT

# On PARCHMENT backgrounds:
TEXT.LIGHT.PRIMARY    # #2C2C2C Shadow   - Main body text (11.4:1)
TEXT.LIGHT.SECONDARY  # #3D3D3D Charcoal - Supporting text (8.9:1)
TEXT.LIGHT.TERTIARY   # #555566 Slate    - Captions, hints (6.0:1)
TEXT.LIGHT.ACCENT     # #B87333 Copper   - Warm emphasis (3.1:1, large only)
TEXT.LIGHT.MUTED      # #71797E Steel    - Large text only (3.6:1)
```

---

## Axis Convention

The axis colors tell QBP's story using natural materials:

```
X-axis: Terracotta (#C4785A)  — baked earth, warmth, energy
        Clay (#D9956E)        on dark — 6.3:1 AA
Y-axis: Sage (#3D8B6E)        — natural growth, correctness, life
        Sage Light (#5BA88A)  on dark — 5.5:1 AA
Z-axis: Verdigris (#3D7A73)   — aged copper, depth, measured truth
        Patina (#5A9E94)      on dark — 5.0:1 AA
```

Use `PALETTE.AXIS_X_DARK`, `PALETTE.AXIS_Y_DARK`, `PALETTE.AXIS_Z_DARK` for dark mode.

For legacy compatibility: `PALETTE.AXIS_X_LEGACY` (Crimson), `PALETTE.AXIS_Y_LEGACY` (Jade), `PALETTE.AXIS_Z_LEGACY` (Teal)

---

## Semantic Colors

| Purpose | Color | Use |
|---------|-------|-----|
| `PALETTE.SUCCESS` | Sage | Correct, passing, verified |
| `PALETTE.WARNING` | Amber | Caution, attention needed |
| `PALETTE.ERROR` | Terracotta | Problems, errors (warm earth, not harsh) |
| `PALETTE.ACCENT` | Ochre | Energy, muted academic highlights |
| `PALETTE.HIGHLIGHT` | Gold | Vibrant emphasis (use sparingly) |
| `PALETTE.PRIMARY` | Brass | Main objects |
| `PALETTE.SECONDARY` | Verdigris | Supporting elements (aged patina) |
| `PALETTE.TERTIARY` | Sage | Growth, correctness |

---

## Typography

| Context | Recommendation |
|---------|----------------|
| **Titles** | Bold, clean sans-serif, use `TEXT.*.ACCENT` |
| **Body** | Regular weight, use `TEXT.*.PRIMARY` |
| **Labels** | Use `TEXT.*.SECONDARY` |
| **Captions** | Use `TEXT.*.TERTIARY` |
| **Code** | Monospace, use `TEXT.*.PRIMARY` |
| **Disabled** | Use `TEXT.*.MUTED` (large text only) |

Keep text minimal. Let motion and color convey meaning.

---

## Usage in Code

### Python (vpython/matplotlib)

```python
from viz.theme import COLORS, PALETTE, TEXT, apply_matplotlib_theme, check_contrast

# Access colors (academic naming)
axis_color = COLORS.BRASS.vpython      # For vpython
line_color = COLORS.PATINA.hex         # For matplotlib
rgb_tuple = COLORS.SAGE.rgb_norm       # (0.24, 0.55, 0.43)

# Text colors (always use TEXT hierarchy!)
primary_text = TEXT.DARK.PRIMARY.hex   # For dark backgrounds
secondary_text = TEXT.DARK.SECONDARY.hex

# Academic axis colors for dark mode
x_axis = PALETTE.AXIS_X_DARK.vpython   # Clay
y_axis = PALETTE.AXIS_Y_DARK.vpython   # Sage Light
z_axis = PALETTE.AXIS_Z_DARK.vpython   # Patina

# Vibrant gold for key emphasis
highlight = COLORS.GOLD.vpython        # Pure vibrant gold

# Apply matplotlib theme (use legacy=True for steampunk dark)
apply_matplotlib_theme(dark_mode=True)           # Verdant Night (solarpunk)
apply_matplotlib_theme(dark_mode=True, legacy=True)  # Dark Slate (steampunk)

# Check accessibility
result = check_contrast(TEXT.DARK.PRIMARY, COLORS.VERDANT_NIGHT)
print(f"Contrast: {result['ratio']}:1, AA: {result['AA']}")
```

### HTML/CSS (VPython Captions)

**IMPORTANT:** VPython's caption area has a **light gray background** that cannot be overridden with CSS. Always use `TEXT.LIGHT` colors (dark text) for VPython captions, not `TEXT.DARK` colors.

```python
# CORRECT: Use TEXT.LIGHT for VPython captions (light background)
self.scene.append_to_caption(f"""
<div style='padding: 15px;'>
    <h3 style='color: {COLORS.COPPER.hex};'>Title</h3>
    <p style='color: {TEXT.LIGHT.PRIMARY.hex};'>Main text here</p>
    <span style='color: {TEXT.LIGHT.SECONDARY.hex};'>Supporting info</span>
</div>
""")

# WRONG: Don't use TEXT.DARK colors - they're invisible on light background!
# color: {TEXT.DARK.PRIMARY.hex}  <- #F5F5F5 white - INVISIBLE
# color: {COLORS.IVORY.hex}       <- #FFFEF0 cream - INVISIBLE
```

**VPython Caption Color Quick Reference:**

| Element | Color | Hex |
|---------|-------|-----|
| Headers | Copper | `#B87333` |
| Body text | Shadow (TEXT.LIGHT.PRIMARY) | `#2C2C2C` |
| Secondary | Charcoal (TEXT.LIGHT.SECONDARY) | `#3D3D3D` |
| Positive values | Sage | `#3D8B6E` |
| Negative values | Terracotta | `#C4785A` |
| Accents | Verdigris, Copper | `#3D7A73`, `#B87333` |

**Note:** The 3D canvas background (controlled by `scene.background`) CAN be dark. Only the caption HTML area is fixed to light gray.

### View Palette and Contrast Report

```bash
PYTHONPATH=src python src/viz/theme.py
```

---

## Design Principles

1. **Academic credibility** — Natural material names (Sage, Patina, Clay) enhance rigor
2. **Warmth with hope** — Brass warmth meets organic greens
3. **Motion over text** — Animate rather than annotate
4. **Contrast for clarity** — Use `TEXT` hierarchy for WCAG compliance
5. **Consistent axes** — XYZ = Terracotta/Sage/Verdigris (Clay/Sage Light/Patina on dark)
6. **Light as understanding** — Vibrant Gold for key emphasis, Ochre for subtle warmth
7. **Show your work** — Every visualization must display formal math
8. **Link to learn** — Every animation must link to documentation

---

## The Aesthetic Story

The QBP design system tells the story of moving from complexity to clarity:

- **Legacy metals** (Brass, Copper) represent the inherited machinery of physics — still beautiful, still precise, but part of the old paradigm
- **Academic greens** (Sage, Patina, Verdigris) represent nature's truth emerging — named after natural materials for scholarly credibility
- **Earth tones** (Clay, Terracotta, Ochre, Sienna) ground the palette in historical pigments — approachable yet rigorous
- **Solar light** (Gold, Amber) represents illumination and understanding — the "aha" moments when the math clicks (vibrant Gold kept for key emphasis)
- **Verdant Night** background vs **Dark Slate** — the shift from industrial (steampunk) to organic (solarpunk)

This is the visual language of a theory that works — academic enough to be taken seriously, hopeful enough to inspire.

---

## Axis Color Rationale

The axis color assignments are **aesthetic with structural justification**, not mathematical encodings. They are not arbitrary, but they are choices — different choices could work equally well.

| Axis | Color | Rationale |
|------|-------|-----------|
| **X** | Clay `#D9956E` | Warm, advancing tone — the x-axis extends "toward" the viewer in standard orientation. Clay (baked earth) conveys energy and immediacy. |
| **Y** | Sage Light `#5BA88A` | Green tones are perceptually sensitive — the eye distinguishes green variations most finely. The y-axis (vertical in most physics plots) benefits from this sensitivity. Sage (natural growth) conveys correctness. |
| **Z** | Patina `#5A9E94` | Cool, receding tone — the z-axis extends "into" depth. Patina (aged copper-green) conveys measured depth and truth revealed over time. |

**Why not encode physics?** We considered mapping colors to physical meaning (e.g., spin components), but axis colors must be stable across all visualizations — spin, position, momentum. Encoding physics into axis color would create contradictions across experiments. Natural-material naming keeps the associations stable and memorable without false precision.

---

## Visual Comparisons

The palette evolved from vibrant primary colors to muted academic tones. Two comparison documents show this transition:

- **[Palette Comparison](design-system-compare.html)** — Side-by-side view of old (vivid) vs. new (muted) palette applied to the same visualization elements. The muted palette enhances readability for academic audiences while maintaining visual warmth.
- **[Design Preview](design-system-preview.html)** — Full preview of the current design system applied to typical QBP visualization layouts, showing text hierarchy, axis colors, and semantic colors in context.

**Key differences from old palette:**
- Legacy Crimson/Jade/Teal replaced with Clay/Sage/Patina — warmer, less saturated
- Background shifted from Dark Slate (`#1A1A2E`) to Verdant Night (`#0D2820`) — green-tinted, organic
- Text hierarchy formalized with WCAG-compliant contrast ratios
- Color names changed from descriptive (Red, Green, Blue) to material (Clay, Sage, Patina)

---

## References

- [Solarpunk Aesthetics Wiki](https://aesthetics.fandom.com/wiki/Solarpunk)
- [WCAG 2.1 Contrast Guidelines](https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum.html)
- [WebAIM Contrast Checker](https://webaim.org/resources/contrastchecker/)
- [WebAIM Contrast and Color Accessibility](https://webaim.org/articles/contrast/)
