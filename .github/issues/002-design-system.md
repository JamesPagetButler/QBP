# Issue #002: Create Futuristic Steampunk Design System

**Labels:** `design`, `infrastructure`
**Status:** Open

## Summary

Establish a cohesive visual design system for QBP based on a **futuristic steampunk** aesthetic. This creates visual consistency across visualizations, documentation, and outputs.

## Design Direction

**Futuristic Steampunk** = Victorian-era mechanical elegance + advanced physics concepts

| Element | Inspiration |
|---------|-------------|
| Colors | Brass, copper, aged ivory, deep teal, amber glow |
| Typography | Clean labels with subtle serif accents |
| Motifs | Gears, orbital rings, orrery mechanics, brass instruments |
| Feel | Precision instruments measuring the fabric of reality |

## Deliverables

1. `docs/design-system.md` - Color codes, typography, usage guidelines
2. `src/viz/theme.py` - Python constants for vpython/matplotlib
3. Updated `quaternion_rotation.py` - Apply the theme
4. Sample palette image (optional)

## Acceptance Criteria

- [ ] Design system documented with hex/RGB color codes
- [ ] Theme module importable: `from viz.theme import COLORS`
- [ ] At least one visualization updated to use theme
- [ ] Accessibility maintained (sufficient contrast)

## Branch

`feature/design-system`
