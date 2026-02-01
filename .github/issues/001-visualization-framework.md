# Issue #001: Establish Visualization Framework

**Labels:** `infrastructure`, `accessibility`
**Status:** Open

## Summary

Select and configure a visualization stack for quaternion physics animations. Must support accessibility (dyslexia-friendly: motion over dense text, clear labels, high contrast).

## Requirements

| Requirement | Priority |
|-------------|----------|
| 3D quaternion rotation visualization | High |
| Animation export (GIF/MP4/HTML) | High |
| Browser-viewable output | Medium |
| Reproducible from code (no GUI) | High |
| Clear, high-contrast labeling | High |

## Candidates

| Framework | Use Case | Install |
|-----------|----------|---------|
| **manim** | Publication-quality math animations | `pip install manim` |
| **vpython** | Interactive 3D physics | `pip install vpython` |
| **plotly** | Interactive browser plots | `pip install plotly` |

**Recommendation:** `manim` for paper figures + `vpython` for exploration.

## Acceptance Criteria

- [ ] Framework(s) documented in `docs/visualization.md`
- [ ] Dependencies added to `requirements.txt`
- [ ] Minimal example: `src/viz/quaternion_rotation.py` animates a unit quaternion
- [ ] Output viewable in browser

## Structure

```
src/
  viz/
    __init__.py
    quaternion_rotation.py   # minimal working example
docs/
  visualization.md           # usage guide
```

## Branch

`feature/visualization-framework`
