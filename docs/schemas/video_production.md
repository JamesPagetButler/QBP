# Video Production Guide

This document defines the video production standards for QBP experiment visualizations.

## Video Tiers

| Tier | Duration | Audience | Content |
|------|----------|----------|---------|
| **Short** | ≤1 min | Social media | Iconic moment, hook |
| **Standard** | ≤20 min | Science writers, enthusiasts | Experiment overview |
| **Deep Dive** | ≤2 hours | Advanced audience | Full technical details |

---

## Production Checklist

For each completed experiment, complete the following:

### Pre-Production

- [ ] Interactive visualization working (vpython)
- [ ] Key moments identified for animation
- [ ] Script outline written
- [ ] Manim scene structure planned

### Production

- [ ] Manim scene created with QBP theme
- [ ] All animations render without errors
- [ ] Color scheme matches design system
- [ ] Text is readable at target resolution

### Short Video (≤1 min)

- [ ] Iconic moment identified
- [ ] Hook within first 3 seconds
- [ ] Vertical format (1080x1920)
- [ ] 60 fps rendering
- [ ] No narration needed (visuals speak)
- [ ] End card with QBP branding

### Standard Video (≤20 min)

- [ ] Script written and reviewed
- [ ] Introduction hooks viewer
- [ ] Core concept explained simply
- [ ] Math shown with visual support
- [ ] Results clearly presented
- [ ] Conclusion with key insight
- [ ] Horizontal format (1920x1080)
- [ ] 60 fps rendering

### Deep Dive Video (≤2 hours)

- [ ] Detailed script with timestamps
- [ ] Chapter markers defined
- [ ] Full derivations shown
- [ ] Code walkthrough included
- [ ] Q&A or edge cases addressed
- [ ] Horizontal format (1920x1080)
- [ ] 30 fps acceptable for length

### Post-Production

- [ ] YouTube metadata prepared
- [ ] Title (≤60 characters)
- [ ] Description with timestamps
- [ ] Tags relevant to physics/math
- [ ] Thumbnail designed (using design system)
- [ ] Chapter markers set

---

## Visualization Documentation Standard

Every visualization must display the following information panel:

```
┌─────────────────────────────────────────────────────┐
│ EXPERIMENT: [Name]                                   │
│ STATUS: [Passed/In Progress/Failed]                  │
├─────────────────────────────────────────────────────┤
│ WHAT: [One sentence]                                 │
│ WHY:  [Physical significance]                        │
│ MATH: [Core equation]                                │
├─────────────────────────────────────────────────────┤
│ KEY INSIGHT: [What this proves about QBP model]      │
│                                                      │
│ [Interactive visualization area]                     │
│                                                      │
├─────────────────────────────────────────────────────┤
│ Results: [Link to data]                              │
│ Theory: [Link to docs]                               │
│ Tests: [Pass/Fail status]                            │
└─────────────────────────────────────────────────────┘
```

---

## Comparison Display

Each visualization must highlight:

| Element | Description | Display |
|---------|-------------|---------|
| **Model Prediction** | What QBP framework predicts | Equation + value |
| **Standard QM Prediction** | What conventional QM predicts | Equation + value |
| **Measurement** | What simulation/experiment shows | Value with error |
| **Agreement** | Visual indicator of match | Green/Yellow/Red |

### Agreement Indicators

- **Green**: Predictions match within error bounds
- **Yellow**: Partial agreement, minor discrepancies
- **Red**: Significant disagreement requiring investigation

---

## Technical Specifications

### Manim Rendering

```bash
# Short (vertical)
manim -qh --resolution 1080,1920 -o short.mp4 scene.py ShortScene

# Standard
manim -qh -o standard.mp4 scene.py StandardScene

# Deep Dive
manim -qm -o deep_dive.mp4 scene.py DeepDiveScene
```

### Color Palette

Use colors from `src/viz/theme.py`:

| Purpose | Color | Hex |
|---------|-------|-----|
| Primary | Brass | #D4A574 |
| Secondary | Copper | #B87333 |
| Accent | Amber | #F4A261 |
| Spin Up | Teal | #2A9D8F |
| Spin Down | Crimson | #9B2335 |
| Background | Dark Slate | #1A1A2E |
| Text | Ivory | #FFFEF0 |

### Font

- Use system default sans-serif
- Title: 48pt
- Body: 24pt
- Labels: 18pt

---

## Directory Structure

```
media/
├── shorts/
│   ├── exp_01_stern_gerlach.mp4
│   └── exp_02_angle_test.mp4
├── videos/
│   ├── exp_01_overview.mp4
│   ├── exp_01_deep_dive.mp4
│   └── ...
└── thumbnails/
    ├── exp_01.png
    └── ...
```

---

## Quality Gates

Before publication:

- [ ] Scientific accuracy verified by Red Team
- [ ] Visual quality meets minimum standards
- [ ] Audio quality acceptable (if narration present)
- [ ] All text readable at 720p
- [ ] Accessibility: color blind friendly contrasts
- [ ] Human approval obtained
