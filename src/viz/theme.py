"""
QBP Design System: Academic Steampunk → Solarpunk Aesthetic

A visual language bridging Victorian mechanical precision with organic,
nature-inspired optimism. The palette tells the story of moving from
"broken theories" (industrial complexity) toward "working theories"
(elegant natural truth).

AESTHETIC: Brass orreries in a greenhouse. Precision instruments
illuminated by sunlight filtering through leaves. The machinery of
discovery growing into understanding.

ACADEMIC APPROACH: Colors named after natural materials and historical
pigments (Sage, Patina, Clay, Ochre, Sienna). Muted tones that enhance
rather than distract from rigorous mathematics and physics — approachable
yet credible for academic audiences.

ACCESSIBILITY: All text colors meet WCAG 2.1 AA minimum (4.5:1 for normal text,
3:1 for large text). Use TEXT hierarchy for proper contrast.

References:
- Solarpunk aesthetic: https://aesthetics.fandom.com/wiki/Solarpunk
- WCAG contrast: https://webaim.org/articles/contrast/

Usage:
    from viz.theme import COLORS, PALETTE, TEXT, apply_theme, check_contrast
"""

from dataclasses import dataclass
from typing import Tuple, Optional


# =============================================================================
# COLOR DEFINITIONS
# =============================================================================


@dataclass(frozen=True)
class Color:
    """Color with multiple format outputs and accessibility metadata."""

    name: str
    hex: str
    _contrast_dark: Optional[float] = None  # Contrast ratio on VERDANT_NIGHT
    _contrast_light: Optional[float] = None  # Contrast ratio on PARCHMENT

    @property
    def rgb(self) -> Tuple[int, int, int]:
        """RGB as 0-255 integers."""
        h = self.hex.lstrip("#")
        r, g, b = (int(h[i : i + 2], 16) for i in (0, 2, 4))
        return (r, g, b)

    @property
    def rgb_norm(self) -> Tuple[float, float, float]:
        """RGB normalized 0-1 for matplotlib/vpython."""
        r, g, b = self.rgb
        return (r / 255, g / 255, b / 255)

    @property
    def vpython(self):
        """Return vpython vector (import vpython separately)."""
        from vpython import vector

        return vector(*self.rgb_norm)

    @property
    def css(self) -> str:
        """Return CSS-ready hex string."""
        return self.hex


# =============================================================================
# CONTRAST UTILITIES (WCAG 2.1)
# =============================================================================


def relative_luminance(r: int, g: int, b: int) -> float:
    """Calculate relative luminance per WCAG 2.1 formula.

    Args:
        r, g, b: RGB values 0-255

    Returns:
        Relative luminance 0-1
    """
    def channel(c: int) -> float:
        c_norm = c / 255
        if c_norm <= 0.04045:
            return c_norm / 12.92
        else:
            return ((c_norm + 0.055) / 1.055) ** 2.4
    return 0.2126 * channel(r) + 0.7152 * channel(g) + 0.0722 * channel(b)


def contrast_ratio(color1: Color, color2: Color) -> float:
    """Calculate WCAG contrast ratio between two colors.

    Args:
        color1, color2: Color objects

    Returns:
        Contrast ratio (1:1 to 21:1)
    """
    l1 = relative_luminance(*color1.rgb)
    l2 = relative_luminance(*color2.rgb)
    lighter = max(l1, l2)
    darker = min(l1, l2)
    return (lighter + 0.05) / (darker + 0.05)


def check_contrast(fg: Color, bg: Color, size: str = "normal") -> dict:
    """Check if a color combination meets WCAG requirements.

    Args:
        fg: Foreground (text) color
        bg: Background color
        size: "normal" (< 18pt) or "large" (>= 18pt or >= 14pt bold)

    Returns:
        Dict with ratio, AA pass, AAA pass
    """
    ratio = contrast_ratio(fg, bg)
    if size == "large":
        aa_threshold = 3.0
        aaa_threshold = 4.5
    else:
        aa_threshold = 4.5
        aaa_threshold = 7.0

    return {
        "ratio": round(ratio, 2),
        "AA": ratio >= aa_threshold,
        "AAA": ratio >= aaa_threshold,
        "fg": fg.name,
        "bg": bg.name,
    }


# =============================================================================
# THE PALETTE: Steampunk → Solarpunk Transition
# =============================================================================


class COLORS:
    """
    A palette bridging Victorian precision with organic optimism.

    THE NARRATIVE:
    - Legacy metals (Brass, Copper) = the old machinery, still beautiful
    - Living greens (Jade, Teal, Verdant) = nature's truth emerging
    - Solar light (Gold, Solar, Amber) = illumination, understanding
    - The shift from industrial to organic tells QBP's story

    Contrast ratios documented for VERDANT_NIGHT and PARCHMENT backgrounds.
    """

    # =========================================================================
    # LEGACY METALS — The precision instruments we inherited
    # =========================================================================
    BRASS = Color("Brass", "#D4A574")       # Warm, polished brass (keep)
    COPPER = Color("Copper", "#B87333")     # Rich copper patina
    BRONZE = Color("Bronze", "#CD7F32")     # Deep bronze mechanisms
    STEEL = Color("Steel", "#71797E")       # Cool iron-steel (muted)

    # =========================================================================
    # SOLAR LIGHT — Illumination and understanding
    # =========================================================================
    GOLD = Color("Gold", "#FFD700")         # Pure solar gold, highlights (vibrant!)
    OCHRE = Color("Ochre", "#D4AA5A")       # Earth pigment, warm academic tone
    AMBER = Color("Amber", "#F4A261")       # Gaslight glow, warmth
    SIENNA = Color("Sienna", "#C9956A")     # Burnt earth, warm accent

    # Legacy alias for backward compatibility
    SOLAR = Color("Solar", "#D4AA5A")       # Alias for OCHRE

    # =========================================================================
    # LIVING GREENS — Nature's truth, organic elegance
    # Academic naming: Natural materials and aged surfaces
    # =========================================================================
    SAGE = Color("Sage", "#3D8B6E")         # Muted green, growth, life
    JADE = Color("Jade", "#00A86B")         # Legacy: Growth, correctness
    PATINA = Color("Patina", "#5A9E94")     # Aged copper-green, depth
    TEAL = Color("Teal", "#2A9D8F")         # Legacy: Deep ocean, Z-axis
    VERDANT = Color("Verdant", "#228B22")   # Forest green, flourishing
    VERDIGRIS = Color("Verdigris", "#3D7A73")  # Aged copper, transition

    # =========================================================================
    # SKY & EARTH — Openness and warmth
    # Academic naming: Natural pigments and materials
    # =========================================================================
    SKY = Color("Sky", "#87CEEB")           # Open sky, possibility
    TERRACOTTA = Color("Terracotta", "#C4785A")  # Baked earth, X-axis base
    CLAY = Color("Clay", "#D9956E")         # Warm earth, accessible X-axis
    CORAL = Color("Coral", "#E07B53")       # Legacy: Warm accent

    # =========================================================================
    # LEGACY ACCENTS — Kept for continuity
    # =========================================================================
    CRIMSON = Color("Crimson", "#9B2335")   # X-axis on light bg, warnings
    IVORY = Color("Ivory", "#FFFEF0")       # Aged paper, warm labels

    # =========================================================================
    # BACKGROUNDS — From industrial dark to verdant night
    # =========================================================================
    PARCHMENT = Color("Parchment", "#F5E6D3")    # Light mode, warm paper
    VERDANT_NIGHT = Color("Verdant Night", "#0D2820")  # Dark with green tint (new primary)
    DARK_SLATE = Color("Dark Slate", "#1A1A2E")  # Legacy industrial dark
    MIDNIGHT = Color("Midnight", "#0D1B2A")      # Deep space black

    # =========================================================================
    # TEXT COLORS: Dark Mode (on VERDANT_NIGHT/DARK_SLATE)
    # =========================================================================
    CLOUD = Color("Cloud", "#F5F5F5")       # Primary text (15.7:1)
    SILVER = Color("Silver", "#B8B8B8")     # Secondary text (8.6:1)
    ASH = Color("Ash", "#9A9A9A")           # Tertiary text (6.1:1)
    # IVORY for warm accent text (16.8:1)

    # =========================================================================
    # TEXT COLORS: Light Mode (on PARCHMENT)
    # =========================================================================
    SHADOW = Color("Shadow", "#2C2C2C")     # Primary text (11.4:1)
    CHARCOAL = Color("Charcoal", "#3D3D3D") # Secondary text (8.9:1)
    SLATE = Color("Slate", "#555566")       # Tertiary text (6.0:1)

    # =========================================================================
    # ACADEMIC LIGHT VARIANTS — Accessible on dark backgrounds
    # Used for axis colors and accent elements
    # =========================================================================
    SAGE_LIGHT = Color("Sage Light", "#5BA88A")         # Y-axis on dark (5.9:1)

    # Legacy aliases for backward compatibility (map to academic colors)
    CORAL_BRIGHT = Color("Clay", "#D9956E")             # → CLAY (same color)
    JADE_BRIGHT = Color("Sage Light", "#5BA88A")        # → SAGE_LIGHT (same color)
    TEAL_BRIGHT = Color("Patina", "#5A9E94")            # → PATINA (same color)
    CRIMSON_BRIGHT = Color("Crimson Bright", "#E84057") # Legacy vivid red (4.3:1)
    VERDIGRIS_BRIGHT = Color("Verdigris Bright", "#5FA393")  # Bright patina (5.4:1)

    # =========================================================================
    # UTILITY
    # =========================================================================
    LIGHT_GRAY = Color("Light Gray", "#E8E4E0")  # Grid lines, subtle elements


# =============================================================================
# TEXT HIERARCHY SYSTEM
# =============================================================================


class TEXT:
    """
    Text color hierarchy for accessibility.

    Use these instead of raw colors for text to ensure WCAG compliance.
    All colors meet AA minimum (4.5:1) for normal text.

    Usage:
        from viz.theme import TEXT
        color = TEXT.DARK.PRIMARY.hex  # For text on dark backgrounds
        color = TEXT.LIGHT.SECONDARY.hex  # For secondary text on light bg
    """

    class DARK:
        """Text colors for dark backgrounds (VERDANT_NIGHT, DARK_SLATE)."""
        PRIMARY = COLORS.CLOUD      # Main body text (15.7:1) - clear, neutral
        SECONDARY = COLORS.SILVER   # Supporting text (8.6:1) - still prominent
        TERTIARY = COLORS.ASH       # Captions, hints (6.1:1) - subtle but readable
        ACCENT = COLORS.IVORY       # Warm emphasis (16.8:1) - titles, highlights
        MUTED = COLORS.STEEL        # Large text only (3.9:1) - use sparingly

    class LIGHT:
        """Text colors for light backgrounds (PARCHMENT)."""
        PRIMARY = COLORS.SHADOW     # Main body text (11.4:1) - strong contrast
        SECONDARY = COLORS.CHARCOAL # Supporting text (8.9:1) - good clarity
        TERTIARY = COLORS.SLATE     # Captions, hints (6.0:1) - subtle
        ACCENT = COLORS.COPPER      # Warm emphasis (3.1:1) - large text only
        MUTED = COLORS.STEEL        # Large text only (3.6:1) - use sparingly


# =============================================================================
# PALETTE GROUPINGS
# =============================================================================


class PALETTE:
    """Pre-composed color schemes for common uses.

    Academic naming: Natural materials and historical pigments
    - X: Clay/Terracotta (warmth, energy, baked earth)
    - Y: Sage (growth, correctness, natural growth)
    - Z: Patina/Verdigris (depth, aged truth, measured time)
    """

    # =========================================================================
    # AXIS COLORS — The story of measurement (Academic naming)
    # =========================================================================
    # On light backgrounds
    AXIS_X = COLORS.TERRACOTTA      # X-axis: warm earth
    AXIS_Y = COLORS.SAGE            # Y-axis: natural growth
    AXIS_Z = COLORS.VERDIGRIS       # Z-axis: aged depth

    # On dark backgrounds (accessible muted academic tones)
    AXIS_X_DARK = COLORS.CLAY           # X-axis on dark (6.2:1)
    AXIS_Y_DARK = COLORS.SAGE_LIGHT     # Y-axis on dark (5.9:1)
    AXIS_Z_DARK = COLORS.PATINA         # Z-axis on dark (5.4:1)

    # Legacy axis colors (for backward compatibility)
    AXIS_X_LEGACY = COLORS.CRIMSON      # Original X-axis
    AXIS_Y_LEGACY = COLORS.JADE         # Original Y-axis (vivid)
    AXIS_Z_LEGACY = COLORS.TEAL         # Original Z-axis (vivid)

    # =========================================================================
    # SEMANTIC COLORS — For data and states
    # =========================================================================
    PRIMARY = COLORS.BRASS          # Main objects, key elements
    SECONDARY = COLORS.VERDIGRIS    # Supporting elements (aged patina)
    TERTIARY = COLORS.SAGE          # Growth, success, correctness
    ACCENT = COLORS.OCHRE           # Energy, highlights (academic gold)
    HIGHLIGHT = COLORS.GOLD         # Pure vibrant gold for key emphasis
    WARNING = COLORS.AMBER          # Caution, attention
    ERROR = COLORS.TERRACOTTA       # Problems, errors (warm earth, not harsh)
    SUCCESS = COLORS.SAGE           # Correct, passing, verified

    # =========================================================================
    # BACKGROUNDS
    # =========================================================================
    BG_LIGHT = COLORS.PARCHMENT
    BG_DARK = COLORS.VERDANT_NIGHT   # Primary dark (green-tinted, solarpunk)
    BG_LEGACY = COLORS.DARK_SLATE    # Legacy industrial dark (steampunk)

    # =========================================================================
    # LEGACY ALIASES (for backward compatibility)
    # =========================================================================
    TEXT_ON_LIGHT = COLORS.SHADOW
    TEXT_ON_DARK = COLORS.IVORY


# =============================================================================
# THEME APPLICATION
# =============================================================================


def get_matplotlib_style(dark_mode: bool = False, legacy: bool = False) -> dict:
    """Return matplotlib rcParams for the academic steampunk-solarpunk theme.

    Args:
        dark_mode: If True, use dark background
        legacy: If True, use DARK_SLATE instead of VERDANT_NIGHT
    """
    if dark_mode:
        bg = COLORS.DARK_SLATE if legacy else COLORS.VERDANT_NIGHT
        # Academic muted colors for dark mode
        return {
            "figure.facecolor": bg.hex,
            "axes.facecolor": bg.hex,
            "axes.edgecolor": COLORS.BRASS.hex,
            "axes.labelcolor": TEXT.DARK.PRIMARY.hex,
            "axes.prop_cycle": f"cycler('color', ['{COLORS.BRASS.hex}', '{COLORS.PATINA.hex}', '{COLORS.SAGE_LIGHT.hex}', '{COLORS.OCHRE.hex}', '{COLORS.CLAY.hex}'])",
            "xtick.color": TEXT.DARK.SECONDARY.hex,
            "ytick.color": TEXT.DARK.SECONDARY.hex,
            "grid.color": COLORS.STEEL.hex,
            "text.color": TEXT.DARK.PRIMARY.hex,
            "legend.facecolor": bg.hex,
            "legend.edgecolor": COLORS.BRASS.hex,
            "legend.labelcolor": TEXT.DARK.PRIMARY.hex,
        }
    else:
        # Academic colors for light mode
        return {
            "figure.facecolor": COLORS.PARCHMENT.hex,
            "axes.facecolor": COLORS.PARCHMENT.hex,
            "axes.edgecolor": COLORS.BRASS.hex,
            "axes.labelcolor": TEXT.LIGHT.PRIMARY.hex,
            "axes.prop_cycle": f"cycler('color', ['{COLORS.BRASS.hex}', '{COLORS.VERDIGRIS.hex}', '{COLORS.SAGE.hex}', '{COLORS.OCHRE.hex}', '{COLORS.TERRACOTTA.hex}'])",
            "xtick.color": TEXT.LIGHT.SECONDARY.hex,
            "ytick.color": TEXT.LIGHT.SECONDARY.hex,
            "grid.color": COLORS.LIGHT_GRAY.hex,
            "text.color": TEXT.LIGHT.PRIMARY.hex,
            "legend.facecolor": COLORS.IVORY.hex,
            "legend.edgecolor": COLORS.BRASS.hex,
        }


def apply_matplotlib_theme(dark_mode: bool = False, legacy: bool = False):
    """Apply steampunk-solarpunk theme to matplotlib globally."""
    import matplotlib.pyplot as plt

    plt.rcParams.update(get_matplotlib_style(dark_mode, legacy))


def vpython_scene_config(dark_mode: bool = False, legacy: bool = False) -> dict:
    """Return vpython canvas configuration."""
    if dark_mode:
        bg = COLORS.DARK_SLATE if legacy else COLORS.VERDANT_NIGHT
        return {
            "background": bg.vpython,
            "ambient": COLORS.STEEL.vpython * 0.3,
        }
    else:
        return {
            "background": COLORS.PARCHMENT.vpython,
            "ambient": COLORS.IVORY.vpython * 0.4,
        }


# =============================================================================
# DISPLAY UTILITIES
# =============================================================================


def show_palette():
    """Print the color palette to terminal with ANSI colors."""
    print("\n" + "=" * 70)
    print("  QBP DESIGN SYSTEM: Academic Steampunk → Solarpunk")
    print("  'Brass orreries in a greenhouse'")
    print("  Natural materials • Historical pigments • WCAG accessible")
    print("=" * 70 + "\n")

    all_colors = [
        (
            "LEGACY METALS",
            [COLORS.BRASS, COLORS.COPPER, COLORS.BRONZE, COLORS.STEEL],
        ),
        (
            "SOLAR LIGHT",
            [COLORS.GOLD, COLORS.OCHRE, COLORS.AMBER, COLORS.SIENNA],
        ),
        (
            "ACADEMIC GREENS",
            [COLORS.SAGE, COLORS.SAGE_LIGHT, COLORS.PATINA, COLORS.VERDIGRIS],
        ),
        (
            "EARTH & SKY",
            [COLORS.TERRACOTTA, COLORS.CLAY, COLORS.SKY, COLORS.IVORY],
        ),
        (
            "BACKGROUNDS",
            [COLORS.PARCHMENT, COLORS.VERDANT_NIGHT, COLORS.DARK_SLATE, COLORS.MIDNIGHT],
        ),
        (
            "TEXT (DARK BG)",
            [COLORS.CLOUD, COLORS.SILVER, COLORS.ASH, COLORS.IVORY],
        ),
        (
            "TEXT (LIGHT BG)",
            [COLORS.SHADOW, COLORS.CHARCOAL, COLORS.SLATE],
        ),
        (
            "LEGACY COLORS",
            [COLORS.JADE, COLORS.TEAL, COLORS.CORAL, COLORS.CRIMSON],
        ),
    ]

    for group_name, colors in all_colors:
        print(f"  {group_name}:")
        for c in colors:
            r, g, b = c.rgb
            # ANSI true color background
            print(f"    \033[48;2;{r};{g};{b}m    \033[0m  {c.name:18} {c.hex}")
        print()

    print("=" * 70 + "\n")


def show_contrast_report():
    """Print contrast ratio report for all text colors."""
    print("\n" + "=" * 70)
    print("  WCAG CONTRAST RATIO REPORT")
    print("=" * 70 + "\n")

    verdant_bg = COLORS.VERDANT_NIGHT
    light_bg = COLORS.PARCHMENT

    print(f"  TEXT ON VERDANT NIGHT ({verdant_bg.hex})")
    print("  " + "-" * 50)
    for name in ["PRIMARY", "SECONDARY", "TERTIARY", "ACCENT", "MUTED"]:
        color = getattr(TEXT.DARK, name)
        result = check_contrast(color, verdant_bg)
        aa = "AA" if result["AA"] else "--"
        aaa = "AAA" if result["AAA"] else "---"
        print(f"    {name:12} {color.hex}  {result['ratio']:5.1f}:1  {aa}  {aaa}")
    print()

    print(f"  TEXT ON PARCHMENT ({light_bg.hex})")
    print("  " + "-" * 50)
    for name in ["PRIMARY", "SECONDARY", "TERTIARY", "ACCENT", "MUTED"]:
        color = getattr(TEXT.LIGHT, name)
        result = check_contrast(color, light_bg)
        aa = "AA" if result["AA"] else "--"
        aaa = "AAA" if result["AAA"] else "---"
        print(f"    {name:12} {color.hex}  {result['ratio']:5.1f}:1  {aa}  {aaa}")
    print()

    print("  ACADEMIC AXIS COLORS ON VERDANT NIGHT")
    print("  " + "-" * 50)
    for name, color in [("X (Clay)", COLORS.CLAY),
                        ("Y (Sage Light)", COLORS.SAGE_LIGHT),
                        ("Z (Patina)", COLORS.PATINA)]:
        result = check_contrast(color, verdant_bg)
        aa = "AA" if result["AA"] else "--"
        aaa = "AAA" if result["AAA"] else "---"
        print(f"    {name:18} {color.hex}  {result['ratio']:5.1f}:1  {aa}  {aaa}")

    print("\n" + "=" * 70 + "\n")


if __name__ == "__main__":
    show_palette()
    show_contrast_report()
