"""
QBP Design System: Futuristic Steampunk Theme

A visual language combining Victorian mechanical elegance
with the precision of modern physics.

Usage:
    from viz.theme import COLORS, PALETTE, apply_theme
"""

from dataclasses import dataclass
from typing import Tuple

# =============================================================================
# COLOR DEFINITIONS
# =============================================================================


@dataclass(frozen=True)
class Color:
    """Color with multiple format outputs."""

    name: str
    hex: str

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


# =============================================================================
# THE PALETTE: Futuristic Steampunk
# =============================================================================


class COLORS:
    """
    Primary palette inspired by brass instruments, gaslight,
    and the machinery of discovery.
    """

    # --- Primary: The Metals ---
    BRASS = Color("Brass", "#D4A574")  # Warm, polished brass
    COPPER = Color("Copper", "#B87333")  # Rich copper
    BRONZE = Color("Bronze", "#CD7F32")  # Deep bronze
    STEEL = Color("Steel", "#71797E")  # Cool iron-steel
    GOLD = Color("Gold", "#FFD700")  # Accent highlights

    # --- Secondary: The Elements ---
    TEAL = Color("Teal", "#2A9D8F")  # Deep ocean teal
    VERDIGRIS = Color("Verdigris", "#4A766E")  # Oxidized copper-green
    AMBER = Color("Amber", "#F4A261")  # Gaslight glow
    CRIMSON = Color("Crimson", "#9B2335")  # Warning, energy
    IVORY = Color("Ivory", "#FFFEF0")  # Aged paper, labels

    # --- Backgrounds ---
    PARCHMENT = Color("Parchment", "#F5E6D3")  # Light background
    DARK_SLATE = Color("Dark Slate", "#1A1A2E")  # Dark background
    MIDNIGHT = Color("Midnight", "#0D1B2A")  # Deep space black

    # --- Utility ---
    SHADOW = Color("Shadow", "#2C2C2C")  # Dark text, lines
    LIGHT_GRAY = Color("Light Gray", "#E8E4E0")  # Subtle grid lines


# Convenience groupings
class PALETTE:
    """Pre-composed color schemes for common uses."""

    # Axis colors (maintain XYZ = RGB convention with steampunk twist)
    AXIS_X = COLORS.CRIMSON  # X-axis: warm red
    AXIS_Y = COLORS.VERDIGRIS  # Y-axis: green-teal
    AXIS_Z = COLORS.TEAL  # Z-axis: deep blue-teal

    # For sequential data / rotations
    PRIMARY = COLORS.BRASS
    SECONDARY = COLORS.COPPER
    TERTIARY = COLORS.TEAL
    ACCENT = COLORS.AMBER

    # Backgrounds
    BG_LIGHT = COLORS.PARCHMENT
    BG_DARK = COLORS.DARK_SLATE

    # Text
    TEXT_ON_LIGHT = COLORS.SHADOW
    TEXT_ON_DARK = COLORS.IVORY


# =============================================================================
# THEME APPLICATION
# =============================================================================


def get_matplotlib_style() -> dict:
    """Return matplotlib rcParams for the steampunk theme."""
    return {
        "figure.facecolor": COLORS.PARCHMENT.hex,
        "axes.facecolor": COLORS.PARCHMENT.hex,
        "axes.edgecolor": COLORS.BRASS.hex,
        "axes.labelcolor": COLORS.SHADOW.hex,
        "axes.prop_cycle": f"cycler('color', ['{COLORS.BRASS.hex}', '{COLORS.TEAL.hex}', '{COLORS.COPPER.hex}', '{COLORS.AMBER.hex}', '{COLORS.VERDIGRIS.hex}'])",
        "xtick.color": COLORS.STEEL.hex,
        "ytick.color": COLORS.STEEL.hex,
        "grid.color": COLORS.LIGHT_GRAY.hex,
        "text.color": COLORS.SHADOW.hex,
        "legend.facecolor": COLORS.IVORY.hex,
        "legend.edgecolor": COLORS.BRASS.hex,
    }


def apply_matplotlib_theme():
    """Apply steampunk theme to matplotlib globally."""
    import matplotlib.pyplot as plt

    plt.rcParams.update(get_matplotlib_style())


def vpython_scene_config(dark_mode: bool = False) -> dict:
    """Return vpython canvas configuration."""
    if dark_mode:
        return {
            "background": COLORS.DARK_SLATE.vpython,
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
    print("\n" + "=" * 60)
    print("  QBP DESIGN SYSTEM: Futuristic Steampunk Palette")
    print("=" * 60 + "\n")

    all_colors = [
        (
            "METALS",
            [COLORS.BRASS, COLORS.COPPER, COLORS.BRONZE, COLORS.STEEL, COLORS.GOLD],
        ),
        (
            "ELEMENTS",
            [COLORS.TEAL, COLORS.VERDIGRIS, COLORS.AMBER, COLORS.CRIMSON, COLORS.IVORY],
        ),
        ("BACKGROUNDS", [COLORS.PARCHMENT, COLORS.DARK_SLATE, COLORS.MIDNIGHT]),
    ]

    for group_name, colors in all_colors:
        print(f"  {group_name}:")
        for c in colors:
            r, g, b = c.rgb
            # ANSI true color background
            print(f"    \033[48;2;{r};{g};{b}m    \033[0m  {c.name:12} {c.hex}")
        print()

    print("=" * 60 + "\n")


if __name__ == "__main__":
    show_palette()
