# Visualization module for QBP
# Design System: Futuristic Steampunk

from .theme import COLORS, PALETTE, apply_matplotlib_theme, show_palette
from .quaternion_rotation import visualize_rotation, rotate_vector_by_quaternion
from .stern_gerlach_demo import SternGerlachDemo

__all__ = [
    "COLORS",
    "PALETTE",
    "apply_matplotlib_theme",
    "show_palette",
    "visualize_rotation",
    "rotate_vector_by_quaternion",
    "SternGerlachDemo",
]
