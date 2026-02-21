# Visualization module for QBP
# Design System: Futuristic Steampunk
#
# NOTE: vpython-dependent symbols (visualize_rotation, SternGerlachDemo) are
# imported lazily to avoid pulling in vpython at module load time.  vpython
# requires pkg_resources which was removed from setuptools >=78.  Lazy imports
# let tests use the pure-math helpers without vpython installed.

from .theme import COLORS, PALETTE, apply_matplotlib_theme, show_palette
from .quaternion_rotation import rotate_vector_by_quaternion


def __getattr__(name):
    if name == "visualize_rotation":
        from .quaternion_rotation import visualize_rotation

        return visualize_rotation
    if name == "SternGerlachDemo":
        from .stern_gerlach_demo import SternGerlachDemo

        return SternGerlachDemo
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = [
    "COLORS",
    "PALETTE",
    "apply_matplotlib_theme",
    "show_palette",
    "visualize_rotation",
    "rotate_vector_by_quaternion",
    "SternGerlachDemo",
]
