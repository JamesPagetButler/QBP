"""
QBP Manim Scenes

Publication-quality mathematical animations using the Manim library.
All scenes use the QBP Futuristic Steampunk theme.

Usage:
    from viz.manim import QBPScene, QBPColors

    class MyScene(QBPScene):
        def construct(self):
            # Your animation code here
            pass

Rendering:
    manim -pql src/viz/manim/experiment_01.py SternGerlachScene
"""

from .base_scene import QBPScene, QBPColors, MANIM_THEME

__all__ = ["QBPScene", "QBPColors", "MANIM_THEME"]
