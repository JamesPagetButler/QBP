"""
QBP Video Export Utilities

Tools for exporting Manim animations in YouTube-optimized formats.

Usage:
    from viz.export import YOUTUBE_PRESETS, get_render_config

    config = get_render_config("standard")
    # Use config for manim rendering
"""

from .youtube import YOUTUBE_PRESETS, get_render_config, VideoTier

__all__ = ["YOUTUBE_PRESETS", "get_render_config", "VideoTier"]
