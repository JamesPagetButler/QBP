"""
YouTube Export Presets for QBP Visualizations

Defines rendering configurations optimized for different YouTube content tiers.

Usage:
    from viz.export import get_render_config, VideoTier

    # Get configuration for a standard video
    config = get_render_config(VideoTier.STANDARD)

    # Apply to manim
    from manim import config as manim_config
    manim_config.pixel_width = config["pixel_width"]
    manim_config.pixel_height = config["pixel_height"]
    manim_config.frame_rate = config["fps"]
"""

from dataclasses import dataclass
from enum import Enum
from typing import Dict, Any


class VideoTier(Enum):
    """Video production tier classification."""

    SHORT = "short"
    STANDARD = "standard"
    DEEP_DIVE = "deep_dive"


@dataclass(frozen=True)
class YouTubePreset:
    """Configuration for a YouTube video tier."""

    name: str
    pixel_width: int
    pixel_height: int
    fps: int
    duration_max: int  # seconds
    format: str
    chapters: bool = False
    description: str = ""

    @property
    def resolution(self) -> str:
        """Return resolution as WxH string."""
        return f"{self.pixel_width}x{self.pixel_height}"

    @property
    def aspect_ratio(self) -> str:
        """Return aspect ratio description."""
        if self.pixel_width > self.pixel_height:
            return "16:9 (landscape)"
        elif self.pixel_width < self.pixel_height:
            return "9:16 (vertical)"
        else:
            return "1:1 (square)"


# YouTube-optimized presets
YOUTUBE_PRESETS: Dict[str, YouTubePreset] = {
    "short": YouTubePreset(
        name="Short",
        pixel_width=1080,
        pixel_height=1920,
        fps=60,
        duration_max=60,
        format="mp4",
        description="YouTube Shorts / Social media vertical format",
    ),
    "standard": YouTubePreset(
        name="Standard",
        pixel_width=1920,
        pixel_height=1080,
        fps=60,
        duration_max=1200,  # 20 minutes
        format="mp4",
        description="Standard YouTube video for science writers and enthusiasts",
    ),
    "deep_dive": YouTubePreset(
        name="Deep Dive",
        pixel_width=1920,
        pixel_height=1080,
        fps=30,  # Lower for longer content
        duration_max=7200,  # 2 hours
        format="mp4",
        chapters=True,
        description="Extended technical walkthrough for advanced audience",
    ),
}


def get_render_config(tier: VideoTier | str) -> Dict[str, Any]:
    """
    Get Manim-compatible render configuration for a video tier.

    Args:
        tier: VideoTier enum or string name ("short", "standard", "deep_dive")

    Returns:
        Dictionary with render configuration

    Raises:
        ValueError: If tier is not recognized
    """
    if isinstance(tier, VideoTier):
        tier_name = tier.value
    else:
        tier_name = tier.lower()

    if tier_name not in YOUTUBE_PRESETS:
        valid = ", ".join(YOUTUBE_PRESETS.keys())
        raise ValueError(f"Unknown tier '{tier_name}'. Valid tiers: {valid}")

    preset = YOUTUBE_PRESETS[tier_name]

    return {
        "pixel_width": preset.pixel_width,
        "pixel_height": preset.pixel_height,
        "fps": preset.fps,
        "format": preset.format,
        "duration_max": preset.duration_max,
        "chapters": preset.chapters,
    }


def get_manim_quality_flag(tier: VideoTier | str) -> str:
    """
    Get the manim CLI quality flag for a tier.

    Args:
        tier: VideoTier enum or string name

    Returns:
        Manim quality flag string (e.g., "-qh" for high quality)
    """
    if isinstance(tier, VideoTier):
        tier_name = tier.value
    else:
        tier_name = tier.lower()

    # Map to manim quality flags
    # -ql: 480p15
    # -qm: 720p30
    # -qh: 1080p60
    # -qp: 1440p60 (production)
    # -qk: 4K60 (4K)

    if tier_name == "short":
        return "-qh"  # 1080p60 for shorts (vertical will be handled separately)
    elif tier_name == "standard":
        return "-qh"  # 1080p60
    elif tier_name == "deep_dive":
        return "-qm"  # 720p30 is fine for long content, or -qh if needed
    else:
        return "-qm"  # Default to medium


def print_presets():
    """Print all available presets in a formatted table."""
    print("\n" + "=" * 70)
    print("  QBP YouTube Export Presets")
    print("=" * 70 + "\n")

    for name, preset in YOUTUBE_PRESETS.items():
        print(f"  {preset.name.upper()}")
        print(f"    Resolution:    {preset.resolution} ({preset.aspect_ratio})")
        print(f"    Frame Rate:    {preset.fps} fps")
        print(f"    Max Duration:  {preset.duration_max // 60} minutes")
        print(f"    Format:        {preset.format}")
        print(f"    Chapters:      {'Yes' if preset.chapters else 'No'}")
        print(f"    Description:   {preset.description}")
        print()

    print("=" * 70 + "\n")


if __name__ == "__main__":
    print_presets()
