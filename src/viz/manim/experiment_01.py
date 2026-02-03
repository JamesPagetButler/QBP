"""
Stern-Gerlach Experiment Visualization

Manim scene demonstrating the Stern-Gerlach experiment using the QBP
quaternionic framework.

Usage:
    # Preview (low quality)
    manim -pql src/viz/manim/experiment_01.py SternGerlachScene

    # High quality render
    manim -qh src/viz/manim/experiment_01.py SternGerlachScene

    # YouTube Short (vertical)
    manim -qh --resolution 1080,1920 src/viz/manim/experiment_01.py SternGerlachShort
"""

from manim import (
    Scene,
    VGroup,
    Arrow,
    Circle,
    Rectangle,
    Line,
    Dot,
    Text,
    MathTex,
    Tex,
    UP,
    DOWN,
    LEFT,
    RIGHT,
    ORIGIN,
    Write,
    Create,
    FadeIn,
    FadeOut,
    Transform,
    MoveToTarget,
    GrowArrow,
    Wait,
    AnimationGroup,
    Succession,
    config,
    TracedPath,
    ValueTracker,
    always_redraw,
    rate_functions,
    Polygon,
    Arc,
)
import numpy as np

from .base_scene import QBPScene, QBPColors


class SternGerlachScene(QBPScene):
    """
    Standard overview of the Stern-Gerlach experiment.

    Demonstrates:
    - Particle beam entering magnetic field
    - Spin quantization into up/down outcomes
    - 50/50 split for X-aligned initial state measured on Z
    """

    def construct(self):
        # Title
        title = self.create_title(
            "Stern-Gerlach Experiment",
            "Quaternionic Spin Quantization",
        )
        title.to_edge(UP, buff=0.5)
        self.play(Write(title))
        self.wait(0.5)

        # Create apparatus
        apparatus = self.create_apparatus()
        apparatus.scale(0.8)
        apparatus.next_to(title, DOWN, buff=0.8)
        self.play(Create(apparatus))
        self.wait(0.5)

        # Show initial state equation
        initial_eq = MathTex(
            r"\psi = (0, 1, 0, 0)",
            r"\quad \text{(X-aligned)}",
            color=QBPColors.IVORY,
        )
        initial_eq.scale(0.7)
        initial_eq.next_to(apparatus, DOWN, buff=0.5)
        self.play(Write(initial_eq))
        self.wait(0.5)

        # Show observable
        obs_eq = MathTex(
            r"O = \hat{k}",
            r"\quad \text{(measure Z)}",
            color=QBPColors.IVORY,
        )
        obs_eq.scale(0.7)
        obs_eq.next_to(initial_eq, DOWN, buff=0.3)
        self.play(Write(obs_eq))
        self.wait(0.5)

        # Animate particles
        self.animate_particles(apparatus)
        self.wait(0.5)

        # Show results
        results = self.create_results_panel()
        results.scale(0.7)
        results.to_edge(DOWN, buff=0.5)
        self.play(FadeIn(results))
        self.wait(1)

        # Key insight
        insight = Text(
            "Key: Continuous input → Discrete output",
            color=QBPColors.GOLD,
            font_size=28,
        )
        insight.next_to(results, UP, buff=0.3)
        self.play(Write(insight))
        self.wait(2)

    def create_apparatus(self) -> VGroup:
        """Create the Stern-Gerlach apparatus visualization."""
        # Source
        source = Circle(radius=0.3, color=QBPColors.BRASS, fill_opacity=0.3)
        source_label = Text("Source", color=QBPColors.BRASS, font_size=16)
        source_label.next_to(source, DOWN, buff=0.1)
        source_group = VGroup(source, source_label)

        # Collimator
        collimator = Rectangle(
            width=0.2,
            height=0.8,
            color=QBPColors.STEEL,
            fill_opacity=0.5,
        )
        collimator.next_to(source, RIGHT, buff=0.5)

        # Magnet (wedge shape)
        north_pole = Polygon(
            [-0.3, 0.6, 0],
            [0.3, 0.6, 0],
            [0.5, 0.2, 0],
            [-0.5, 0.2, 0],
            color=QBPColors.CRIMSON,
            fill_opacity=0.4,
        )
        north_label = Text("N", color=QBPColors.CRIMSON, font_size=20)
        north_label.move_to(north_pole.get_center())

        south_pole = Polygon(
            [-0.5, -0.2, 0],
            [0.5, -0.2, 0],
            [0.3, -0.6, 0],
            [-0.3, -0.6, 0],
            color=QBPColors.TEAL,
            fill_opacity=0.4,
        )
        south_label = Text("S", color=QBPColors.TEAL, font_size=20)
        south_label.move_to(south_pole.get_center())

        magnet = VGroup(north_pole, north_label, south_pole, south_label)
        magnet.next_to(collimator, RIGHT, buff=0.5)

        # Magnetic field arrow
        b_field = Arrow(
            start=DOWN * 0.3,
            end=UP * 0.3,
            color=QBPColors.AMBER,
            stroke_width=3,
        )
        b_field.next_to(magnet, RIGHT, buff=0.1)
        b_label = MathTex(r"\vec{B}", color=QBPColors.AMBER, font_size=20)
        b_label.next_to(b_field, RIGHT, buff=0.1)

        # Detectors
        detector_up = Rectangle(
            width=0.4,
            height=0.3,
            color=QBPColors.TEAL,
            fill_opacity=0.6,
        )
        detector_up.next_to(magnet, RIGHT, buff=1.5)
        detector_up.shift(UP * 0.8)
        up_label = Text("+1 (Up)", color=QBPColors.TEAL, font_size=14)
        up_label.next_to(detector_up, RIGHT, buff=0.1)

        detector_down = Rectangle(
            width=0.4,
            height=0.3,
            color=QBPColors.CRIMSON,
            fill_opacity=0.6,
        )
        detector_down.next_to(magnet, RIGHT, buff=1.5)
        detector_down.shift(DOWN * 0.8)
        down_label = Text("-1 (Down)", color=QBPColors.CRIMSON, font_size=14)
        down_label.next_to(detector_down, RIGHT, buff=0.1)

        # Beam path (will be animated)
        beam_in = Line(
            start=source.get_right(),
            end=collimator.get_left(),
            color=QBPColors.AMBER,
            stroke_width=2,
        )

        beam_through = Line(
            start=collimator.get_right(),
            end=magnet.get_left() + RIGHT * 0.3,
            color=QBPColors.AMBER,
            stroke_width=2,
        )

        apparatus = VGroup(
            source_group,
            collimator,
            magnet,
            b_field,
            b_label,
            detector_up,
            up_label,
            detector_down,
            down_label,
            beam_in,
            beam_through,
        )

        return apparatus

    def animate_particles(self, apparatus: VGroup):
        """Animate particles splitting in the magnetic field."""
        # Get positions from apparatus
        magnet_center = apparatus[2].get_center()
        detector_up = apparatus[5]
        detector_down = apparatus[7]

        # Create several particles
        particles = []
        for i in range(6):
            particle = Dot(
                point=apparatus[0][0].get_right() + RIGHT * 0.1,
                radius=0.08,
                color=QBPColors.AMBER,
            )
            particles.append(particle)

        # Animate particles entering
        self.play(*[FadeIn(p) for p in particles[:3]], run_time=0.3)

        # Move to magnet center
        self.play(
            *[p.animate.move_to(magnet_center) for p in particles[:3]],
            run_time=0.5,
        )

        # Split: some go up, some go down (simulating 50/50)
        self.play(
            particles[0].animate.move_to(detector_up.get_left()),
            particles[1].animate.move_to(detector_down.get_left()),
            particles[2].animate.move_to(detector_up.get_left() + DOWN * 0.1),
            run_time=0.5,
        )

        # More particles
        self.play(*[FadeIn(p) for p in particles[3:]], run_time=0.3)
        self.play(
            *[p.animate.move_to(magnet_center) for p in particles[3:]],
            run_time=0.5,
        )
        self.play(
            particles[3].animate.move_to(detector_down.get_left() + UP * 0.1),
            particles[4].animate.move_to(detector_up.get_left() + DOWN * 0.2),
            particles[5].animate.move_to(detector_down.get_left() + DOWN * 0.1),
            run_time=0.5,
        )

        # Fade out particles
        self.play(*[FadeOut(p) for p in particles], run_time=0.3)

    def create_results_panel(self) -> VGroup:
        """Create the results display panel."""
        # Box
        box = Rectangle(
            width=8,
            height=1.5,
            color=QBPColors.BRASS,
            fill_color=QBPColors.DARK_SLATE,
            fill_opacity=0.8,
        )

        # Results text
        header = Text("RESULTS (n = 1,000,000)", color=QBPColors.BRASS, font_size=20)
        header.next_to(box.get_top(), DOWN, buff=0.2)

        up_result = Text(
            "Spin Up (+1):   ~50.0%",
            color=QBPColors.TEAL,
            font_size=18,
        )
        up_result.next_to(header, DOWN, buff=0.2)
        up_result.align_to(box, LEFT)
        up_result.shift(RIGHT * 0.5)

        down_result = Text(
            "Spin Down (-1): ~50.0%",
            color=QBPColors.CRIMSON,
            font_size=18,
        )
        down_result.next_to(up_result, DOWN, buff=0.1)
        down_result.align_to(up_result, LEFT)

        # Agreement indicator
        indicator = Circle(
            radius=0.15,
            color=QBPColors.TEAL,
            fill_opacity=1.0,
        )
        indicator.next_to(box.get_right(), LEFT, buff=0.5)

        match_text = Text("Matches QM", color=QBPColors.TEAL, font_size=14)
        match_text.next_to(indicator, DOWN, buff=0.1)

        return VGroup(box, header, up_result, down_result, indicator, match_text)


class SternGerlachShort(QBPScene):
    """
    YouTube Short version - vertical format, under 60 seconds.

    Focus on the iconic moment: beam splitting into two discrete outcomes.
    """

    def construct(self):
        # Configure for vertical
        # Note: Resolution is set via command line --resolution 1080,1920

        # Title (brief)
        title = Text(
            "Spin Quantization",
            color=QBPColors.BRASS,
            font_size=48,
        )
        title.to_edge(UP, buff=1)

        # Subtitle
        subtitle = Text(
            "Stern-Gerlach",
            color=QBPColors.IVORY,
            font_size=32,
        )
        subtitle.next_to(title, DOWN, buff=0.3)

        self.play(Write(title), run_time=0.5)
        self.play(FadeIn(subtitle), run_time=0.3)
        self.wait(0.5)

        # Simple apparatus (vertical layout)
        source = Circle(radius=0.4, color=QBPColors.BRASS, fill_opacity=0.3)
        source.shift(UP * 1)

        magnet_frame = Rectangle(
            width=3,
            height=1,
            color=QBPColors.STEEL,
        )
        magnet_frame.next_to(source, DOWN, buff=0.8)

        n_label = Text("N", color=QBPColors.CRIMSON, font_size=36)
        n_label.move_to(magnet_frame.get_left() + RIGHT * 0.5)
        s_label = Text("S", color=QBPColors.TEAL, font_size=36)
        s_label.move_to(magnet_frame.get_right() + LEFT * 0.5)

        # Detectors
        det_up = Circle(radius=0.3, color=QBPColors.TEAL, fill_opacity=0.5)
        det_up.next_to(magnet_frame, DOWN, buff=1.5)
        det_up.shift(LEFT * 1.5)

        det_down = Circle(radius=0.3, color=QBPColors.CRIMSON, fill_opacity=0.5)
        det_down.next_to(magnet_frame, DOWN, buff=1.5)
        det_down.shift(RIGHT * 1.5)

        up_label = MathTex(r"+1", color=QBPColors.TEAL)
        up_label.next_to(det_up, DOWN, buff=0.2)

        down_label = MathTex(r"-1", color=QBPColors.CRIMSON)
        down_label.next_to(det_down, DOWN, buff=0.2)

        apparatus = VGroup(
            source,
            magnet_frame,
            n_label,
            s_label,
            det_up,
            det_down,
            up_label,
            down_label,
        )

        self.play(Create(apparatus), run_time=1)
        self.wait(0.3)

        # Animate particle stream
        for _ in range(3):
            # Particle from source
            particle = Dot(
                point=source.get_center(),
                radius=0.12,
                color=QBPColors.AMBER,
            )
            self.play(FadeIn(particle), run_time=0.1)

            # Move to magnet
            self.play(
                particle.animate.move_to(magnet_frame.get_center()),
                run_time=0.3,
            )

            # Split randomly
            import random

            if random.random() < 0.5:
                self.play(
                    particle.animate.move_to(det_up.get_center()),
                    particle.animate.set_color(QBPColors.TEAL),
                    run_time=0.3,
                )
            else:
                self.play(
                    particle.animate.move_to(det_down.get_center()),
                    particle.animate.set_color(QBPColors.CRIMSON),
                    run_time=0.3,
                )

            self.play(FadeOut(particle), run_time=0.1)

        # Key message
        key = Text(
            "Only two outcomes\npossible!",
            color=QBPColors.GOLD,
            font_size=36,
        )
        key.to_edge(DOWN, buff=1.5)

        self.play(Write(key), run_time=0.5)
        self.wait(1)

        # QBP branding
        brand = Text(
            "QBP Framework",
            color=QBPColors.BRASS,
            font_size=24,
        )
        brand.to_edge(DOWN, buff=0.5)
        self.play(FadeIn(brand), run_time=0.3)
        self.wait(0.5)


class SternGerlachDeepDive(QBPScene):
    """
    Extended technical walkthrough of the Stern-Gerlach experiment.

    Covers:
    - Historical context
    - Quaternionic state representation
    - Measurement postulate derivation
    - Full simulation results
    - Comparison with standard QM
    """

    def construct(self):
        # This is a placeholder for the full deep dive
        # Full implementation would include:
        # - Multiple scenes with transitions
        # - Mathematical derivations
        # - Code walkthrough
        # - Statistical analysis

        title = self.create_title(
            "Stern-Gerlach: Deep Dive",
            "A Complete Technical Walkthrough",
        )
        self.play(Write(title))
        self.wait(1)

        # Chapter 1: Introduction
        ch1 = Text(
            "Chapter 1: Historical Context",
            color=QBPColors.GOLD,
            font_size=36,
        )
        ch1.next_to(title, DOWN, buff=1)
        self.play(Write(ch1))
        self.wait(2)

        # Placeholder for remaining chapters
        chapters = [
            "Chapter 2: Quaternionic States",
            "Chapter 3: The Measurement Postulate",
            "Chapter 4: Simulation Results",
            "Chapter 5: Comparison with Standard QM",
        ]

        for ch_text in chapters:
            ch = Text(ch_text, color=QBPColors.IVORY, font_size=28)
            ch.next_to(ch1, DOWN, buff=0.5)
            self.play(Transform(ch1, ch), run_time=0.5)
            self.wait(1)

        # End card
        self.play(FadeOut(ch1), FadeOut(title))

        end = Text(
            "Full deep dive: 90+ minutes\nSee docs for chapter timestamps",
            color=QBPColors.BRASS,
            font_size=28,
        )
        self.play(Write(end))
        self.wait(2)
