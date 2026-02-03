"""
QBP Base Scene for Manim

Provides a themed base scene class that applies the QBP Futuristic Steampunk
design system to all Manim animations.

Usage:
    from viz.manim import QBPScene

    class MyExperiment(QBPScene):
        def construct(self):
            title = self.create_title("Stern-Gerlach Experiment")
            self.play(Write(title))
"""

from manim import (
    Scene,
    config,
    Text,
    MathTex,
    Tex,
    VGroup,
    UP,
    DOWN,
    LEFT,
    RIGHT,
    Write,
    FadeIn,
    FadeOut,
    Create,
    Rectangle,
    Line,
)


class QBPColors:
    """
    QBP Design System colors converted to Manim hex format.

    Based on the Futuristic Steampunk theme from src/viz/theme.py
    """

    # --- Primary: The Metals ---
    BRASS = "#D4A574"
    COPPER = "#B87333"
    BRONZE = "#CD7F32"
    STEEL = "#71797E"
    GOLD = "#FFD700"

    # --- Secondary: The Elements ---
    TEAL = "#2A9D8F"
    VERDIGRIS = "#4A766E"
    AMBER = "#F4A261"
    CRIMSON = "#9B2335"
    IVORY = "#FFFEF0"

    # --- Backgrounds ---
    PARCHMENT = "#F5E6D3"
    DARK_SLATE = "#1A1A2E"
    MIDNIGHT = "#0D1B2A"

    # --- Utility ---
    SHADOW = "#2C2C2C"
    LIGHT_GRAY = "#E8E4E0"

    # --- Semantic ---
    AXIS_X = CRIMSON
    AXIS_Y = VERDIGRIS
    AXIS_Z = TEAL

    PRIMARY = BRASS
    SECONDARY = COPPER
    TERTIARY = TEAL
    ACCENT = AMBER

    # --- Spin States ---
    SPIN_UP = TEAL
    SPIN_DOWN = CRIMSON
    SUPERPOSITION = AMBER


# Manim configuration theme
MANIM_THEME = {
    "background_color": QBPColors.DARK_SLATE,
    "text_color": QBPColors.IVORY,
}


class QBPScene(Scene):
    """
    Base scene class with QBP theming applied.

    All QBP Manim scenes should inherit from this class to ensure
    consistent styling across all animations.
    """

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        # Apply theme
        config.background_color = QBPColors.DARK_SLATE

    def create_title(
        self,
        text: str,
        subtitle: str = None,
        scale: float = 1.0,
    ) -> VGroup:
        """
        Create a styled title with optional subtitle.

        Args:
            text: Main title text
            subtitle: Optional subtitle
            scale: Scale factor for the title

        Returns:
            VGroup containing title elements
        """
        title = Text(
            text,
            color=QBPColors.BRASS,
            font_size=48 * scale,
        )

        if subtitle:
            sub = Text(
                subtitle,
                color=QBPColors.IVORY,
                font_size=24 * scale,
            )
            sub.next_to(title, DOWN, buff=0.3)
            return VGroup(title, sub)

        return VGroup(title)

    def create_equation(
        self,
        latex: str,
        color: str = None,
    ) -> MathTex:
        """
        Create a styled mathematical equation.

        Args:
            latex: LaTeX string for the equation
            color: Optional color override

        Returns:
            MathTex object
        """
        return MathTex(
            latex,
            color=color or QBPColors.IVORY,
        )

    def create_label(
        self,
        text: str,
        color: str = None,
        font_size: int = 24,
    ) -> Text:
        """
        Create a styled text label.

        Args:
            text: Label text
            color: Optional color override
            font_size: Font size

        Returns:
            Text object
        """
        return Text(
            text,
            color=color or QBPColors.IVORY,
            font_size=font_size,
        )

    def create_info_panel(
        self,
        experiment_name: str,
        status: str,
        what: str,
        why: str,
        math: str,
        insight: str,
    ) -> VGroup:
        """
        Create an information panel following the James Review Dashboard standard.

        Args:
            experiment_name: Name of the experiment
            status: Current status (Passed/In Progress/Failed)
            what: One sentence description
            why: Physical significance
            math: Core equation (LaTeX)
            insight: Key insight about QBP model

        Returns:
            VGroup containing the info panel
        """
        # Status color
        status_colors = {
            "Passed": QBPColors.TEAL,
            "In Progress": QBPColors.AMBER,
            "Failed": QBPColors.CRIMSON,
        }
        status_color = status_colors.get(status, QBPColors.IVORY)

        # Build panel
        header = Text(
            f"EXPERIMENT: {experiment_name}",
            color=QBPColors.BRASS,
            font_size=32,
        )

        status_text = Text(
            f"STATUS: {status}",
            color=status_color,
            font_size=24,
        )
        status_text.next_to(header, DOWN, buff=0.2, aligned_edge=LEFT)

        # Separator
        sep1 = Line(
            start=LEFT * 4,
            end=RIGHT * 4,
            color=QBPColors.BRASS,
            stroke_width=2,
        )
        sep1.next_to(status_text, DOWN, buff=0.3)

        # What/Why/Math
        what_label = Text("WHAT: ", color=QBPColors.BRASS, font_size=20)
        what_text = Text(what, color=QBPColors.IVORY, font_size=20)
        what_text.next_to(what_label, RIGHT, buff=0.1)
        what_group = VGroup(what_label, what_text)
        what_group.next_to(sep1, DOWN, buff=0.2, aligned_edge=LEFT)

        why_label = Text("WHY:  ", color=QBPColors.BRASS, font_size=20)
        why_text = Text(why, color=QBPColors.IVORY, font_size=20)
        why_text.next_to(why_label, RIGHT, buff=0.1)
        why_group = VGroup(why_label, why_text)
        why_group.next_to(what_group, DOWN, buff=0.1, aligned_edge=LEFT)

        math_label = Text("MATH: ", color=QBPColors.BRASS, font_size=20)
        math_eq = MathTex(math, color=QBPColors.IVORY, font_size=20)
        math_eq.next_to(math_label, RIGHT, buff=0.1)
        math_group = VGroup(math_label, math_eq)
        math_group.next_to(why_group, DOWN, buff=0.1, aligned_edge=LEFT)

        # Separator
        sep2 = Line(
            start=LEFT * 4,
            end=RIGHT * 4,
            color=QBPColors.BRASS,
            stroke_width=2,
        )
        sep2.next_to(math_group, DOWN, buff=0.3)

        # Key insight
        insight_label = Text("KEY INSIGHT: ", color=QBPColors.GOLD, font_size=20)
        insight_label.next_to(sep2, DOWN, buff=0.2, aligned_edge=LEFT)

        insight_text = Text(
            insight,
            color=QBPColors.IVORY,
            font_size=18,
        )
        insight_text.next_to(insight_label, DOWN, buff=0.1, aligned_edge=LEFT)

        panel = VGroup(
            header,
            status_text,
            sep1,
            what_group,
            why_group,
            math_group,
            sep2,
            insight_label,
            insight_text,
        )

        return panel

    def create_comparison_indicator(
        self,
        model_pred: str,
        qm_pred: str,
        measurement: str,
        agreement: str,  # "match", "partial", "mismatch"
    ) -> VGroup:
        """
        Create a comparison indicator showing model vs QM predictions.

        Args:
            model_pred: QBP model prediction
            qm_pred: Standard QM prediction
            measurement: Simulation/experiment result
            agreement: Level of agreement

        Returns:
            VGroup containing the comparison
        """
        agreement_colors = {
            "match": QBPColors.TEAL,
            "partial": QBPColors.AMBER,
            "mismatch": QBPColors.CRIMSON,
        }
        indicator_color = agreement_colors.get(agreement, QBPColors.IVORY)

        model_label = Text("QBP Model: ", color=QBPColors.BRASS, font_size=18)
        model_value = Text(model_pred, color=QBPColors.IVORY, font_size=18)
        model_value.next_to(model_label, RIGHT, buff=0.1)
        model_group = VGroup(model_label, model_value)

        qm_label = Text("Standard QM: ", color=QBPColors.BRASS, font_size=18)
        qm_value = Text(qm_pred, color=QBPColors.IVORY, font_size=18)
        qm_value.next_to(qm_label, RIGHT, buff=0.1)
        qm_group = VGroup(qm_label, qm_value)
        qm_group.next_to(model_group, DOWN, buff=0.1, aligned_edge=LEFT)

        meas_label = Text("Measurement: ", color=QBPColors.BRASS, font_size=18)
        meas_value = Text(measurement, color=QBPColors.IVORY, font_size=18)
        meas_value.next_to(meas_label, RIGHT, buff=0.1)
        meas_group = VGroup(meas_label, meas_value)
        meas_group.next_to(qm_group, DOWN, buff=0.1, aligned_edge=LEFT)

        # Agreement indicator
        indicator = Rectangle(
            width=0.3,
            height=0.3,
            color=indicator_color,
            fill_opacity=1.0,
        )
        indicator.next_to(meas_group, RIGHT, buff=0.5)

        return VGroup(model_group, qm_group, meas_group, indicator)
