# analysis/01b_angle_dependent/bloch_sphere.py
"""
Interactive Bloch Sphere Visualization for Experiment 01b

Demonstrates angle-dependent measurement probability P(+) = cos²(θ/2)
using an interactive 3D Bloch sphere with a slider to sweep angles.

Features:
- Rotatable 3D Bloch sphere with wireframe
- State vector ψ(θ) tilted at angle θ from z-axis
- Measurement axis (z) shown as reference
- Real-time probability display as angle changes
- Comparison with theoretical prediction

Run: python analysis/01b_angle_dependent/bloch_sphere.py
"""

import numpy as np
import sys
import os

# Add project root to path for imports
project_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, project_root)

from vpython import (
    canvas,
    vector,
    arrow,
    sphere,
    ring,
    curve,
    label,
    rate,
    slider,
    wtext,
    color,
    button,
)

from src.viz.theme import COLORS, PALETTE


class BlochSphereDemo:
    """Interactive Bloch sphere visualization for angle-dependent measurement."""

    def __init__(self):
        self.theta_deg = 45  # Initial angle
        self.setup_scene()
        self.setup_bloch_sphere()
        self.setup_vectors()
        self.setup_controls()
        self.setup_info_panel()
        self.update_state(None)  # Initialize display

    def setup_scene(self):
        """Create the main visualization canvas."""
        self.scene = canvas(
            title='<b style="font-family: Georgia, serif;">⚙ Bloch Sphere: Angle-Dependent Measurement ⚙</b>',
            width=1000,
            height=700,
            center=vector(0, 0, 0),
            background=COLORS.DARK_SLATE.vpython,
            forward=vector(-0.5, -0.3, -1),  # Angled view
            up=vector(0, 1, 0),
        )

    def setup_bloch_sphere(self):
        """Create the Bloch sphere wireframe."""
        # Main sphere (transparent)
        self.bloch_sphere = sphere(
            pos=vector(0, 0, 0),
            radius=1.0,
            color=COLORS.STEEL.vpython,
            opacity=0.1,
        )

        # Equatorial ring (XY plane)
        ring(
            pos=vector(0, 0, 0),
            axis=vector(0, 1, 0),  # Normal to XY plane
            radius=1.0,
            thickness=0.015,
            color=COLORS.STEEL.vpython,
        )

        # Meridian ring (XZ plane) - the plane where we rotate
        ring(
            pos=vector(0, 0, 0),
            axis=vector(0, 0, 1),  # Normal to XZ plane (around Y)
            radius=1.0,
            thickness=0.02,
            color=COLORS.BRASS.vpython,
        )

        # Meridian ring (YZ plane)
        ring(
            pos=vector(0, 0, 0),
            axis=vector(1, 0, 0),  # Normal to YZ plane
            radius=1.0,
            thickness=0.015,
            color=COLORS.STEEL.vpython,
        )

        # Coordinate axes (subdued)
        axis_length = 1.4
        axis_width = 0.02

        # X-axis
        arrow(
            pos=vector(0, 0, 0),
            axis=vector(axis_length, 0, 0),
            color=PALETTE.AXIS_X.vpython,
            shaftwidth=axis_width,
            opacity=0.6,
        )
        label(
            pos=vector(axis_length + 0.15, 0, 0),
            text="X",
            color=PALETTE.AXIS_X.vpython,
            box=False,
            height=14,
            opacity=0.8,
        )

        # Y-axis
        arrow(
            pos=vector(0, 0, 0),
            axis=vector(0, axis_length, 0),
            color=PALETTE.AXIS_Y.vpython,
            shaftwidth=axis_width,
            opacity=0.6,
        )
        label(
            pos=vector(0, axis_length + 0.15, 0),
            text="Y",
            color=PALETTE.AXIS_Y.vpython,
            box=False,
            height=14,
            opacity=0.8,
        )

        # Z-axis (measurement axis - highlighted)
        arrow(
            pos=vector(0, 0, 0),
            axis=vector(0, 0, axis_length),
            color=PALETTE.AXIS_Z.vpython,
            shaftwidth=axis_width,
            opacity=0.6,
        )
        label(
            pos=vector(0, 0, axis_length + 0.15),
            text="Z",
            color=PALETTE.AXIS_Z.vpython,
            box=False,
            height=14,
            opacity=0.8,
        )

        # Poles labels
        label(
            pos=vector(0, 0, 1.25),
            text="|+⟩",
            color=COLORS.TEAL.vpython,
            box=False,
            height=16,
        )
        label(
            pos=vector(0, 0, -1.25),
            text="|−⟩",
            color=COLORS.CRIMSON.vpython,
            box=False,
            height=16,
        )

    def setup_vectors(self):
        """Create the state and measurement vectors."""
        # Measurement axis (O = k, along z) - TEAL, prominent
        self.measurement_arrow = arrow(
            pos=vector(0, 0, 0),
            axis=vector(0, 0, 1.0),
            color=COLORS.TEAL.vpython,
            shaftwidth=0.06,
            headwidth=0.15,
            headlength=0.12,
        )
        self.measurement_label = label(
            pos=vector(0.2, 0, 0.7),
            text="O (measure)",
            color=COLORS.TEAL.vpython,
            box=False,
            height=12,
        )

        # State vector ψ(θ) - BRASS/GOLD, prominent
        self.state_arrow = arrow(
            pos=vector(0, 0, 0),
            axis=vector(0.707, 0, 0.707),  # Initial 45°
            color=COLORS.BRASS.vpython,
            shaftwidth=0.07,
            headwidth=0.18,
            headlength=0.14,
        )

        # Glowing tip for state vector
        self.state_tip = sphere(
            pos=vector(0.707, 0, 0.707),
            radius=0.06,
            color=COLORS.GOLD.vpython,
            emissive=True,
        )

        self.state_label = label(
            pos=vector(0.5, 0.2, 0.5),
            text="ψ(θ)",
            color=COLORS.GOLD.vpython,
            box=False,
            height=14,
        )

        # Arc showing the angle θ
        self.angle_arc = self.create_angle_arc(45)

        # Angle label
        self.angle_label = label(
            pos=vector(0.25, 0, 0.35),
            text="θ = 45°",
            color=COLORS.AMBER.vpython,
            box=False,
            height=12,
        )

        # Projection line (dashed effect via opacity)
        self.projection_line = curve(
            [vector(0.707, 0, 0.707), vector(0, 0, 0.707)],
            color=COLORS.AMBER.vpython,
            radius=0.008,
        )

    def create_angle_arc(self, theta_deg):
        """Create an arc showing the angle between state and z-axis."""
        # Remove old arc if exists
        if hasattr(self, 'angle_arc') and self.angle_arc:
            self.angle_arc.visible = False

        theta_rad = np.radians(theta_deg)
        arc_radius = 0.3
        n_points = max(3, int(theta_deg / 5) + 1)

        points = []
        for i in range(n_points + 1):
            angle = (i / n_points) * theta_rad
            x = arc_radius * np.sin(angle)
            z = arc_radius * np.cos(angle)
            points.append(vector(x, 0, z))

        return curve(points, color=COLORS.AMBER.vpython, radius=0.012)

    def setup_controls(self):
        """Create interactive controls."""
        self.scene.append_to_caption(
            "\n<hr style='border-color: #D4A574; margin: 10px 0;'>\n"
        )
        self.scene.append_to_caption(
            "<h3 style='color: #D4A574; font-family: Georgia; margin: 0 0 10px 0;'>🎮 ANGLE CONTROL</h3>\n"
        )

        self.scene.append_to_caption(
            "<span style='color: #FFFEF0; font-size: 14px;'>State angle θ from Z-axis: </span>"
        )
        self.angle_slider = slider(
            min=0,
            max=180,
            value=45,
            step=1,
            bind=self.update_state,
            length=400,
        )
        self.angle_text = wtext(text=" <b style='color: #F4A261;'>45°</b>")
        self.scene.append_to_caption("\n\n")

        # Quick angle buttons
        self.scene.append_to_caption(
            "<span style='color: #FFFEF0;'>Quick angles: </span>"
        )
        for angle in [0, 30, 45, 60, 90, 120, 180]:
            button(
                text=f"{angle}°",
                bind=lambda b, a=angle: self.set_angle(a),
            )
            self.scene.append_to_caption(" ")
        self.scene.append_to_caption("\n")

    def setup_info_panel(self):
        """Create the probability and formula display."""
        self.scene.append_to_caption(
            "\n<hr style='border-color: #D4A574; margin: 15px 0;'>\n"
        )

        # Probability display
        self.scene.append_to_caption(
            "<h3 style='color: #FFD700; font-family: Georgia; margin: 0 0 10px 0;'>📊 MEASUREMENT PROBABILITY</h3>\n"
        )
        self.prob_text = wtext(text=self.format_probability(45))
        self.scene.append_to_caption("\n")

        # Formula explanation
        self.scene.append_to_caption(
            "\n<hr style='border-color: #D4A574; margin: 15px 0;'>\n"
        )
        self.scene.append_to_caption(
            "<h3 style='color: #D4A574; font-family: Georgia; margin: 0 0 10px 0;'>📐 THE PHYSICS</h3>\n"
        )
        self.scene.append_to_caption("""
<div style="font-family: Georgia; color: #FFFEF0; font-size: 13px; line-height: 1.6;">
<p><b style="color: #D4A574;">State:</b> ψ(θ) = sin(θ)·<b>i</b> + cos(θ)·<b>k</b></p>
<p><b style="color: #2A9D8F;">Observable:</b> O = <b>k</b> (measurement along Z)</p>
<p><b style="color: #F4A261;">Expectation:</b> ⟨O⟩ = vecDot(ψ, O) = cos(θ)</p>
<p><b style="color: #FFD700;">Probability:</b> P(+) = (1 + cos θ)/2 = cos²(θ/2)</p>
</div>
""")

        # Key insight
        self.scene.append_to_caption(
            "\n<div style='border-left: 3px solid #F4A261; padding-left: 10px; margin: 10px 0;'>\n"
        )
        self.scene.append_to_caption(
            "<p style='color: #F4A261; font-family: Georgia; font-size: 13px; margin: 0;'>"
            "<b>Key Insight:</b> The quaternion dot product equals cos(θ) — "
            "the projection of the state onto the measurement axis. "
            "This geometric fact is why quantum probabilities follow cos²(θ/2).</p>\n"
        )
        self.scene.append_to_caption("</div>\n")

    def format_probability(self, theta_deg):
        """Format the probability display for a given angle."""
        theta_rad = np.radians(theta_deg)
        cos_theta = np.cos(theta_rad)
        p_up = (1 + cos_theta) / 2
        p_down = 1 - p_up

        # Also show cos²(θ/2) form
        cos_half = np.cos(theta_rad / 2)
        cos_sq_half = cos_half ** 2

        return f"""
<table style="font-family: Georgia; color: #FFFEF0; font-size: 14px;">
<tr><td style="color: #2A9D8F; padding-right: 20px;"><b>P(+1) = </b></td>
    <td><b>{p_up:.4f}</b></td>
    <td style="color: #888; padding-left: 15px;">= cos²({theta_deg}°/2) = cos²({theta_deg/2:.1f}°) = {cos_sq_half:.4f}</td></tr>
<tr><td style="color: #9B2335; padding-right: 20px;"><b>P(−1) = </b></td>
    <td><b>{p_down:.4f}</b></td>
    <td style="color: #888; padding-left: 15px;">= sin²({theta_deg}°/2) = {1-cos_sq_half:.4f}</td></tr>
<tr><td colspan="3" style="padding-top: 8px; color: #F4A261;">
    cos(θ) = cos({theta_deg}°) = {cos_theta:.4f}</td></tr>
</table>
"""

    def set_angle(self, angle):
        """Set angle from button click."""
        self.angle_slider.value = angle
        self.update_state(None)

    def update_state(self, s):
        """Update the visualization when angle changes."""
        theta_deg = self.angle_slider.value
        theta_rad = np.radians(theta_deg)

        # State vector direction: ψ(θ) = sin(θ)·i + cos(θ)·k
        # In our coordinate system: x = sin(θ), z = cos(θ)
        x = np.sin(theta_rad)
        z = np.cos(theta_rad)

        # Update state arrow
        self.state_arrow.axis = vector(x, 0, z)
        self.state_tip.pos = vector(x, 0, z)

        # Update state label position
        label_offset = 0.2
        self.state_label.pos = vector(x + label_offset, label_offset, z)

        # Update angle arc
        self.angle_arc.visible = False
        self.angle_arc = self.create_angle_arc(theta_deg)

        # Update angle label
        arc_mid_angle = theta_rad / 2
        label_r = 0.4
        self.angle_label.pos = vector(
            label_r * np.sin(arc_mid_angle),
            0.1,
            label_r * np.cos(arc_mid_angle)
        )
        self.angle_label.text = f"θ = {theta_deg:.0f}°"

        # Update projection line
        self.projection_line.clear()
        if theta_deg > 0 and theta_deg < 180:
            self.projection_line.append(vector(x, 0, z))
            self.projection_line.append(vector(0, 0, z))

        # Update text displays
        self.angle_text.text = f" <b style='color: #F4A261;'>{theta_deg:.0f}°</b>"
        self.prob_text.text = self.format_probability(theta_deg)

    def run(self):
        """Main loop - keep the visualization running."""
        print("\n" + "=" * 55)
        print("  ⚙  BLOCH SPHERE: ANGLE-DEPENDENT MEASUREMENT  ⚙")
        print("=" * 55)
        print("\nOpening browser window...")
        print("Use the slider to change the state angle θ.")
        print("Press Ctrl+C to exit.\n")

        while True:
            rate(30)


def main():
    """Entry point for the Bloch sphere demo."""
    demo = BlochSphereDemo()
    demo.run()


if __name__ == "__main__":
    main()
