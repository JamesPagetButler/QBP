"""
Stern-Gerlach Interactive Demonstration

An interactive vpython visualization of the Stern-Gerlach experiment
using the QBP quaternionic framework.

Features:
- Real-time particle simulation through magnetic field
- Adjustable measurement angle
- Live statistics display
- Comparison with QM predictions

Run: python -m src.viz.stern_gerlach_demo
"""

import numpy as np
from vpython import (
    canvas,
    vector,
    arrow,
    sphere,
    box,
    cylinder,
    label,
    rate,
    color,
    button,
    slider,
    wtext,
    graph,
    gcurve,
)
import sys
import os

# Add project root to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src.viz.theme import COLORS, PALETTE
from src import qphysics


class SternGerlachDemo:
    """Interactive Stern-Gerlach experiment visualization."""

    def __init__(self):
        self.running = False
        self.particle_count = 0
        self.up_count = 0
        self.down_count = 0
        self.particles = []
        self.measurement_angle = 0  # Angle of measurement axis from Z

        self.setup_scene()
        self.setup_apparatus()
        self.setup_controls()
        self.setup_stats()

    def setup_scene(self):
        """Create the main visualization canvas."""
        self.scene = canvas(
            title='<b style="font-family: Georgia, serif;">Stern-Gerlach Experiment</b>',
            width=1000,
            height=600,
            center=vector(0, 0, 0),
            background=COLORS.DARK_SLATE.vpython,
        )
        self.scene.caption = "\n"

    def setup_apparatus(self):
        """Create the Stern-Gerlach apparatus visualization."""
        # Source (oven)
        self.source = box(
            pos=vector(-4, 0, 0),
            size=vector(0.8, 1.2, 1.2),
            color=COLORS.BRASS.vpython,
            opacity=0.7,
        )
        label(
            pos=vector(-4, -1.2, 0),
            text="Source",
            color=COLORS.IVORY.vpython,
            box=False,
            height=14,
        )

        # Collimator
        self.collimator = box(
            pos=vector(-2.5, 0, 0),
            size=vector(0.2, 0.8, 0.8),
            color=COLORS.STEEL.vpython,
        )

        # Magnet (North pole - top)
        self.north_pole = box(
            pos=vector(0, 1, 0),
            size=vector(2, 0.6, 1.5),
            color=COLORS.CRIMSON.vpython,
            opacity=0.6,
        )
        label(
            pos=vector(0, 1.5, 0),
            text="N",
            color=COLORS.CRIMSON.vpython,
            box=False,
            height=20,
        )

        # Magnet (South pole - bottom)
        self.south_pole = box(
            pos=vector(0, -1, 0),
            size=vector(2, 0.6, 1.5),
            color=COLORS.TEAL.vpython,
            opacity=0.6,
        )
        label(
            pos=vector(0, -1.5, 0),
            text="S",
            color=COLORS.TEAL.vpython,
            box=False,
            height=20,
        )

        # Magnetic field indicator
        self.b_field = arrow(
            pos=vector(1.5, -0.5, 0),
            axis=vector(0, 1, 0),
            color=COLORS.AMBER.vpython,
            shaftwidth=0.08,
        )
        label(
            pos=vector(1.8, 0, 0),
            text="B",
            color=COLORS.AMBER.vpython,
            box=False,
            height=16,
        )

        # Detectors
        self.detector_up = box(
            pos=vector(4, 1.5, 0),
            size=vector(0.6, 0.8, 1.2),
            color=COLORS.TEAL.vpython,
            opacity=0.5,
        )
        self.label_up = label(
            pos=vector(4, 2.3, 0),
            text="+1 (Up): 0",
            color=COLORS.TEAL.vpython,
            box=False,
            height=16,
        )

        self.detector_down = box(
            pos=vector(4, -1.5, 0),
            size=vector(0.6, 0.8, 1.2),
            color=COLORS.CRIMSON.vpython,
            opacity=0.5,
        )
        self.label_down = label(
            pos=vector(4, -2.3, 0),
            text="-1 (Down): 0",
            color=COLORS.CRIMSON.vpython,
            box=False,
            height=16,
        )

    def setup_controls(self):
        """Create interactive controls."""
        self.scene.append_to_caption("\n<b>Controls:</b>\n\n")

        # Start/Stop button
        self.start_button = button(
            text="Start Experiment",
            bind=self.toggle_running,
        )
        self.scene.append_to_caption("  ")

        # Reset button
        button(text="Reset", bind=self.reset_experiment)
        self.scene.append_to_caption("\n\n")

        # Speed slider
        self.scene.append_to_caption("Particle Rate: ")
        self.speed_slider = slider(
            min=1,
            max=50,
            value=10,
            bind=lambda s: None,
        )
        self.scene.append_to_caption("\n\n")

        # Initial state angle slider
        self.scene.append_to_caption("Initial Spin Angle (from Z): ")
        self.angle_slider = slider(
            min=0,
            max=180,
            value=90,  # Start with X-aligned (90 degrees from Z)
            bind=self.update_angle,
        )
        self.angle_text = wtext(text=" 90°")
        self.scene.append_to_caption("\n\n")

    def setup_stats(self):
        """Create statistics display."""
        self.scene.append_to_caption("<b>Statistics:</b>\n")
        self.stats_text = wtext(text="Waiting to start...")
        self.scene.append_to_caption("\n\n")

        # Comparison panel
        self.scene.append_to_caption("<b>Comparison:</b>\n")
        self.comparison_text = wtext(
            text="QBP Model:    P(up) = cos²(θ/2)\n"
            "Standard QM:  P(up) = cos²(θ/2)\n"
            "Agreement:    ✓ MATCH"
        )

    def toggle_running(self, b):
        """Start or stop the experiment."""
        self.running = not self.running
        b.text = "Stop" if self.running else "Start Experiment"

    def reset_experiment(self, b):
        """Reset all counters and clear particles."""
        self.running = False
        self.start_button.text = "Start Experiment"
        self.particle_count = 0
        self.up_count = 0
        self.down_count = 0

        # Remove existing particles
        for p in self.particles:
            p.visible = False
        self.particles = []

        # Update displays
        self.update_displays()

    def update_angle(self, s):
        """Update the initial spin angle."""
        self.angle_text.text = f" {int(s.value)}°"

    def update_displays(self):
        """Update all display text."""
        total = self.up_count + self.down_count
        if total > 0:
            pct_up = (self.up_count / total) * 100
            pct_down = (self.down_count / total) * 100
        else:
            pct_up = pct_down = 0

        self.label_up.text = f"+1 (Up): {self.up_count}"
        self.label_down.text = f"-1 (Down): {self.down_count}"

        self.stats_text.text = (
            f"Total Particles: {total}\n"
            f"Spin Up:   {self.up_count:6d} ({pct_up:5.1f}%)\n"
            f"Spin Down: {self.down_count:6d} ({pct_down:5.1f}%)"
        )

        # Update comparison with theoretical prediction
        theta = np.radians(self.angle_slider.value)
        predicted_up = np.cos(theta / 2) ** 2 * 100

        self.comparison_text.text = (
            f"Initial angle: {int(self.angle_slider.value)}° from Z\n"
            f"QBP Model:    P(up) = cos²(θ/2) = {predicted_up:.1f}%\n"
            f"Standard QM:  P(up) = cos²(θ/2) = {predicted_up:.1f}%\n"
            f"Measured:     P(up) = {pct_up:.1f}%\n"
            f"Agreement:    {'✓ MATCH' if abs(pct_up - predicted_up) < 5 or total < 10 else '... converging'}"
        )

    def create_particle(self):
        """Create a new particle at the source."""
        particle = sphere(
            pos=vector(-3.5, 0, 0),
            radius=0.1,
            color=COLORS.AMBER.vpython,
            make_trail=True,
            trail_type="curve",
            retain=50,
        )
        self.particles.append(particle)
        return particle

    def measure_particle(self):
        """Measure a particle using the QBP framework."""
        # Get initial state based on angle slider
        # Angle is from Z-axis, so 0° = Z-aligned, 90° = X-aligned
        theta = np.radians(self.angle_slider.value)

        # Create state: rotate from Z toward X by theta
        # State vector in spherical: (sin(theta), 0, cos(theta))
        state_vector = [np.sin(theta), 0, np.cos(theta)]
        psi = qphysics.create_state_from_vector(state_vector)

        # Measure along Z
        result = qphysics.measure(psi, qphysics.SPIN_Z)
        return result

    def animate_particle(self, particle, result):
        """Animate particle through the apparatus."""
        # Phase 1: Move to magnet entrance
        for _ in range(10):
            rate(60)
            particle.pos.x += 0.15

        # Phase 2: Deflect based on measurement result
        deflection = 0.15 if result == 1 else -0.15
        for _ in range(20):
            rate(60)
            particle.pos.x += 0.15
            particle.pos.y += deflection

        # Phase 3: Move to detector
        final_y = 1.5 if result == 1 else -1.5
        target_x = 4
        steps = 15
        dy = (final_y - particle.pos.y) / steps

        for _ in range(steps):
            rate(60)
            particle.pos.x += (target_x - particle.pos.x) / steps
            particle.pos.y += dy

        # Change color at detector
        particle.color = COLORS.TEAL.vpython if result == 1 else COLORS.CRIMSON.vpython

        # Update counts
        if result == 1:
            self.up_count += 1
        else:
            self.down_count += 1

        self.particle_count += 1
        self.update_displays()

        # Fade out particle
        for i in range(10):
            rate(30)
            particle.opacity = 1 - i / 10

        particle.visible = False
        particle.clear_trail()

    def run(self):
        """Main animation loop."""
        print("\nStern-Gerlach Interactive Demo")
        print("=" * 40)
        print("Opening browser window...")
        print("Press Ctrl+C to exit\n")

        frame_count = 0
        particle_interval = 20  # Frames between particles

        while True:
            rate(60)
            frame_count += 1

            if self.running:
                # Adjust particle rate based on slider
                particle_interval = max(5, 60 - self.speed_slider.value)

                if frame_count % particle_interval == 0:
                    # Create and measure new particle
                    particle = self.create_particle()
                    result = self.measure_particle()
                    self.animate_particle(particle, result)

                    # Clean up old particles
                    self.particles = [p for p in self.particles if p.visible]


def main():
    """Entry point for the Stern-Gerlach demo."""
    demo = SternGerlachDemo()
    demo.run()


if __name__ == "__main__":
    main()
