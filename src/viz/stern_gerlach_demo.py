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
)
import sys
import os

# Add project root to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src.viz.theme import COLORS, PALETTE
from src import qphysics


class Particle:
    """A particle with its own animation state."""

    def __init__(self, sphere_obj, result, start_x=-3.5):
        self.sphere = sphere_obj
        self.result = result  # +1 or -1
        self.phase = 0  # 0=traveling, 1=deflecting, 2=to_detector, 3=fading, 4=done
        self.step = 0
        self.start_x = start_x
        self.target_y = 1.5 if result == 1 else -1.5
        self.deflection = 0.08 if result == 1 else -0.08

    def update(self):
        """Update particle position for one frame. Returns True if still active."""
        if self.phase == 0:  # Traveling to magnet
            self.sphere.pos.x += 0.12
            self.step += 1
            if self.step >= 12:
                self.phase = 1
                self.step = 0
        elif self.phase == 1:  # Deflecting in magnet
            self.sphere.pos.x += 0.08
            self.sphere.pos.y += self.deflection
            self.step += 1
            if self.step >= 20:
                self.phase = 2
                self.step = 0
        elif self.phase == 2:  # Moving to detector
            dx = (4 - self.sphere.pos.x) * 0.15
            dy = (self.target_y - self.sphere.pos.y) * 0.15
            self.sphere.pos.x += dx
            self.sphere.pos.y += dy
            self.step += 1
            if self.step >= 15:
                # Change color at detector
                if self.result == 1:
                    self.sphere.color = COLORS.TEAL.vpython
                else:
                    self.sphere.color = COLORS.CRIMSON.vpython
                self.phase = 3
                self.step = 0
        elif self.phase == 3:  # Fading out
            self.sphere.opacity -= 0.1
            self.step += 1
            if self.step >= 10:
                self.sphere.visible = False
                self.phase = 4
        return self.phase < 4


class SternGerlachDemo:
    """Interactive Stern-Gerlach experiment visualization."""

    def __init__(self):
        self.running = False
        self.particle_count = 0
        self.up_count = 0
        self.down_count = 0
        self.active_particles = []

        self.setup_scene()
        self.setup_info_panel()
        self.setup_apparatus()
        self.setup_controls()
        self.setup_stats()

    def setup_scene(self):
        """Create the main visualization canvas."""
        self.scene = canvas(
            title='<b style="font-family: Georgia, serif;">⚙ Stern-Gerlach Experiment ⚙</b>',
            width=1100,
            height=650,
            center=vector(0, 0, 0),
            background=COLORS.DARK_SLATE.vpython,
        )

    def setup_info_panel(self):
        """Create the experiment description and key observations panel."""
        self.scene.caption = """
<div style="font-family: Georgia, serif; padding: 10px; background: #1a1a2e; border: 1px solid #D4A574; margin: 10px 0;">
<h3 style="color: #D4A574; margin-top: 0;">📋 EXPERIMENT OVERVIEW</h3>
<p style="color: #FFFEF0; font-size: 14px;">
<b>What:</b> Silver atoms pass through an inhomogeneous magnetic field.<br>
<b>Classical prediction:</b> Continuous distribution (smeared line).<br>
<b>Quantum result:</b> Only TWO discrete spots (spin up or down).
</p>

<h3 style="color: #FFD700; margin-top: 15px;">🔍 WHAT TO OBSERVE</h3>
<ol style="color: #FFFEF0; font-size: 13px; margin-bottom: 0;">
<li><b>Binary Outcomes:</b> Each particle goes to EITHER +1 (teal) OR -1 (red) — never in between!</li>
<li><b>Probabilistic:</b> At 90° angle, expect ~50% up, ~50% down</li>
<li><b>Angle Dependence:</b> Change the angle slider to see P(up) = cos²(θ/2)</li>
<li><b>QBP = QM:</b> Our quaternionic model matches standard quantum mechanics exactly</li>
</ol>
</div>

<h3 style="color: #D4A574; font-family: Georgia, serif;">⚡ KEY INSIGHT</h3>
<p style="color: #F4A261; font-family: Georgia, serif; font-size: 14px; border-left: 3px solid #F4A261; padding-left: 10px;">
<b>Continuous input → Discrete output</b><br>
This is the hallmark of quantum mechanics: measurement forces a definite outcome from a superposition.
</p>
"""

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
            pos=vector(-4, -1.5, 0),
            text="Atomic\nSource",
            color=COLORS.IVORY.vpython,
            box=False,
            height=12,
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
            pos=vector(1.9, 0, 0),
            text="B field",
            color=COLORS.AMBER.vpython,
            box=False,
            height=12,
        )

        # Detectors
        self.detector_up = box(
            pos=vector(4, 1.5, 0),
            size=vector(0.6, 0.8, 1.2),
            color=COLORS.TEAL.vpython,
            opacity=0.5,
        )
        self.label_up = label(
            pos=vector(5.2, 1.5, 0),
            text="Spin UP (+1)\nCount: 0",
            color=COLORS.TEAL.vpython,
            box=False,
            height=14,
        )

        self.detector_down = box(
            pos=vector(4, -1.5, 0),
            size=vector(0.6, 0.8, 1.2),
            color=COLORS.CRIMSON.vpython,
            opacity=0.5,
        )
        self.label_down = label(
            pos=vector(5.2, -1.5, 0),
            text="Spin DOWN (-1)\nCount: 0",
            color=COLORS.CRIMSON.vpython,
            box=False,
            height=14,
        )

    def setup_controls(self):
        """Create interactive controls."""
        self.scene.append_to_caption("\n<hr style='border-color: #D4A574;'>\n")
        self.scene.append_to_caption(
            "<h3 style='color: #D4A574; font-family: Georgia;'>🎮 CONTROLS</h3>\n"
        )

        # Start/Stop button
        self.start_button = button(
            text="▶ Start Experiment",
            bind=self.toggle_running,
        )
        self.scene.append_to_caption("  ")

        # Reset button
        button(text="↺ Reset", bind=self.reset_experiment)
        self.scene.append_to_caption("\n\n")

        # Speed slider
        self.scene.append_to_caption(
            "<span style='color: #FFFEF0;'>Particle Rate: </span>"
        )
        self.speed_slider = slider(
            min=1,
            max=30,
            value=5,
            bind=lambda s: None,
        )
        self.scene.append_to_caption(
            " <i style='color: #888;'>(particles per second)</i>\n\n"
        )

        # Initial state angle slider
        self.scene.append_to_caption(
            "<span style='color: #FFFEF0;'>Initial Spin Angle from Z-axis: </span>"
        )
        self.angle_slider = slider(
            min=0,
            max=180,
            value=90,  # Start with X-aligned (90 degrees from Z)
            bind=self.update_angle,
        )
        self.angle_text = wtext(text=" <b>90°</b> (X-aligned → 50/50 split expected)")
        self.scene.append_to_caption("\n\n")

    def setup_stats(self):
        """Create statistics display."""
        self.scene.append_to_caption("<hr style='border-color: #D4A574;'>\n")
        self.scene.append_to_caption(
            "<h3 style='color: #D4A574; font-family: Georgia;'>📊 RESULTS</h3>\n"
        )
        self.stats_text = wtext(text="<i>Click 'Start Experiment' to begin...</i>")
        self.scene.append_to_caption("\n\n")

        # Comparison panel
        self.scene.append_to_caption(
            "<h3 style='color: #FFD700; font-family: Georgia;'>⚖️ QBP vs STANDARD QM</h3>\n"
        )
        self.comparison_text = wtext(
            text="<span style='color: #D4A574;'>QBP Model:</span>    P(up) = cos²(θ/2) = 50.0%<br>"
            "<span style='color: #888;'>Standard QM:</span>  P(up) = cos²(θ/2) = 50.0%<br>"
            "<span style='color: #2A9D8F;'><b>✓ PREDICTIONS MATCH</b></span>"
        )

    def toggle_running(self, b):
        """Start or stop the experiment."""
        self.running = not self.running
        b.text = "⏹ Stop" if self.running else "▶ Start Experiment"

    def reset_experiment(self, b):
        """Reset all counters and clear particles."""
        self.running = False
        self.start_button.text = "▶ Start Experiment"
        self.particle_count = 0
        self.up_count = 0
        self.down_count = 0

        # Remove existing particles
        for p in self.active_particles:
            p.sphere.visible = False
        self.active_particles = []

        # Update displays
        self.update_displays()

    def update_angle(self, s):
        """Update the initial spin angle."""
        angle = int(s.value)
        if angle == 0:
            desc = "(Z-aligned → 100% UP expected)"
        elif angle == 90:
            desc = "(X-aligned → 50/50 split expected)"
        elif angle == 180:
            desc = "(-Z-aligned → 100% DOWN expected)"
        else:
            theta = np.radians(angle)
            pred = np.cos(theta / 2) ** 2 * 100
            desc = f"(expect ~{pred:.0f}% UP)"
        self.angle_text.text = f" <b>{angle}°</b> {desc}"

    def update_displays(self):
        """Update all display text."""
        total = self.up_count + self.down_count
        if total > 0:
            pct_up = (self.up_count / total) * 100
            pct_down = (self.down_count / total) * 100
        else:
            pct_up = pct_down = 0

        self.label_up.text = f"Spin UP (+1)\nCount: {self.up_count}"
        self.label_down.text = f"Spin DOWN (-1)\nCount: {self.down_count}"

        self.stats_text.text = (
            f"<b>Total Particles:</b> {total}<br>"
            f"<span style='color: #2A9D8F;'>Spin Up (+1):</span>   {self.up_count:5d} ({pct_up:5.1f}%)<br>"
            f"<span style='color: #9B2335;'>Spin Down (-1):</span> {self.down_count:5d} ({pct_down:5.1f}%)"
        )

        # Update comparison with theoretical prediction
        theta = np.radians(self.angle_slider.value)
        predicted_up = np.cos(theta / 2) ** 2 * 100

        diff = abs(pct_up - predicted_up)
        if total < 10:
            status = "<span style='color: #888;'>⏳ Collecting data...</span>"
        elif diff < 3:
            status = "<span style='color: #2A9D8F;'><b>✓ EXCELLENT MATCH</b></span>"
        elif diff < 10:
            status = "<span style='color: #F4A261;'>↻ Converging...</span>"
        else:
            status = "<span style='color: #F4A261;'>↻ More samples needed...</span>"

        self.comparison_text.text = (
            f"<span style='color: #D4A574;'>QBP Model:</span>    P(up) = cos²(θ/2) = {predicted_up:.1f}%<br>"
            f"<span style='color: #888;'>Standard QM:</span>  P(up) = cos²(θ/2) = {predicted_up:.1f}%<br>"
            f"<span style='color: #FFFEF0;'>Measured:</span>     P(up) = {pct_up:.1f}%<br>"
            f"{status}"
        )

    def create_particle(self):
        """Create a new particle at the source and measure it."""
        # Create visual sphere
        sphere_obj = sphere(
            pos=vector(-3.5, 0, 0),
            radius=0.18,
            color=COLORS.GOLD.vpython,
            emissive=True,
        )

        # Measure using QBP framework
        theta = np.radians(self.angle_slider.value)
        state_vector = [np.sin(theta), 0, np.cos(theta)]
        psi = qphysics.create_state_from_vector(state_vector)
        result, _ = qphysics.measure(psi, qphysics.SPIN_Z)  # Unpack tuple (outcome, collapsed_state)

        # Create particle object with animation state
        particle = Particle(sphere_obj, result)
        self.active_particles.append(particle)

        # Update counts immediately (we know the result)
        if result == 1:
            self.up_count += 1
        else:
            self.down_count += 1
        self.particle_count += 1

        return particle

    def run(self):
        """Main animation loop."""
        print("\n" + "=" * 50)
        print("  ⚙  STERN-GERLACH INTERACTIVE DEMO  ⚙")
        print("=" * 50)
        print("\nOpening browser window...")
        print("Click 'Start Experiment' to begin.")
        print("Press Ctrl+C to exit.\n")

        frame_count = 0
        last_particle_frame = 0

        while True:
            rate(60)  # 60 FPS
            frame_count += 1

            # Spawn new particles based on rate slider
            if self.running:
                # Convert particles/second to frames between particles
                particles_per_second = self.speed_slider.value
                frames_between = max(2, int(60 / particles_per_second))

                if frame_count - last_particle_frame >= frames_between:
                    self.create_particle()
                    self.update_displays()
                    last_particle_frame = frame_count

            # Update all active particles (non-blocking animation)
            still_active = []
            for particle in self.active_particles:
                if particle.update():
                    still_active.append(particle)
            self.active_particles = still_active


def main():
    """Entry point for the Stern-Gerlach demo."""
    demo = SternGerlachDemo()
    demo.run()


if __name__ == "__main__":
    main()
