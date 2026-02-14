#!/usr/bin/env python3
# analysis/03_double_slit/double_slit_viz.py
"""
Interactive Double-Slit Visualization (VPython)

Explore interference patterns across three scenarios:
  A — Complex baseline (Fraunhofer): full interference fringes
  B — Which-path detection: no interference, diffraction envelope only
  C — Quaternionic (BPM): interference modulated by U1 gauge coupling

Controls:
  Scenario buttons (A / B / C) toggle the displayed pattern.
  U1 slider and eta0 buttons (active for Scenario C only) sweep the
  quaternionic parameter space — 6 U1 values x 3 eta0 values = 18 runs.

Two stacked graphs:
  Top  — "Intensity Profile": I(x) for the selected scenario/params.
         Scenario A reference shown as a faint overlay when viewing B or C.
  Bottom — "Difference Engine": I_A(x) - I_current(x) residuals.
         Zero when viewing Scenario A; shows decoherence signature otherwise.

Design principles (Dev Team):
  Bret Victor  — Make it explorable; discover physics by interacting.
  Tufte        — Maximum data-ink ratio; no decorative elements.
  Rich Harris  — Smooth, reactive updates; slider changes feel instant.
  Papert       — Learning by building; toggle/slider teaches interference.

Run: python3 analysis/03_double_slit/double_slit_viz.py
"""

import os
import sys
import glob

import numpy as np
import pandas as pd

# ---------------------------------------------------------------------------
# Project root on sys.path
# ---------------------------------------------------------------------------
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from vpython import graph, gcurve, button, slider, wtext, menu, rate, vector

from src.viz.theme import COLORS, PALETTE, TEXT
from src.simulation.analytical_double_slit import fringe_visibility

# ---------------------------------------------------------------------------
# Color contract
# ---------------------------------------------------------------------------
SCENARIO_COLORS = {
    "A": COLORS.TEAL,  # Complex baseline  — #2A9D8F
    "B": COLORS.BRASS,  # Which-path        — #D4A574
    "C": COLORS.SAGE,  # Quaternionic      — #3D8B6E
}
REF_COLOR = COLORS.STEEL  # Reference overlay — #71797E

# Available parameter values for Scenario C
U1_VALUES = [0.0, 0.5, 1.0, 2.0, 5.0, 10.0]
ETA0_VALUES = [0.01, 0.1, 0.5]


def to_vpython_color(c):
    """Convert a theme Color to a VPython vector."""
    r, g, b = c.rgb_norm
    return vector(r, g, b)


def snap_to_nearest(value, allowed):
    """Snap a continuous slider value to the nearest allowed discrete value."""
    return min(allowed, key=lambda v: abs(v - value))


# ============================================================================
# Data Loading
# ============================================================================

DATA_DIR = os.path.join(os.path.dirname(__file__), "../../results/03_double_slit")


def load_latest_data():
    """
    Load the most recent fringe_data and summary CSVs.

    Returns (fringe_df, summary_df, timestamp).
    """
    fringe_files = sorted(glob.glob(os.path.join(DATA_DIR, "fringe_data_*.csv")))
    if not fringe_files:
        print("ERROR: No fringe_data CSV found in", DATA_DIR)
        print("Run the Phase 2 simulation first to generate data.")
        sys.exit(1)

    latest_fringe = fringe_files[-1]
    timestamp = (
        os.path.basename(latest_fringe).replace("fringe_data_", "").replace(".csv", "")
    )

    summary_path = os.path.join(DATA_DIR, f"summary_{timestamp}.csv")

    fringe_df = pd.read_csv(latest_fringe)
    summary_df = pd.read_csv(summary_path) if os.path.exists(summary_path) else None

    return fringe_df, summary_df, timestamp


# ============================================================================
# Main Demo Class
# ============================================================================


class DoubleSitDemo:
    """Interactive double-slit interference explorer."""

    def __init__(self):
        self.current_scenario = "A"
        self.current_u1 = 0.0
        self.current_eta0 = 0.01

        self.load_data()
        self.setup_graphs()
        self.setup_controls()
        self.setup_stats()
        self.update_display()

    # ------------------------------------------------------------------ data
    def load_data(self):
        """Load and preprocess all fringe data into lookup dictionaries."""
        fringe_df, summary_df, timestamp = load_latest_data()
        self.timestamp = timestamp

        # --- Scenario A (SI metres) ---
        df_a = fringe_df[fringe_df["scenario"] == "A"]
        x_a = df_a["x_position"].values
        x_norm_a = x_a / np.max(np.abs(x_a)) if np.max(np.abs(x_a)) > 0 else x_a
        self.data_a = {"x": x_norm_a, "I": df_a["intensity_total"].values}

        # --- Scenario B (SI metres) ---
        df_b = fringe_df[fringe_df["scenario"] == "B"]
        x_b = df_b["x_position"].values
        x_norm_b = x_b / np.max(np.abs(x_b)) if np.max(np.abs(x_b)) > 0 else x_b
        self.data_b = {"x": x_norm_b, "I": df_b["intensity_total"].values}

        # --- Scenario C (natural units) — indexed by (U1, eta0) ---
        self.data_c = {}
        fringe_c = fringe_df[fringe_df["scenario"] == "C"]
        for (u1, eta0), group in fringe_c.groupby(["U1_strength", "eta0"]):
            group = group.sort_values("x_position")
            x_c = group["x_position"].values
            x_max = np.max(np.abs(x_c))
            x_norm = x_c / x_max if x_max > 0 else x_c
            self.data_c[(u1, eta0)] = {
                "x": x_norm,
                "I": group["intensity_total"].values,
            }

        # --- Summary (visibility table) ---
        self.summary = {}
        if summary_df is not None:
            for _, row in summary_df.iterrows():
                key = (row["scenario"], row["U1_strength"], row["eta0"])
                self.summary[key] = {
                    "visibility": row["visibility"],
                    "norm_final": row.get("norm_final", np.nan),
                }

        # Reference visibility for V_norm (Scenario C at U1=0 per eta0)
        self.v_ref = {}
        for eta0 in ETA0_VALUES:
            key = ("C", 0.0, eta0)
            if key in self.summary:
                self.v_ref[eta0] = self.summary[key]["visibility"]
            else:
                self.v_ref[eta0] = 1.0  # fallback

    # -------------------------------------------------------------- graphs
    def setup_graphs(self):
        """Create the two stacked VPython graph panels."""
        # Top panel: intensity profile
        self.g_intensity = graph(
            title="<b>Intensity Profile</b>",
            xtitle="Normalized position",
            ytitle="Intensity (a.u.)",
            width=800,
            height=300,
            fast=False,
        )
        # Placeholder curves (will be recreated on each update)
        self.curve_ref = None
        self.curve_main = None

        # Bottom panel: difference engine
        self.g_diff = graph(
            title="<b>Difference Engine: I<sub>A</sub>(x) \u2212 I(x)</b>",
            xtitle="Normalized position",
            ytitle="Residual",
            width=800,
            height=250,
            fast=False,
        )
        self.curve_diff = None

    # ------------------------------------------------------------ controls
    def setup_controls(self):
        """Create scenario buttons, U1 slider, eta0 buttons."""
        # --- Scenario selector ---
        self.g_intensity.append_to_caption(
            f"\n<div style='padding: 10px 0;'>"
            f"<span style='color: {TEXT.LIGHT.PRIMARY.hex}; "
            f"font-family: Georgia; font-size: 14px;'>"
            f"<b style='color: {COLORS.COPPER.hex};'>Scenario:</b> </span>"
        )

        self.btn_a = button(
            text="A  Complex",
            bind=self._select_a,
        )
        self.g_intensity.append_to_caption(" ")
        self.btn_b = button(
            text="B  Which-path",
            bind=self._select_b,
        )
        self.g_intensity.append_to_caption(" ")
        self.btn_c = button(
            text="C  Quaternionic",
            bind=self._select_c,
        )
        self.g_intensity.append_to_caption("</div>")

        # --- U1 slider (Scenario C only) ---
        self.g_intensity.append_to_caption(
            f"\n<div style='padding: 5px 0;'>"
            f"<span style='color: {TEXT.LIGHT.PRIMARY.hex}; "
            f"font-family: Georgia; font-size: 14px;'>"
            f"<b style='color: {COLORS.COPPER.hex};'>"
            f"U<sub>1</sub> strength:</b> </span>"
        )
        self.u1_slider = slider(
            min=0,
            max=10,
            value=0,
            step=0.5,
            bind=self._update_u1,
            length=350,
        )
        self.u1_text = wtext(text=f" <b style='color: {COLORS.COPPER.hex};'>0.0</b>")
        self.g_intensity.append_to_caption("</div>")

        # --- eta0 selector ---
        self.g_intensity.append_to_caption(
            f"\n<div style='padding: 5px 0;'>"
            f"<span style='color: {TEXT.LIGHT.PRIMARY.hex}; "
            f"font-family: Georgia; font-size: 14px;'>"
            f"<b style='color: {COLORS.COPPER.hex};'>"
            f"\u03b7<sub>0</sub>:</b> </span>"
        )
        for eta0 in ETA0_VALUES:
            button(
                text=str(eta0),
                bind=lambda b, e=eta0: self._set_eta0(e),
            )
            self.g_intensity.append_to_caption(" ")
        self.g_intensity.append_to_caption("</div>")

    # --------------------------------------------------------------- stats
    def setup_stats(self):
        """Create the statistics text display below the difference graph."""
        self.g_diff.append_to_caption(
            f"\n<div style='padding: 10px 0; font-family: Georgia; "
            f"font-size: 14px; color: {TEXT.LIGHT.PRIMARY.hex};'>"
        )
        self.stats_text = wtext(text="")
        self.g_diff.append_to_caption("</div>")

    # ------------------------------------------------------- event handlers
    def _select_a(self, b):
        self.current_scenario = "A"
        self.update_display()

    def _select_b(self, b):
        self.current_scenario = "B"
        self.update_display()

    def _select_c(self, b):
        self.current_scenario = "C"
        self.update_display()

    def _update_u1(self, s):
        self.current_u1 = snap_to_nearest(s.value, U1_VALUES)
        self.u1_text.text = (
            f" <b style='color: {COLORS.COPPER.hex};'>{self.current_u1}</b>"
        )
        if self.current_scenario == "C":
            self.update_display()

    def _set_eta0(self, eta0):
        self.current_eta0 = eta0
        if self.current_scenario == "C":
            self.update_display()

    # ------------------------------------------------------ display update
    def _get_current_data(self):
        """Return (x, I) arrays for the current scenario and parameters."""
        if self.current_scenario == "A":
            return self.data_a["x"], self.data_a["I"]
        elif self.current_scenario == "B":
            return self.data_b["x"], self.data_b["I"]
        else:
            key = (self.current_u1, self.current_eta0)
            if key in self.data_c:
                return self.data_c[key]["x"], self.data_c[key]["I"]
            # Fallback: snap to nearest available
            fallback_key = min(
                self.data_c.keys(),
                key=lambda k: abs(k[0] - self.current_u1)
                + abs(k[1] - self.current_eta0),
            )
            return self.data_c[fallback_key]["x"], self.data_c[fallback_key]["I"]

    def _compute_residuals(self, x_cur, I_cur):
        """Compute I_A(x) - I_current(x) on a common grid.

        Since Scenarios A/B share the same grid and Scenario C has a
        different grid, we interpolate Scenario A onto the current grid
        when coordinate systems differ.
        """
        x_a = self.data_a["x"]
        I_a = self.data_a["I"]

        if self.current_scenario == "A":
            return x_cur, np.zeros_like(I_cur)

        # Interpolate A onto current grid (both already normalised to [-1,1])
        I_a_interp = np.interp(x_cur, x_a, I_a)
        residuals = I_a_interp - I_cur
        return x_cur, residuals

    def _lookup_visibility(self):
        """Return (V, V_norm) for current selection, or compute from data."""
        sc = self.current_scenario
        u1 = self.current_u1 if sc == "C" else 0.0
        eta0 = self.current_eta0 if sc == "C" else 0.0

        key = (sc, u1, eta0)
        if key in self.summary:
            v = self.summary[key]["visibility"]
        else:
            _, I_cur = self._get_current_data()
            v = fringe_visibility(I_cur)

        # V_norm: normalise by Scenario C at U1=0 with same eta0
        if sc == "C":
            v_ref = self.v_ref.get(eta0, 1.0)
            v_norm = v / v_ref if v_ref > 0 else 0.0
        else:
            v_norm = 1.0  # A and B are their own references

        return v, v_norm

    def update_display(self):
        """Redraw all curves and stats for the current selection."""
        x_cur, I_cur = self._get_current_data()
        x_res, residuals = self._compute_residuals(x_cur, I_cur)

        sc_color = to_vpython_color(SCENARIO_COLORS[self.current_scenario])
        ref_col = to_vpython_color(REF_COLOR)
        diff_col = to_vpython_color(COLORS.TERRACOTTA)

        # ---- Intensity graph ----
        # Delete old curves
        if self.curve_ref is not None:
            self.curve_ref.delete()
            self.curve_ref = None
        if self.curve_main is not None:
            self.curve_main.delete()
            self.curve_main = None

        # Reference (Scenario A) as faint overlay when not viewing A
        if self.current_scenario != "A":
            self.curve_ref = gcurve(
                graph=self.g_intensity,
                color=ref_col,
                label="Scenario A ref",
            )
            x_a = self.data_a["x"]
            I_a = self.data_a["I"]
            # Downsample reference to keep it fast (every 4th point)
            step_ref = max(1, len(x_a) // 2000)
            for i in range(0, len(x_a), step_ref):
                self.curve_ref.plot(x_a[i], I_a[i])

        # Main curve
        label_map = {
            "A": "A: Complex baseline",
            "B": "B: Which-path",
            "C": f"C: U\u2081={self.current_u1}, \u03b7\u2080={self.current_eta0}",
        }
        self.curve_main = gcurve(
            graph=self.g_intensity,
            color=sc_color,
            label=label_map[self.current_scenario],
        )
        step_main = max(1, len(x_cur) // 2500)
        for i in range(0, len(x_cur), step_main):
            self.curve_main.plot(x_cur[i], I_cur[i])

        # ---- Difference graph ----
        if self.curve_diff is not None:
            self.curve_diff.delete()
            self.curve_diff = None

        self.curve_diff = gcurve(
            graph=self.g_diff,
            color=diff_col,
            label=f"I_A \u2212 I_{self.current_scenario}",
        )
        step_diff = max(1, len(x_res) // 2500)
        for i in range(0, len(x_res), step_diff):
            self.curve_diff.plot(x_res[i], residuals[i])

        # ---- Stats ----
        v, v_norm = self._lookup_visibility()
        max_res = float(np.max(np.abs(residuals)))

        param_str = ""
        if self.current_scenario == "C":
            param_str = (
                f" | U<sub>1</sub> = {self.current_u1} "
                f"| \u03b7<sub>0</sub> = {self.current_eta0}"
            )

        self.stats_text.text = (
            f"<b style='color: {COLORS.COPPER.hex};'>Scenario:</b> "
            f"<span style='color: {SCENARIO_COLORS[self.current_scenario].hex};'>"
            f"<b>{self.current_scenario}</b></span>"
            f"{param_str}"
            f"&nbsp;&nbsp;&nbsp;&nbsp;"
            f"<b style='color: {COLORS.COPPER.hex};'>V:</b> {v:.4f}"
            f"&nbsp;&nbsp;"
            f"<b style='color: {COLORS.COPPER.hex};'>V<sub>norm</sub>:</b> {v_norm:.4f}"
            f"&nbsp;&nbsp;"
            f"<b style='color: {COLORS.COPPER.hex};'>max |residual|:</b> {max_res:.4f}"
        )

    # ----------------------------------------------------------------- run
    def run(self):
        """Main event loop."""
        print()
        print("=" * 62)
        print("  Double-Slit Interference Explorer")
        print("  Sprint 3 Phase 3 -- QBP Project")
        print("=" * 62)
        print()
        print(f"  Data timestamp: {self.timestamp}")
        print(f"  Scenario A: {len(self.data_a['x']):,} points (complex baseline)")
        print(f"  Scenario B: {len(self.data_b['x']):,} points (which-path)")
        print(f"  Scenario C: {len(self.data_c)} parameter runs (quaternionic)")
        print()
        print("  Opening browser window...")
        print("  Use buttons and slider to explore interference patterns.")
        print("  Press Ctrl+C to exit.")
        print()

        while True:
            rate(30)


# ============================================================================
# Entry point
# ============================================================================


def main():
    """Entry point for the double-slit visualization demo."""
    demo = DoubleSitDemo()
    demo.run()


if __name__ == "__main__":
    main()
