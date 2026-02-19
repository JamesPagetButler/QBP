#!/usr/bin/env python3
# analysis/03_double_slit/double_slit_viz.py
"""
Interactive Double-Slit Visualization (VPython) — 6-Panel Explorer

Presents three perspectives on the double-slit experiment:
  1. Adler's predicted exponential η-decay (which does NOT happen)
  2. Standard QM — flat η, full coherence at U₁=0
  3. QBP BPM — discrete step-change in η at the coupling region

Six graph panels:
  1a — "Adler Prediction vs Reality": full-scale η(z)
  1b — "Zoomed: Step-Change at Coupling Region": Δη(z) detail
  2  — "Visibility vs Coupling Strength": V vs U₁ scatter
  3  — "Near-Field BPM Fringe Pattern": I(x) in nm (full)
  4  — "Zoomed: Individual Interference Fringes": ~12 fringes at center
  5  — "Far-Field Comparison": Standard QM vs QBP (mm scale, actual BPM+FFT)

Controls: U₁ slider, η₀ buttons, live stats.

Design principles (Dev Team):
  Bret Victor  — Make it explorable; discover physics by interacting.
  Tufte        — Maximum data-ink ratio; no decorative elements.
  Rich Harris  — Smooth, reactive updates; slider changes feel instant.
  Papert       — Learning by building; toggle/slider teaches interference.

Run: python3 /home/prime/Documents/QBP/analysis/03_double_slit/double_slit_viz.py
"""

import json
import os
import sys
import glob

import numpy as np
import pandas as pd

# ---------------------------------------------------------------------------
# Project root on sys.path
# ---------------------------------------------------------------------------
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from vpython import (
    canvas,
    graph,
    gcurve,
    button,
    slider,
    wtext,
    rate,
    vector,
)

from src.viz.theme import COLORS, TEXT

# ---------------------------------------------------------------------------
# Color contract
# ---------------------------------------------------------------------------
COL_ADLER = COLORS.BRASS  # #D4A574 — Adler prediction
COL_STD_QM = COLORS.STEEL  # #71797E — Standard QM (U₁=0 control)
COL_EXPECTED = COLORS.CRIMSON  # #9B2335 — Expected/baseline (red = expected)
COL_QBP = COLORS.TEAL  # #2A9D8F — QBP coupling result (teal = QBP)
COL_AMBER = COLORS.AMBER  # #F4A261 — Coupling region shade
COL_GOLD = COLORS.GOLD  # #FFD700 — Current-selection highlight


def to_vpy(c):
    """Convert a theme Color to a VPython vector."""
    r, g, b = c.rgb_norm
    return vector(r, g, b)


def snap_to_nearest(value, allowed):
    """Snap a continuous slider value to the nearest allowed discrete value."""
    return min(allowed, key=lambda v: abs(v - value))


def _clear_curves(curve_list):
    """Blank out all gcurves in *curve_list*, then return an empty list.

    VPython's ``gcurve.delete()`` does NOT reliably remove curves from
    the rendered graph — it can also corrupt graph state for new curves.
    Instead we blank the data and hide the object.  The empty gcurve
    objects accumulate harmlessly in memory.
    """
    for c in curve_list:
        try:
            c.data = []  # Remove all plotted points
        except Exception:
            pass
        try:
            c.visible = False
        except Exception:
            pass
        # NOTE: do NOT call c.delete() — it corrupts the graph and
        # prevents new curves from rendering on the same graph.
    return []


# ============================================================================
# Data Loading
# ============================================================================

DATA_DIR = os.path.join(os.path.dirname(__file__), "../../results/03_double_slit")
V3_DIR = os.path.join(DATA_DIR, "v3")


def load_latest_data():
    """Load the most recent simulation data.

    Tries v3 format first (``results/03_double_slit/v3/``), then falls
    back to the legacy v2 format in the parent directory.

    Returns ``(decay_df, nearfield_df, farfield_df, farfield_qbp_df, summary_df, metadata, timestamp)``.

    For v3 format, ``nearfield_df`` contains BPM data with a ``regime``
    column (``"expected"`` or ``"qbp"``), ``farfield_df`` contains
    analytical scenarios A/B, and ``farfield_qbp_df`` contains BPM+FFT
    far-field predictions.  For legacy format, ``nearfield_df`` holds
    all fringe data (scenarios A+B+C) and ``farfield_df`` is ``None``.
    """
    # --- Try v3 format first ---
    v3_nearfield = sorted(glob.glob(os.path.join(V3_DIR, "results_nearfield_*.csv")))
    if v3_nearfield:
        latest = v3_nearfield[-1]
        timestamp = (
            os.path.basename(latest)
            .replace("results_nearfield_", "")
            .replace(".csv", "")
        )
        nearfield_df = pd.read_csv(latest)

        farfield_path = os.path.join(V3_DIR, f"results_farfield_{timestamp}.csv")
        farfield_df = (
            pd.read_csv(farfield_path) if os.path.exists(farfield_path) else None
        )

        farfield_qbp_path = os.path.join(
            V3_DIR, f"results_farfield_qbp_{timestamp}.csv"
        )
        farfield_qbp_df = (
            pd.read_csv(farfield_qbp_path)
            if os.path.exists(farfield_qbp_path)
            else None
        )

        decay_path = os.path.join(V3_DIR, f"decay_{timestamp}.csv")
        decay_df = pd.read_csv(decay_path) if os.path.exists(decay_path) else None

        summary_path = os.path.join(V3_DIR, f"summary_{timestamp}.csv")
        summary_df = pd.read_csv(summary_path) if os.path.exists(summary_path) else None

        metadata_path = os.path.join(V3_DIR, f"metadata_{timestamp}.json")
        metadata = {}
        if os.path.exists(metadata_path):
            with open(metadata_path) as f:
                metadata = json.load(f)

        print(f"Loaded v3 data (timestamp {timestamp})")
        if farfield_qbp_df is not None:
            print(f"  Far-field QBP: {len(farfield_qbp_df)} rows")
        return (
            decay_df,
            nearfield_df,
            farfield_df,
            farfield_qbp_df,
            summary_df,
            metadata,
            timestamp,
        )

    # --- Fall back to legacy v2 format ---
    decay_files = sorted(glob.glob(os.path.join(DATA_DIR, "decay_data_*.csv")))
    if not decay_files:
        print("ERROR: No simulation data found in", DATA_DIR)
        print("Run the Phase 2 simulation first to generate data.")
        sys.exit(1)

    latest_decay = decay_files[-1]
    timestamp = (
        os.path.basename(latest_decay).replace("decay_data_", "").replace(".csv", "")
    )

    fringe_path = os.path.join(DATA_DIR, f"fringe_data_{timestamp}.csv")
    summary_path = os.path.join(DATA_DIR, f"summary_{timestamp}.csv")
    metadata_path = os.path.join(DATA_DIR, f"metadata_{timestamp}.json")

    decay_df = pd.read_csv(latest_decay)
    nearfield_df = pd.read_csv(fringe_path) if os.path.exists(fringe_path) else None
    summary_df = pd.read_csv(summary_path) if os.path.exists(summary_path) else None

    metadata = {}
    if os.path.exists(metadata_path):
        with open(metadata_path) as f:
            metadata = json.load(f)

    print(f"Loaded legacy v2 data (timestamp {timestamp})")
    return decay_df, nearfield_df, None, None, summary_df, metadata, timestamp


# ============================================================================
# Main Demo Class
# ============================================================================


class DoubleSlitDemo:
    """Interactive 6-panel double-slit explorer."""

    def __init__(self):
        self.current_u1 = 0.0
        self.current_eta0 = 0.5

        self.load_data()
        self.setup_controls()
        self.setup_graphs()
        self.update_all()

    # ------------------------------------------------------------------ data
    def load_data(self):
        """Load and index all data into lookup dictionaries.

        Supports both v3 format (regime column, separate nearfield/farfield)
        and legacy v2 format (scenario column, single fringe_data CSV).
        """
        (
            decay_df,
            nearfield_df,
            farfield_df,
            farfield_qbp_df,
            summary_df,
            metadata,
            timestamp,
        ) = load_latest_data()
        self.timestamp = timestamp
        self.metadata = metadata
        self.is_v3 = farfield_df is not None  # v3 provides a separate farfield df

        # Physical constants for Adler κ
        self.hbar = 1.0546e-34  # J·s
        self.e_charge = 1.602e-19  # J/eV
        self.v_z = metadata.get("v_z_si_m_per_s", 14547790.0)

        # Discover available U₁ and η₀ values
        self.u1_values = sorted(decay_df["U1_strength_eV"].unique())
        self.eta0_values = sorted(decay_df["eta0"].unique())

        # --- Decay data: (u1, eta0) → (z_nm, eta) ---
        self.decay = {}
        for (u1, eta0), grp in decay_df.groupby(["U1_strength_eV", "eta0"]):
            grp = grp.sort_values("z_m")
            z_nm = grp["z_m"].values * 1e9  # metres → nm
            eta = grp["eta_fraction"].values
            self.decay[(u1, eta0)] = (z_nm, eta)

        # --- Summary: keyed by ("C", u1, eta0) for backward compat ---
        self.summary = {}
        if summary_df is not None:
            for _, row in summary_df.iterrows():
                if self.is_v3:
                    regime = row["regime"]
                    # Map v3 regimes to legacy scenario keys for panel lookups
                    if regime in ("expected", "qbp"):
                        key = ("C", row["U1_strength_eV"], row["eta0"])
                    elif regime == "farfield_A":
                        key = ("A", 0.0, 0.0)
                    elif regime == "farfield_B":
                        key = ("B", 0.0, 0.0)
                    else:
                        continue
                else:
                    key = (row["scenario"], row["U1_strength_eV"], row["eta0"])
                self.summary[key] = {
                    "visibility": row["visibility"],
                    "norm_final": row.get("norm_final", np.nan),
                }

        # --- Fringe data (BPM near-field): (u1, eta0) → (x_nm, I) ---
        self.fringe = {}
        if nearfield_df is not None:
            if self.is_v3:
                # v3: filter by regime, all rows are BPM
                for (u1, eta0), grp in nearfield_df.groupby(["U1_strength_eV", "eta0"]):
                    grp = grp.sort_values("x_position_m")
                    x_nm = grp["x_position_m"].values * 1e9
                    I_tot = grp["intensity_total_normalized"].values
                    self.fringe[(u1, eta0)] = (x_nm, I_tot)
            else:
                # Legacy: filter scenario == "C"
                fringe_c = nearfield_df[nearfield_df["scenario"] == "C"]
                for (u1, eta0), grp in fringe_c.groupby(["U1_strength_eV", "eta0"]):
                    grp = grp.sort_values("x_position_m")
                    x_nm = grp["x_position_m"].values * 1e9
                    I_tot = grp["intensity_total_normalized"].values
                    self.fringe[(u1, eta0)] = (x_nm, I_tot)

        # --- Far-field data (Scenarios A and B): x in mm, I normalized ---
        self.farfield_a = None
        self.farfield_b = None
        if self.is_v3 and farfield_df is not None:
            df_a = farfield_df[farfield_df["scenario"] == "A"].sort_values(
                "x_position_m"
            )
            if len(df_a) > 0:
                self.farfield_a = (
                    df_a["x_position_m"].values * 1e3,
                    df_a["intensity_total_normalized"].values,
                )
            df_b = farfield_df[farfield_df["scenario"] == "B"].sort_values(
                "x_position_m"
            )
            if len(df_b) > 0:
                self.farfield_b = (
                    df_b["x_position_m"].values * 1e3,
                    df_b["intensity_total_normalized"].values,
                )
        elif nearfield_df is not None:
            # Legacy: A/B in the same fringe CSV
            df_a = nearfield_df[nearfield_df["scenario"] == "A"].sort_values(
                "x_position_m"
            )
            if len(df_a) > 0:
                self.farfield_a = (
                    df_a["x_position_m"].values * 1e3,
                    df_a["intensity_total_normalized"].values,
                )
            df_b = nearfield_df[nearfield_df["scenario"] == "B"].sort_values(
                "x_position_m"
            )
            if len(df_b) > 0:
                self.farfield_b = (
                    df_b["x_position_m"].values * 1e3,
                    df_b["intensity_total_normalized"].values,
                )

        # --- Far-field QBP data: (u1, eta0) → (x_mm, I_norm) ---
        self.farfield_qbp = {}
        if farfield_qbp_df is not None:
            for regime in ("expected", "qbp"):
                sub = farfield_qbp_df[farfield_qbp_df["regime"] == regime]
                for (u1, eta0), grp in sub.groupby(["U1_strength_eV", "eta0"]):
                    grp = grp.sort_values("x_position_m")
                    x_mm = grp["x_position_m"].values * 1e3
                    I_tot = grp["intensity_total_normalized"].values
                    self.farfield_qbp[(regime, u1, eta0)] = (x_mm, I_tot)
            print(f"  Far-field QBP indexed: {len(self.farfield_qbp)} curves")

        # Baseline visibility per η₀ (U₁=0)
        self.v_baseline = {}
        for eta0 in self.eta0_values:
            key = ("C", 0.0, eta0)
            if key in self.summary:
                self.v_baseline[eta0] = self.summary[key]["visibility"]

        # Set defaults
        self.current_u1 = self.u1_values[0]
        self.current_eta0 = self.eta0_values[-1]  # 0.5

    # -------------------------------------------------------- Adler prediction
    def adler_eta(self, z_nm, u1_eV, eta0):
        """Compute Adler's predicted η(z) = η₀ · exp(-2κz).

        κ = U₁(eV) · e / (ℏ · v_z)  in m⁻¹
        """
        if u1_eV <= 0:
            return np.full_like(z_nm, eta0)
        kappa = u1_eV * self.e_charge / (self.hbar * self.v_z)  # m⁻¹
        z_m = z_nm * 1e-9
        return eta0 * np.exp(-2 * kappa * z_m)

    def adler_decay_length_nm(self, u1_eV):
        """Distance in nm at which Adler predicts η drops to 1/e²."""
        if u1_eV <= 0:
            return float("inf")
        kappa = u1_eV * self.e_charge / (self.hbar * self.v_z)
        return 1.0 / kappa * 1e9  # metres → nm

    # ------------------------------------------------------------- controls
    def setup_controls(self):
        """Create the control canvas with title, slider, buttons, stats."""
        self.ctrl = canvas(
            title=(
                '<div style="font-family: Georgia, serif; padding: 8px 0;">'
                '<b style="font-size: 20px;">Double-Slit: Three Predictions Compared</b>'
                '<br><span style="font-size: 14px; color: #71797E;">'
                "Adler predicted exponential decay. Standard QM predicts nothing. "
                "The BPM shows a discrete step.</span></div>"
            ),
            width=1,
            height=1,
        )
        self.ctrl.visible = False

        # --- U₁ slider ---
        u1_max = max(self.u1_values)
        self.ctrl.append_to_caption(
            f"<div style='padding: 8px 0; font-family: Georgia;'>"
            f"<b style='color: {COLORS.COPPER.hex};'>"
            f"U<sub>1</sub> coupling (eV):</b> "
        )
        self.u1_slider = slider(
            min=0,
            max=u1_max,
            value=0,
            step=u1_max / 100,
            bind=self._on_u1_change,
            length=400,
        )
        self.u1_text = wtext(text=f" <b style='color: {COLORS.COPPER.hex};'>0.0 eV</b>")
        self.ctrl.append_to_caption("</div>")

        # --- η₀ buttons ---
        self.ctrl.append_to_caption(
            f"<div style='padding: 5px 0; font-family: Georgia;'>"
            f"<b style='color: {COLORS.COPPER.hex};'>"
            f"\u03b7<sub>0</sub> (quaternionic fraction):</b> "
        )
        for eta0 in self.eta0_values:
            button(
                text=str(eta0),
                bind=lambda b, e=eta0: self._on_eta0_change(e),
            )
            self.ctrl.append_to_caption(" ")
        self.ctrl.append_to_caption("</div>")

        # --- Stats display ---
        self.ctrl.append_to_caption(
            "<div style='padding: 6px 0; font-family: monospace; font-size: 13px;'>"
        )
        self.stats_wtext = wtext(text="")
        self.ctrl.append_to_caption("</div>")

        # --- Physics explanation ---
        self.ctrl.append_to_caption(
            f"<div style='border-left: 3px solid {COLORS.COPPER.hex}; "
            f"padding: 6px 0 6px 12px; margin: 8px 0; "
            f"font-family: Georgia; font-size: 13px; "
            f"color: {TEXT.LIGHT.SECONDARY.hex};'>"
            "Adler's theory predicted exponential decay of \u03b7. "
            "The BPM instead shows a discrete step-change &mdash; the SO(4) "
            "rotation is unitary, not dissipative."
            "</div>\n"
        )

    # ------------------------------------------------------------- graphs
    def setup_graphs(self):
        """Create the four graph panels."""

        # z range for decay panels
        z_key = (self.u1_values[0], self.eta0_values[0])
        z_arr = self.decay[z_key][0]
        self.z_max = z_arr[-1]

        # --- Panel 1a: Full-scale η(z) ---
        self.g1a = graph(
            title=(
                "<b>P1 &mdash; Adler Prediction vs Reality</b>"
                " &mdash; <i>the predicted exponential decay does NOT happen</i>"
            ),
            xtitle="z (nm)",
            ytitle="\u03b7(z)",
            width=900,
            height=380,
            fast=False,
        )
        self.curves_1a = []

        # --- Panel 1b: Zoomed Δη(z) ---
        self.g1b = graph(
            title=(
                "<b>P2 &mdash; Zoomed: Step-Change at Coupling Region</b>"
                " &mdash; <i>the only change is a discrete step</i>"
            ),
            xtitle="z (nm)",
            ytitle="\u0394\u03b7 = \u03b7(z) \u2212 \u03b7\u2080",
            width=900,
            height=330,
            fast=False,
        )
        self.curves_1b = []

        # --- Panel 2: Visibility vs U₁ ---
        self.g2 = graph(
            title=(
                "<b>P3 &mdash; Visibility vs Coupling Strength</b>"
                " &mdash; <i>visibility drops ~8% as coupling increases</i>"
            ),
            xtitle="U\u2081 (eV)",
            ytitle="Fringe Visibility V",
            width=900,
            height=280,
            fast=False,
        )
        self._plot_panel2_static()
        self.curves_2_dynamic = []

        # --- Panel 3: Near-field fringe ---
        self.g3 = graph(
            title=(
                "<b>P4 &mdash; Near-Field BPM Fringe Pattern</b>"
                " &mdash; <i>near-field (nm scale); far-field patterns (mm) "
                "are NOT shown to avoid misleading comparison</i>"
            ),
            xtitle="x (nm)",
            ytitle="I(x) normalized",
            width=900,
            height=280,
            fast=False,
        )
        self.curves_3 = []

        # --- Panel 4: Zoomed near-field fringes ---
        self.g4 = graph(
            title=(
                "<b>P5 &mdash; Zoomed: Individual Interference Fringes</b>"
                " &mdash; <i>constructive/destructive peaks clearly resolved</i>"
            ),
            xtitle="x (nm)",
            ytitle="I(x) normalized",
            width=900,
            height=300,
            fast=False,
        )
        self.curves_4 = []

        # --- Panel 5: Far-field comparison (A vs QBP) ---
        has_qbp_ff = len(self.farfield_qbp) > 0
        panel5_title = (
            "<b>P6 &mdash; Far-Field QBP: Expected vs Quaternionic Coupling</b>"
            " &mdash; <i>BPM + Fraunhofer FFT (mm scale)</i>"
            if has_qbp_ff
            else "<b>P6 &mdash; Far-Field Reference: Standard QM vs Which-Path</b>"
            " &mdash; <i>classic mm-scale Fraunhofer diffraction</i>"
        )
        self.g5 = graph(
            title=panel5_title,
            xtitle="x (mm)",
            ytitle="I(x) normalized",
            width=900,
            height=300,
            fast=False,
        )
        self._plot_panel5_static()

    # -------------------------------------------------- Panel 2 static parts
    def _plot_panel2_static(self):
        """Plot static elements on Panel 2 (plotted once, never redrawn).

        Three perspectives:
          a. Expected (Adler): V→0 (which-path, complete decoherence)
          b. Standard QM: V=1 (full interference)
          c. QBP BPM: V≈0.55→0.51 (partial, declining with U₁)

        Reference points plotted as short dashes at left edge to anchor
        the scale without crushing the data.
        """
        u1_max = max(self.u1_values)
        edge = u1_max * 0.02  # short dash width

        # (a) Adler predicted: V=0 (complete decoherence)
        c_adler = gcurve(
            graph=self.g2,
            color=to_vpy(COL_ADLER),
            dot=True,
            dot_color=to_vpy(COL_ADLER),
            label="Adler predicted (V=0)",
            radius=0,
        )
        c_adler.plot(0, 0.0)
        c_adler.plot(edge, 0.0)

        # (b) Standard QM: V=1 (full coherence)
        c_qm = gcurve(
            graph=self.g2,
            color=to_vpy(COL_STD_QM),
            dot=True,
            dot_color=to_vpy(COL_STD_QM),
            label="Standard QM (V=1)",
            radius=0,
        )
        c_qm.plot(0, 1.0)
        c_qm.plot(edge, 1.0)

        # (c) QBP BPM baseline (U₁=0) — horizontal reference
        v_base = self.v_baseline.get(
            0.5, self.v_baseline.get(self.eta0_values[0], 0.55)
        )
        c_base = gcurve(
            graph=self.g2,
            color=to_vpy(COL_EXPECTED),
            label=f"QBP baseline U\u2081=0 (V={v_base:.4f})",
            dot=True,
            dot_color=to_vpy(COL_EXPECTED),
            radius=0,
        )
        c_base.plot(0, v_base)
        c_base.plot(u1_max, v_base)

        # (c) QBP BPM data points: V vs U₁
        eta0_for_scatter = self.eta0_values[-1]
        c_data = gcurve(
            graph=self.g2,
            color=to_vpy(COL_QBP),
            dot=True,
            dot_color=to_vpy(COL_QBP),
            label="QBP BPM visibility",
        )
        for u1 in self.u1_values:
            key = ("C", u1, eta0_for_scatter)
            if key in self.summary:
                c_data.plot(u1, self.summary[key]["visibility"])

    # --------------------------------------------------- event handlers
    def _on_u1_change(self, s):
        self.current_u1 = snap_to_nearest(s.value, self.u1_values)
        self.u1_text.text = (
            f" <b style='color: {COLORS.COPPER.hex};'>" f"{self.current_u1:.1f} eV</b>"
        )
        self.update_all()

    def _on_eta0_change(self, eta0):
        self.current_eta0 = eta0
        self.update_all()

    # --------------------------------------------------- master update
    def update_all(self):
        """Redraw all dynamic curves and stats."""
        self._update_panel_1a()
        self._update_panel_1b()
        self._update_panel_2()
        self._update_panel_3()
        self._update_panel_4()
        self._update_panel_5()
        self._update_stats()

    # --------------------------------------------------- Panel 1a
    def _update_panel_1a(self):
        """Full-scale η(z): Adler, Std QM, BPM."""
        self.curves_1a = _clear_curves(self.curves_1a)

        u1 = self.current_u1
        eta0 = self.current_eta0
        key = (u1, eta0)

        # Get z grid from BPM data
        z_nm, eta_bpm = self.decay.get(
            key,
            self.decay.get(
                min(self.decay.keys(), key=lambda k: abs(k[0] - u1) + abs(k[1] - eta0)),
            ),
        )

        # Adler prediction
        eta_adler = self.adler_eta(z_nm, u1, eta0)
        c_adler = gcurve(
            graph=self.g1a,
            color=to_vpy(COL_ADLER),
            dot=True,
            dot_color=to_vpy(COL_ADLER),
            label="Adler prediction",
        )
        for i in range(len(z_nm)):
            c_adler.plot(z_nm[i], eta_adler[i])
        self.curves_1a.append(c_adler)

        # Standard QM: flat at η₀ (use U₁=0 control data)
        z_ctrl, eta_ctrl = self.decay.get((0.0, eta0), (z_nm, np.full_like(z_nm, eta0)))
        c_std = gcurve(
            graph=self.g1a,
            color=to_vpy(COL_STD_QM),
            label="Standard QM (U\u2081=0)",
        )
        for i in range(len(z_ctrl)):
            c_std.plot(z_ctrl[i], eta_ctrl[i])
        self.curves_1a.append(c_std)

        # QBP BPM result
        col = COL_EXPECTED if u1 == 0.0 else COL_QBP
        c_bpm = gcurve(
            graph=self.g1a,
            color=to_vpy(col),
            label=f"QBP BPM (U\u2081={u1:.0f} eV)",
        )
        for i in range(len(z_nm)):
            c_bpm.plot(z_nm[i], eta_bpm[i])
        self.curves_1a.append(c_bpm)

    # --------------------------------------------------- Panel 1b
    def _update_panel_1b(self):
        """Zoomed Δη = η(z) − η₀, with coupling region shading."""
        self.curves_1b = _clear_curves(self.curves_1b)

        u1 = self.current_u1
        eta0 = self.current_eta0
        key = (u1, eta0)

        z_nm, eta_bpm = self.decay.get(
            key,
            self.decay.get(
                min(self.decay.keys(), key=lambda k: abs(k[0] - u1) + abs(k[1] - eta0)),
            ),
        )

        # Standard QM: Δη = 0
        c_std = gcurve(
            graph=self.g1b,
            color=to_vpy(COL_STD_QM),
            label="Standard QM (\u0394\u03b7=0)",
        )
        c_std.plot(0, 0)
        c_std.plot(self.z_max, 0)
        self.curves_1b.append(c_std)

        # BPM Δη
        delta_eta = eta_bpm - eta0
        c_bpm = gcurve(
            graph=self.g1b,
            color=to_vpy(COL_EXPECTED) if u1 == 0.0 else to_vpy(COL_QBP),
            label=f"QBP BPM \u0394\u03b7 (U\u2081={u1:.0f} eV)",
        )
        for i in range(len(z_nm)):
            c_bpm.plot(z_nm[i], delta_eta[i])
        self.curves_1b.append(c_bpm)

        # Coupling region band (z ≈ 7.2–8.8 nm) — draw as two thin vertical lines
        # VPython graphs don't support shaded regions, so we mark the boundaries
        for z_edge in [7.2, 8.8]:
            if z_edge <= self.z_max:
                deta_min = float(np.min(delta_eta)) if len(delta_eta) > 0 else -1e-4
                deta_max = float(np.max(delta_eta)) if len(delta_eta) > 0 else 1e-4
                margin = (
                    abs(deta_max - deta_min) * 0.2 if deta_max != deta_min else 1e-5
                )
                c_edge = gcurve(
                    graph=self.g1b,
                    color=to_vpy(COL_AMBER),
                    label="coupling region" if z_edge == 7.2 else "",
                )
                c_edge.plot(z_edge, deta_min - margin)
                c_edge.plot(z_edge, deta_max + margin)
                self.curves_1b.append(c_edge)

    # --------------------------------------------------- Panel 2
    def _update_panel_2(self):
        """Move the highlight marker to current U₁."""
        self.curves_2_dynamic = _clear_curves(self.curves_2_dynamic)

        u1 = self.current_u1
        eta0_for_v = self.eta0_values[-1]  # V is η₀-independent
        key = ("C", u1, eta0_for_v)
        v_cur = self.summary.get(key, {}).get("visibility", 0.55)

        # Large highlight dot at current position
        c_hl = gcurve(
            graph=self.g2,
            color=to_vpy(COL_GOLD),
            dot=True,
            dot_color=to_vpy(COL_GOLD),
            radius=6,
            label=f"Current: U\u2081={u1:.0f}, V={v_cur:.4f}",
        )
        c_hl.plot(u1, v_cur)
        self.curves_2_dynamic.append(c_hl)

    # --------------------------------------------------- Panel 3
    def _update_panel_3(self):
        """Near-field BPM fringe pattern — three perspectives.

        a. Adler predicted: η→0 ⇒ no fringes (flat at mean intensity)
        b. Standard QM: BPM at U₁=0 (full near-field fringes)
        c. QBP: BPM at current U₁ (fringes with reduced visibility)
        """
        self.curves_3 = _clear_curves(self.curves_3)

        u1 = self.current_u1
        eta0 = self.current_eta0

        # (b) Standard QM: U₁=0 baseline at current η₀
        ref_key = (0.0, eta0)
        if ref_key in self.fringe:
            x_ref, I_ref = self.fringe[ref_key]

            # (a) Adler predicted: no interference → flat at mean intensity
            I_mean = float(np.mean(I_ref))
            c_adler = gcurve(
                graph=self.g3,
                color=to_vpy(COL_ADLER),
                dot=True,
                dot_color=to_vpy(COL_ADLER),
                label=f"Adler: no fringes (\u03b7\u21920, flat at I\u0305={I_mean:.3f})",
                radius=0,
            )
            c_adler.plot(x_ref[0], I_mean)
            c_adler.plot(x_ref[-1], I_mean)
            self.curves_3.append(c_adler)

            # (b) QM baseline
            c_ref = gcurve(
                graph=self.g3,
                color=to_vpy(COL_STD_QM),
                label=f"Standard QM (U\u2081=0)",
            )
            step = max(1, len(x_ref) // 1000)
            for i in range(0, len(x_ref), step):
                c_ref.plot(x_ref[i], I_ref[i])
            self.curves_3.append(c_ref)

        # (c) QBP: current (U₁, η₀)
        main_key = (u1, eta0)
        if main_key in self.fringe:
            x_main, I_main = self.fringe[main_key]
            col = COL_EXPECTED if u1 == 0.0 else COL_QBP
            c_main = gcurve(
                graph=self.g3,
                color=to_vpy(col),
                label=f"QBP (U\u2081={u1:.0f} eV)",
            )
            step = max(1, len(x_main) // 1000)
            for i in range(0, len(x_main), step):
                c_main.plot(x_main[i], I_main[i])
            self.curves_3.append(c_main)

    # --------------------------------------------------- Panel 4
    def _update_panel_4(self):
        """Zoomed near-field fringes — three perspectives at ±0.05 nm.

        a. Adler predicted: flat (no fringes)
        b. Standard QM: U₁=0 baseline fringes
        c. QBP: current U₁ fringes
        """
        self.curves_4 = _clear_curves(self.curves_4)

        u1 = self.current_u1
        eta0 = self.current_eta0
        zoom_half = 0.05  # nm — shows ~12 fringes

        # (b) Standard QM: U₁=0 baseline
        ref_key = (0.0, eta0)
        if ref_key in self.fringe:
            x_all, I_all = self.fringe[ref_key]
            mask = (x_all >= -zoom_half) & (x_all <= zoom_half)
            x_z, I_z = x_all[mask], I_all[mask]
            if len(x_z) > 0:
                # (a) Adler: flat at mean
                I_mean = float(np.mean(I_z))
                c_adler = gcurve(
                    graph=self.g4,
                    color=to_vpy(COL_ADLER),
                    dot=True,
                    dot_color=to_vpy(COL_ADLER),
                    label="Adler: no fringes",
                    radius=0,
                )
                c_adler.plot(x_z[0], I_mean)
                c_adler.plot(x_z[-1], I_mean)
                self.curves_4.append(c_adler)

                # (b) QM baseline
                c_ref = gcurve(
                    graph=self.g4,
                    color=to_vpy(COL_STD_QM),
                    label="Standard QM (U\u2081=0)",
                )
                for i in range(len(x_z)):
                    c_ref.plot(x_z[i], I_z[i])
                self.curves_4.append(c_ref)

        # (c) QBP: current (U₁, η₀)
        main_key = (u1, eta0)
        if main_key in self.fringe:
            x_all, I_all = self.fringe[main_key]
            mask = (x_all >= -zoom_half) & (x_all <= zoom_half)
            x_z, I_z = x_all[mask], I_all[mask]
            if len(x_z) > 0:
                col = COL_EXPECTED if u1 == 0.0 else COL_QBP
                c_main = gcurve(
                    graph=self.g4,
                    color=to_vpy(col),
                    label=f"QBP (U\u2081={u1:.0f} eV)",
                )
                for i in range(len(x_z)):
                    c_main.plot(x_z[i], I_z[i])
                self.curves_4.append(c_main)

    # --------------------------------------------------- Panel 5
    def _plot_panel5_static(self):
        """Far-field static element: BPM+FFT baseline (U₁=0), plotted once.

        Analytical A/B are NOT shown here — they use a plane-wave source at
        ±0.5 mm scale, while BPM+FFT uses a Gaussian source at ±1.5 m scale.
        Mixing them on the same axes makes comparison meaningless.
        """
        # Plot the BPM+FFT Expected baseline (U₁=0) as static reference
        baseline_key = ("expected", 0.0, self.eta0_values[0])
        self._ff_baseline_peak = 1.0  # fallback
        if self.farfield_qbp and baseline_key in self.farfield_qbp:
            x_mm, I_base = self.farfield_qbp[baseline_key]
            I_peak = I_base.max()
            self._ff_baseline_peak = I_peak  # store for dynamic curve normalization
            I_norm = I_base / I_peak if I_peak > 0 else I_base
            mask = np.abs(x_mm) <= 1500
            x_clip = x_mm[mask]
            I_clip = I_norm[mask]

            c_base = gcurve(
                graph=self.g5,
                color=to_vpy(COL_EXPECTED),
                label="Expected baseline (U₁=0, BPM+FFT)",
            )
            step = max(1, len(x_clip) // 2000)
            for i in range(0, len(x_clip), step):
                c_base.plot(x_clip[i], I_clip[i])

    def _update_panel_5(self):
        """Far-field QBP dynamic curve — actual BPM+FFT data.

        Static baseline (U₁=0, red) is plotted once in _plot_panel5_static().
        This method adds the dynamic QBP coupling curve (teal) for current U₁.
        At U₁=0, nothing to add (static baseline already shows it).
        """
        if not hasattr(self, "curves_5"):
            self.curves_5 = []
        self.curves_5 = _clear_curves(self.curves_5)

        u1 = self.current_u1
        eta0 = self.current_eta0

        # At U₁=0, the static baseline already covers it
        if u1 == 0.0:
            return

        if not self.farfield_qbp:
            return

        # Find closest U₁ in available QBP data
        qbp_keys = [k for k in self.farfield_qbp if k[0] == "qbp" and k[2] == eta0]
        if not qbp_keys:
            return
        qbp_key = min(qbp_keys, key=lambda k: abs(k[1] - u1))

        if qbp_key not in self.farfield_qbp:
            return

        x_mm, I_qbp = self.farfield_qbp[qbp_key]
        # Normalize to BASELINE peak (not own peak) — preserves amplitude difference
        ref_peak = getattr(self, "_ff_baseline_peak", I_qbp.max())
        I_norm = I_qbp / ref_peak if ref_peak > 0 else I_qbp

        # Get far-field visibility from summary if available
        v_key = ("C", qbp_key[1], eta0)
        v_ff = self.summary.get(v_key, {}).get("visibility", None)
        v_label = f", V_ff={v_ff:.3f}" if v_ff is not None else ""

        c_qbp = gcurve(
            graph=self.g5,
            color=to_vpy(COL_QBP),
            label=f"QBP coupling (U\u2081={qbp_key[1]:.0f} eV{v_label})",
        )
        # Clip to ±1500 mm to avoid FFT edge artifacts
        mask = np.abs(x_mm) <= 1500
        x_clip = x_mm[mask]
        I_clip = I_norm[mask]
        step = max(1, len(x_clip) // 2000)
        for i in range(0, len(x_clip), step):
            c_qbp.plot(x_clip[i], I_clip[i])
        self.curves_5.append(c_qbp)

    # --------------------------------------------------- Stats
    def _update_stats(self):
        """Update the live stats text."""
        u1 = self.current_u1
        eta0 = self.current_eta0
        key = (u1, eta0)

        # BPM final η
        if key in self.decay:
            _, eta_arr = self.decay[key]
            eta_final = eta_arr[-1]
            delta_eta = eta_final - eta0
        else:
            eta_final = eta0
            delta_eta = 0.0

        # Adler decay length
        adler_len = self.adler_decay_length_nm(u1)

        # Visibility
        v_key = ("C", u1, eta0)
        v_cur = self.summary.get(v_key, {}).get("visibility", float("nan"))
        v_base = self.v_baseline.get(eta0, float("nan"))
        if v_base > 0 and not np.isnan(v_base) and not np.isnan(v_cur):
            v_pct = (1 - v_cur / v_base) * 100
            v_pct_str = f"\u2212{v_pct:.1f}%" if v_pct > 0 else f"+{-v_pct:.1f}%"
        else:
            v_pct_str = "N/A"

        # Adler line
        if u1 > 0:
            adler_str = f"complete decay in {adler_len:.3f} nm"
        else:
            adler_str = "no decay (U\u2081=0)"

        sign = "+" if delta_eta >= 0 else ""
        self.stats_wtext.text = (
            f"<b style='color:{COLORS.COPPER.hex};'>U\u2081</b> = {u1:.1f} eV"
            f"&nbsp;&nbsp;|&nbsp;&nbsp;"
            f"<b style='color:{COLORS.COPPER.hex};'>\u03b7\u2080</b> = {eta0}"
            f"<br>"
            f"<b>BPM:</b> \u03b7<sub>final</sub> = {eta_final:.6f}, "
            f"\u0394\u03b7 = {sign}{delta_eta:.6f}"
            f"<br>"
            f"<b>Adler predicted:</b> {adler_str}"
            f"<br>"
            f"<b>Visibility:</b> V = {v_cur:.4f} "
            f"(baseline {v_base:.4f}, {v_pct_str})"
        )

    # ----------------------------------------------------------------- run
    def run(self):
        """Main event loop."""
        print()
        print("=" * 62)
        print("  Double-Slit: Three Predictions Compared")
        print("  Sprint 3 Phase 3 -- QBP Project")
        print("=" * 62)
        print()
        print(f"  Data timestamp: {self.timestamp}")
        print(f"  Decay curves: {len(self.decay)} parameter combos")
        print(f"  Fringe patterns: {len(self.fringe)} parameter combos")
        print(f"  U\u2081 values (eV): {[f'{v:.1f}' for v in self.u1_values]}")
        print(f"  \u03b7\u2080 values: {self.eta0_values}")
        print()
        print("  Opening browser window...")
        print("  Use slider and buttons to explore.")
        print("  Press Ctrl+C to exit.")
        print()

        while True:
            rate(30)


# ============================================================================
# Entry point
# ============================================================================


def main():
    """Entry point for the double-slit visualization demo."""
    demo = DoubleSlitDemo()
    demo.run()


if __name__ == "__main__":
    main()
