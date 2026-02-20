#!/usr/bin/env python3
"""
export_data.py — Parse Lean proof files and export proof dependency graph as JSON.

Supports multiple experiments via --experiment flag:
  stern_gerlach   → data/proof_graph_01.json (legacy format)
  double_slit     → data/doubleslit.viz.json  (viz.json schema)

The viz.json format is consumed by the C/Raylib visualization at runtime.
Each node has 4-level descriptions (L1 intuitive → L4 formal Lean).

Usage:
  python3 export_data.py                           # Stern-Gerlach (default)
  python3 export_data.py --experiment double_slit   # Double-Slit
"""

import argparse
import json
import re
import sys
from pathlib import Path

# Project root (three levels up from this script's location in src/viz/interactive/)
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent

BASIC_LEAN = PROJECT_ROOT / "proofs" / "QBP" / "Basic.lean"
SG_LEAN = PROJECT_ROOT / "proofs" / "QBP" / "Experiments" / "SternGerlach.lean"
DS_LEAN = PROJECT_ROOT / "proofs" / "QBP" / "Experiments" / "DoubleSlit.lean"

DATA_DIR = Path(__file__).resolve().parent / "data"


def parse_lean_file(path: Path) -> list[dict]:
    """Extract theorem/def names and their statements from a Lean file."""
    items = []
    text = path.read_text()

    # Match theorem/def declarations
    pattern = re.compile(
        r"(?:^|\n)\s*(?:/--.*?-/\s*\n)?"  # optional doc comment
        r"(theorem|def|noncomputable def|abbrev)\s+"
        r"(\w+)"  # name
        r"(.*?)(?=\n(?:theorem|def|noncomputable|abbrev|end |--|/-)|\Z)",  # body
        re.DOTALL,
    )

    for m in pattern.finditer(text):
        kind = m.group(1).strip()
        name = m.group(2)
        body = m.group(3).strip()

        # Skip private helpers
        if name == "mkQ":
            continue

        # Clean up the statement (first line of body)
        statement_lines = []
        for line in body.split("\n"):
            stripped = line.strip()
            if stripped.startswith("--") or stripped.startswith("/-"):
                break
            if stripped.startswith("simp") or stripped.startswith("exact"):
                break
            if stripped:
                statement_lines.append(stripped)
            if ":=" in stripped or "by" == stripped.rstrip():
                break

        statement = " ".join(statement_lines)

        # Determine kind
        if kind in ("def", "noncomputable def", "abbrev"):
            node_kind = "definition"
        else:
            node_kind = "theorem"

        items.append(
            {
                "name": name,
                "kind": node_kind,
                "statement": statement,
                "source": path.name,
            }
        )

    return items


# ============================================================================
# Stern-Gerlach experiment (13 nodes) — legacy format
# ============================================================================

PHYSICAL_MEANINGS = {
    "isPureQuaternion": "Definition encoding QBP Axiom 2: observables are pure quaternions (scalar part = 0).",
    "vecDot": "Dot product of vector parts: measures alignment between state and observable axes.",
    "spin_x_is_pure": "SPIN_X = i is a valid observable (pure quaternion).",
    "spin_z_is_pure": "SPIN_Z = k is a valid observable (pure quaternion).",
    "spinXState": "Experiment state: particle with spin along +x axis (quaternion i).",
    "spinZObservable": "Measurement axis: spin measured along z axis (quaternion k).",
    "spinXState_is_pure": "The spin-x state satisfies the pure quaternion requirement.",
    "spinZObservable_is_pure": "The spin-z observable satisfies the pure quaternion requirement.",
    "x_z_orthogonal": "The x and z spin axes are perpendicular: their dot product is zero.",
    "expectation_orthogonal_is_zero": "General principle: when state and observable axes are perpendicular, expectation value is zero.",
    "expectation_x_measured_z_is_zero": "Core result: <O_z> = 0 for spin-x state. Average measurement is zero.",
    "prob_up_x_measured_z_is_half": "Probability of spin-up (+1) is exactly 50%.",
    "prob_down_x_measured_z_is_half": "Probability of spin-down (-1) is exactly 50%.",
}

SG_DEPENDENCIES = {
    "isPureQuaternion": [],
    "vecDot": [],
    "spin_x_is_pure": ["isPureQuaternion"],
    "spin_z_is_pure": ["isPureQuaternion"],
    "spinXState": [],
    "spinZObservable": [],
    "spinXState_is_pure": ["spinXState", "spin_x_is_pure"],
    "spinZObservable_is_pure": ["spinZObservable", "spin_z_is_pure"],
    "x_z_orthogonal": ["vecDot", "spinXState", "spinZObservable"],
    "expectation_orthogonal_is_zero": ["isPureQuaternion", "vecDot"],
    "expectation_x_measured_z_is_zero": [
        "expectation_orthogonal_is_zero",
        "spinXState_is_pure",
        "spinZObservable_is_pure",
        "x_z_orthogonal",
    ],
    "prob_up_x_measured_z_is_half": ["expectation_x_measured_z_is_zero"],
    "prob_down_x_measured_z_is_half": ["expectation_x_measured_z_is_zero"],
}

SG_WALK_ORDER = [
    "isPureQuaternion",
    "vecDot",
    "spin_x_is_pure",
    "spin_z_is_pure",
    "spinXState",
    "spinZObservable",
    "spinXState_is_pure",
    "spinZObservable_is_pure",
    "x_z_orthogonal",
    "expectation_orthogonal_is_zero",
    "expectation_x_measured_z_is_zero",
    "prob_up_x_measured_z_is_half",
    "prob_down_x_measured_z_is_half",
]


def build_stern_gerlach_graph() -> dict:
    """Build the Stern-Gerlach proof graph (legacy format)."""
    basic_items = parse_lean_file(BASIC_LEAN)
    sg_items = parse_lean_file(SG_LEAN)
    all_items = {item["name"]: item for item in basic_items + sg_items}

    nodes = []
    for name in SG_WALK_ORDER:
        item = all_items.get(name, {})
        kind = item.get("kind", "theorem")
        node = {
            "id": name,
            "name": name,
            "kind": kind,
            "statement": item.get("statement", name),
            "physical_meaning": PHYSICAL_MEANINGS.get(name, ""),
            "dependencies": SG_DEPENDENCIES.get(name, []),
            "source_file": item.get("source", ""),
        }
        nodes.append(node)

    return {
        "experiment": "01_stern_gerlach",
        "title": "Stern-Gerlach: Spin-X measured on Z-axis",
        "description": (
            "Formal proof that a spin-x state measured on the z-axis "
            "produces a 50/50 probability split, as predicted by the "
            "QBP quaternion framework and observed in the Stern-Gerlach experiment."
        ),
        "walk_order": SG_WALK_ORDER,
        "nodes": nodes,
    }


# ============================================================================
# Double-Slit experiment (39 nodes) — viz.json format
# ============================================================================

# Walk order: pedagogical sequence through §1→§9
DS_WALK_ORDER = [
    # §1: Complex Subspace & Basis
    "qJ",
    "isComplex",
    "coeComplex_isComplex",
    "sympForm",
    # §2: Quaternion Algebra
    "qJ_sq",
    "j_mul_complex",
    "complex_mul_j",
    "j_complex_j",
    # §3: Coupling Decomposition
    "coupling_decomposition",
    "coupling_decomposition_real",
    # §3b: Norm Conservation
    "coupling_cancellation",
    "coupling_cancellation_inner",
    # §4: Born Rule + quatFraction
    "normSq_sympForm",
    "normSq_sympForm_zero_psi1",
    "normSq_sympForm_nonneg",
    "quatFraction",
    "quatFraction_nonneg",
    "quatFraction_le_one",
    "quatFraction_zero_iff",
    # §5: Visibility Bounds
    "visibility",
    "visibility_nonneg",
    "visibility_le_one",
    "visibility_one",
    "visibility_zero",
    # §5b: V(η) Bridge — the central QBP prediction
    "visibility_eq_one_sub_quatFraction",
    "visibility_eta_zero",
    "visibility_full_when_eta_zero",
    "visibility_antitone_background",
    "visibility_correlated",
    # §7: Complex Subspace Reduction
    "coupling_decouples_U1_zero",
    "sympForm_zero_psi1",
    # §8: Decay Constant
    "decayConstant",
    "decayLength",
    "decayConstant_pos",
    "decayLength_pos",
    "decayConstant_mono_U1",
    # §9: Edge Cases & Scenarios
    "scenarioA_visibility",
    "scenarioB_visibility",
    "scenarioC_matches_scenarioA_at_detector",
]

# Dependency graph — matches actual Lean proof structure
DS_DEPENDENCIES = {
    # §1
    "qJ": [],
    "isComplex": [],
    "coeComplex_isComplex": ["isComplex"],
    "sympForm": [],
    # §2
    "qJ_sq": ["qJ"],
    "j_mul_complex": ["qJ"],
    "complex_mul_j": ["qJ"],
    "j_complex_j": ["j_mul_complex"],
    # §3
    "coupling_decomposition": [],
    "coupling_decomposition_real": [],
    # §3b
    "coupling_cancellation": [],
    "coupling_cancellation_inner": [],
    # §4
    "normSq_sympForm": ["sympForm"],
    "normSq_sympForm_zero_psi1": ["normSq_sympForm"],
    "normSq_sympForm_nonneg": ["normSq_sympForm"],
    "quatFraction": [],
    "quatFraction_nonneg": ["quatFraction"],
    "quatFraction_le_one": ["quatFraction"],
    "quatFraction_zero_iff": ["quatFraction"],
    # §5
    "visibility": [],
    "visibility_nonneg": ["visibility"],
    "visibility_le_one": ["visibility"],
    "visibility_one": ["visibility"],
    "visibility_zero": ["visibility"],
    # §5b
    "visibility_eq_one_sub_quatFraction": ["visibility", "quatFraction"],
    "visibility_eta_zero": ["visibility_eq_one_sub_quatFraction"],
    "visibility_full_when_eta_zero": ["quatFraction"],
    "visibility_antitone_background": ["visibility"],
    "visibility_correlated": ["visibility"],
    # §7
    "coupling_decouples_U1_zero": [],
    "sympForm_zero_psi1": ["sympForm", "isComplex"],
    # §8
    "decayConstant": [],
    "decayLength": [],
    "decayConstant_pos": ["decayConstant"],
    "decayLength_pos": ["decayLength"],
    "decayConstant_mono_U1": ["decayConstant"],
    # §9
    "scenarioA_visibility": ["visibility_one"],
    "scenarioB_visibility": ["visibility_zero"],
    "scenarioC_matches_scenarioA_at_detector": ["quatFraction_zero_iff"],
}

# Full 4-level descriptions for each DoubleSlit node
DS_NODES = {
    # ── §1: Complex Subspace & Basis ──────────────────────────────────────
    "qJ": {
        "display_name": "Quaternion Unit j",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def qJ : Q := (0, 0, 1, 0)",
        "L3_math": "j = (0, 0, 1, 0) in H, the quaternion unit satisfying j^2 = -1",
        "L2_physical": "The quaternion j is the key to QBP's extension beyond standard QM. It opens a second 'channel' for the wavefunction, allowing psi = psi_0 + psi_1*j where psi_0, psi_1 are complex.",
        "L1_intuitive": "Standard quantum mechanics uses complex numbers (2D). QBP extends this to quaternions (4D) by adding a new 'direction' called j. Think of it as opening a hidden dimension that standard physics ignores.",
        "key_insight": "j is the gateway from complex to quaternionic quantum mechanics.",
        "tags": ["basis"],
        "proof_role": "utility",
    },
    "isComplex": {
        "display_name": "Complex Subspace",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "def isComplex (q : Q) : Prop := q.imJ = 0 AND q.imK = 0",
        "L3_math": "q in C <-> imJ(q) = 0 and imK(q) = 0, identifying C as a subspace of H",
        "L2_physical": "Defines when a quaternion is 'just' a complex number — no j or k components. Standard QM lives entirely in this subspace.",
        "L1_intuitive": "Imagine a building with four floors. Standard quantum mechanics only uses the bottom two floors (real and i). A 'complex' quaternion is one that stays on those two floors, never venturing upstairs.",
        "key_insight": "Standard QM is a subset of QBP — the complex subspace.",
        "tags": ["basis", "reduction"],
        "proof_role": "utility",
    },
    "coeComplex_isComplex": {
        "display_name": "Complex Embedding",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coeComplex_isComplex (a b : R) : isComplex ((a, b, 0, 0) : Q)",
        "L3_math": "For all a, b in R: (a, b, 0, 0) in C (subset of H)",
        "L2_physical": "Any complex number a + bi can be embedded in the quaternions as (a, b, 0, 0). This embedding preserves all complex arithmetic.",
        "L1_intuitive": "If you live on the first two floors, you're definitely a 'complex resident.' This just confirms the obvious: numbers with zero j and k parts are indeed complex.",
        "key_insight": "The embedding C -> H is well-defined.",
        "tags": ["basis"],
        "proof_role": "lemma",
    },
    "sympForm": {
        "display_name": "Symplectic Form",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def sympForm (re0 im0 re1 im1 : R) : Q :=\n  (re0, im0, re1, im1)",
        "L3_math": "psi = psi_0 + psi_1*j where psi_0 = (re0, im0), psi_1 = (re1, im1) in C",
        "L2_physical": "The quaternionic wavefunction decomposes into two complex parts: psi_0 (standard) and psi_1 (quaternionic). This is the symplectic form — the fundamental decomposition of QBP.",
        "L1_intuitive": "Split the 4D quaternion into two 2D complex numbers. One is the 'normal' part (what standard QM sees), the other is the 'hidden' part (what QBP adds). Together they make the full wavefunction.",
        "key_insight": "Every quaternionic state splits into a standard part and a hidden part.",
        "tags": ["basis"],
        "proof_role": "utility",
    },
    # ── §2: Quaternion Algebra ────────────────────────────────────────────
    "qJ_sq": {
        "display_name": "j Squared = -1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem qJ_sq : qJ * qJ = -(1 : Q)",
        "L3_math": "j^2 = -1",
        "L2_physical": "The defining identity of quaternion j, analogous to i^2 = -1 for complex numbers. This drives the coupling between the two complex subspaces.",
        "L1_intuitive": "Just like i*i = -1 defines imaginary numbers, j*j = -1 defines quaternions. This simple rule has profound consequences: it's what allows the two 'channels' of the wavefunction to talk to each other.",
        "key_insight": "j^2 = -1 is the engine of quaternionic coupling.",
        "tags": ["algebra"],
        "proof_role": "lemma",
    },
    "j_mul_complex": {
        "display_name": "j Times Complex (Left)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem j_mul_complex (a b : R) :\n    qJ * (a, b, 0, 0) = (0, 0, a, -b)",
        "L3_math": "j * z = z* * j, where z = a + bi and z* = a - bi (complex conjugation)",
        "L2_physical": "When j passes through a complex number, it conjugates it (flips the sign of the imaginary part). This non-commutativity is THE key difference from standard QM.",
        "L1_intuitive": "In normal math, order doesn't matter: 3*5 = 5*3. But with quaternions, j doesn't commute — passing j through a complex number flips a sign. This is like a mirror: the number comes out as its reflection.",
        "key_insight": "j commutes by conjugation — the source of coupling.",
        "tags": ["algebra"],
        "proof_role": "lemma",
    },
    "complex_mul_j": {
        "display_name": "Complex Times j (Right)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem complex_mul_j (a b : R) :\n    (a, b, 0, 0) * qJ = (0, 0, a, b)",
        "L3_math": "z * j = (0, 0, a, b) for z = a + bi — note: z*j != j*z",
        "L2_physical": "Multiplying from the right is different from the left. This asymmetry is non-commutativity in action — the hallmark of quaternionic quantum mechanics.",
        "L1_intuitive": "If j-from-the-left is a mirror, j-from-the-right is a different mirror. The image isn't the same. This left-right asymmetry is what makes quaternions richer than complex numbers.",
        "key_insight": "Left and right multiplication differ — quaternions are non-commutative.",
        "tags": ["algebra"],
        "proof_role": "lemma",
    },
    "j_complex_j": {
        "display_name": "Triple Product j*z*j",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem j_complex_j (a b : R) :\n    qJ * (a, b, 0, 0) * qJ = (-a, b, 0, 0)",
        "L3_math": "j*z*j = -z* for complex z = a + bi",
        "L2_physical": "The sandwich product j*z*j negates and conjugates z. This triple product appears in the coupling decomposition when expanding (U_0 + U_1*j)(psi_0 + psi_1*j).",
        "L1_intuitive": "Put a complex number between two j's and it comes out flipped twice: conjugated AND negated. This double transformation is what makes the coupling equations work out just right.",
        "key_insight": "The triple product combines conjugation and negation.",
        "tags": ["algebra"],
        "proof_role": "lemma",
    },
    # ── §3: Coupling Decomposition ────────────────────────────────────────
    "coupling_decomposition": {
        "display_name": "Coupling Decomposition",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coupling_decomposition (U0 U1 a0 b0 a1 b1 : R) :\n    (U0 + U1*j)(psi0 + psi1*j) =\n    (U0*a0 - U1*a1, U0*b0 + U1*b1, U0*a1 + U1*a0, U0*b1 - U1*b0)",
        "L3_math": "(U_0 + U_1 j)(psi_0 + psi_1 j) = (U_0 psi_0 - U_1 psi_1*) + (U_0 psi_1 + U_1 psi_0*) j",
        "L2_physical": "THE central algebraic result. When a quaternionic potential acts on a quaternionic wavefunction, it produces coupled equations: each complex component depends on both. This is how quantum gravity or new physics could couple the channels.",
        "L1_intuitive": "This is the master equation. Multiply out the brackets using j² = −1 and j · z = z̄ · j (j conjugates complex numbers), and you get two intertwined equations. The standard part mixes with the hidden part, and vice versa. They can no longer be separated — they're coupled.",
        "key_insight": "The quaternionic potential couples the two complex channels.",
        "tags": ["coupling"],
        "proof_role": "lemma",
    },
    "coupling_decomposition_real": {
        "display_name": "Coupling (Real Potentials)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coupling_decomposition_real (U0 U1 a0 a1 : R) :\n    (U0, 0, U1, 0) * (a0, 0, a1, 0) =\n    (U0*a0 - U1*a1, 0, U0*a1 + U1*a0, 0)",
        "L3_math": "For purely real potentials and wavefunctions:\n(U_0 + U_1 j)(a_0 + a_1 j) = (U_0 a_0 - U_1 a_1) + (U_0 a_1 + U_1 a_0) j",
        "L2_physical": "When everything is real (no imaginary parts), the coupling simplifies. The structure looks like a 2x2 rotation/mixing matrix acting on (a_0, a_1).",
        "L1_intuitive": "Strip away the imaginary parts and the coupling becomes even clearer: it's just mixing two real numbers, like adjusting two volume knobs that influence each other.",
        "key_insight": "Real potentials couple real wavefunctions via a mixing matrix.",
        "tags": ["coupling"],
        "proof_role": "lemma",
    },
    # ── §3b: Norm Conservation ────────────────────────────────────────────
    "coupling_cancellation": {
        "display_name": "Coupling Cancellation (Unitarity)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coupling_cancellation (U1 a0 b0 a1 b1 : R) :\n    2 * (a0 * (-U1*a1) + b0 * (U1*b1) +\n         a1 * (U1*a0) + b1 * (-U1*b0)) = 0",
        "L3_math": "d/dt(|psi_0|^2 + |psi_1|^2)|_coupling = 0",
        "L2_physical": "The coupling terms cancel in the total norm. Energy flows between psi_0 and psi_1 but is never created or destroyed. This proves unitarity — probability is conserved.",
        "L1_intuitive": "Pour water between two glasses: the total amount never changes. That's exactly what happens here — the coupling moves probability between the two channels but never leaks it. Conservation is guaranteed by pure algebra.",
        "key_insight": "Coupling redistributes probability but conserves the total.",
        "tags": ["conservation"],
        "proof_role": "lemma",
    },
    "coupling_cancellation_inner": {
        "display_name": "Coupling Cancellation (Inner Product)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coupling_cancellation_inner (U1 a0 b0 a1 b1 : R) :\n    Re(psi_0* . (-U1*psi_1*)) + Re(psi_1* . (U1*psi_0*)) = 0",
        "L3_math": "<psi_0, -U_1 psi_1*> + <psi_1, U_1 psi_0*> = 0 where <.,.> = Re(z_1* z_2)",
        "L2_physical": "Alternative formulation using complex inner products. The anti-symmetry of the coupling terms guarantees cancellation — what one channel gains, the other loses.",
        "L1_intuitive": "Same conservation law, different notation. Written as inner products, you can see the cancellation is forced by the structure: +U_1 in one term, -U_1 in the other. They're born to cancel.",
        "key_insight": "Anti-symmetric coupling structure forces conservation.",
        "tags": ["conservation"],
        "proof_role": "lemma",
    },
    # ── §4: Born Rule + quatFraction ──────────────────────────────────────
    "normSq_sympForm": {
        "display_name": "No Cross-Terms (Born Rule)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem normSq_sympForm (a0 b0 a1 b1 : R) :\n    (sympForm a0 b0 a1 b1).normSq =\n    (a0^2 + b0^2) + (a1^2 + b1^2)",
        "L3_math": "|psi|^2 = |psi_0|^2 + |psi_1|^2 (no cross-terms)",
        "L2_physical": "THE crucial structural result. The quaternion norm decomposes cleanly: the complex and j-complex parts don't interfere with each other in the Born rule. There are NO cross-terms between psi_0 and psi_1.",
        "L1_intuitive": "When you calculate the total probability, the standard and hidden parts add up independently — no mixing, no interference between them. It's like counting apples and oranges: the total is just apples + oranges, never apple-orange hybrids.",
        "key_insight": "The Born rule has no cross-terms — the basis for visibility theory.",
        "tags": ["born_rule"],
        "proof_role": "lemma",
    },
    "normSq_sympForm_zero_psi1": {
        "display_name": "Norm with Zero psi_1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem normSq_sympForm_zero_psi1 (a0 b0 : R) :\n    (sympForm a0 b0 0 0).normSq = a0^2 + b0^2",
        "L3_math": "|psi_0 + 0*j|^2 = |psi_0|^2",
        "L2_physical": "When the j-component is zero, we recover the standard complex norm. QBP reduces to standard QM in this limit.",
        "L1_intuitive": "If there's nothing in the hidden channel, the total probability is just what the standard channel contains. Standard QM is the special case where the hidden part is empty.",
        "key_insight": "Zero j-component recovers standard quantum mechanics.",
        "tags": ["born_rule", "reduction"],
        "proof_role": "lemma",
    },
    "normSq_sympForm_nonneg": {
        "display_name": "Norm is Non-Negative",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem normSq_sympForm_nonneg (a0 b0 a1 b1 : R) :\n    0 <= (sympForm a0 b0 a1 b1).normSq",
        "L3_math": "|psi|^2 >= 0 (sum of squares)",
        "L2_physical": "The norm squared is a sum of squares, so it's always non-negative. This ensures probabilities are never negative — a basic sanity check.",
        "L1_intuitive": "Squares are always positive (or zero). Since the probability is a sum of squares, it can never go negative. You can't have -30% chance of something happening.",
        "key_insight": "Positivity of probabilities is guaranteed by algebra.",
        "tags": ["born_rule"],
        "proof_role": "lemma",
    },
    "quatFraction": {
        "display_name": "Quaternionic Fraction eta",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def quatFraction (normSq0 normSq1 : R) : R :=\n  normSq1 / (normSq0 + normSq1)",
        "L3_math": "eta = |psi_1|^2 / (|psi_0|^2 + |psi_1|^2)",
        "L2_physical": "The fraction of total probability living in the j-channel. eta = 0 means pure complex (standard QM). eta = 1 means fully quaternionic. This is THE observable that QBP predicts experiments can measure.",
        "L1_intuitive": "What percentage of the wavefunction is hiding in the extra dimension? If eta = 0, nothing is hidden — standard physics applies. If eta = 0.3, 30% has leaked into the quaternionic channel. This number controls how much interference you lose.",
        "key_insight": "eta measures 'how quaternionic' the system is.",
        "tags": ["bridge"],
        "proof_role": "utility",
    },
    "quatFraction_nonneg": {
        "display_name": "eta >= 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem quatFraction_nonneg {n0 n1 : R}\n    (h0 : n0 >= 0) (h1 : n1 >= 0) (hsum : n0 + n1 > 0) :\n    quatFraction n0 n1 >= 0",
        "L3_math": "eta >= 0 when n_0, n_1 >= 0",
        "L2_physical": "You can't have a negative fraction of probability in the j-channel. This is a basic bound that ensures eta is a valid fraction.",
        "L1_intuitive": "You can't have less than 0% of something. The hidden channel always contains zero or more probability — never a debt.",
        "key_insight": "Lower bound: eta is a valid fraction.",
        "tags": ["bridge"],
        "proof_role": "lemma",
    },
    "quatFraction_le_one": {
        "display_name": "eta <= 1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem quatFraction_le_one {n0 n1 : R}\n    (h0 : n0 >= 0) (h1 : n1 >= 0) (hsum : n0 + n1 > 0) :\n    quatFraction n0 n1 <= 1",
        "L3_math": "eta <= 1 when n_0, n_1 >= 0",
        "L2_physical": "The j-channel can hold at most 100% of the probability. Together with eta >= 0, this proves eta is in [0, 1].",
        "L1_intuitive": "You can't hide MORE than everything. At most 100% of the wavefunction can be in the hidden channel. This upper bound completes the proof that eta is a proper fraction.",
        "key_insight": "Upper bound: eta is a valid fraction.",
        "tags": ["bridge"],
        "proof_role": "lemma",
    },
    "quatFraction_zero_iff": {
        "display_name": "eta = 0 iff psi_1 = 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem quatFraction_zero_iff {n0 n1 : R}\n    (h0 : n0 > 0) (h1 : n1 >= 0) :\n    quatFraction n0 n1 = 0 <-> n1 = 0",
        "L3_math": "eta = 0 <=> |psi_1|^2 = 0 <=> psi_1 = 0",
        "L2_physical": "The quaternionic fraction is zero if and only if there is no j-component at all. This characterizes the boundary between QBP and standard QM.",
        "L1_intuitive": "Zero percent hidden means nothing is hidden. And the only way to get zero percent is if there's literally nothing there. This is the precise boundary: eta = 0 IS standard quantum mechanics.",
        "key_insight": "eta = 0 is the exact boundary between QBP and standard QM.",
        "tags": ["bridge", "reduction"],
        "proof_role": "lemma",
    },
    # ── §5: Visibility Bounds ─────────────────────────────────────────────
    "visibility": {
        "display_name": "Visibility Definition",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def visibility (Imax Imin : R) : R :=\n  (Imax - Imin) / (Imax + Imin)",
        "L3_math": "V = (I_max - I_min) / (I_max + I_min)",
        "L2_physical": "Fringe visibility measures the contrast of interference fringes. V = 1 means perfect dark-and-bright bands. V = 0 means uniform illumination (no interference). This is what experimentalists measure.",
        "L1_intuitive": "Look at a double-slit pattern: bright bands and dark bands. Visibility measures how sharp the contrast is. Perfect stripes? V = 1. Everything looks the same brightness? V = 0. It's like the 'contrast' slider on a TV.",
        "key_insight": "Visibility is the experimentally measurable contrast of interference.",
        "tags": ["bridge"],
        "proof_role": "utility",
    },
    "visibility_nonneg": {
        "display_name": "V >= 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_nonneg {Imax Imin : R}\n    (hge : Imax >= Imin) (hmin : Imin >= 0) (hmax : Imax > 0) :\n    visibility Imax Imin >= 0",
        "L3_math": "V >= 0 when I_max >= I_min >= 0",
        "L2_physical": "Visibility can't be negative. You can't have 'worse than no' interference.",
        "L1_intuitive": "The contrast slider can't go below zero. At worst, there's no pattern at all (V = 0).",
        "key_insight": "Visibility lower bound: no fringes is the worst case.",
        "tags": [],
        "proof_role": "lemma",
    },
    "visibility_le_one": {
        "display_name": "V <= 1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_le_one {Imax Imin : R}\n    (hge : Imax >= Imin) (hmin : Imin >= 0) (hmax : Imax > 0) :\n    visibility Imax Imin <= 1",
        "L3_math": "V <= 1 when I_max >= I_min >= 0",
        "L2_physical": "Visibility can't exceed 1. Perfect contrast (complete darkness at minima) is the best possible.",
        "L1_intuitive": "The contrast slider maxes out at 100%. Even the sharpest interference pattern can't be 'more than perfect.'",
        "key_insight": "Visibility upper bound: perfect fringes are the best case.",
        "tags": [],
        "proof_role": "lemma",
    },
    "visibility_one": {
        "display_name": "V = 1 (Perfect Fringes)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_one {Imax : R} (hmax : Imax > 0) :\n    visibility Imax 0 = 1",
        "L3_math": "V = 1 when I_min = 0 (complete destructive interference at minima)",
        "L2_physical": "When the minimum intensity is zero (complete darkness between bright fringes), visibility is 1. This is standard double-slit with perfect coherence.",
        "L1_intuitive": "If the dark bands are truly dark — zero light — then the pattern is as sharp as it gets. This is what happens with perfectly coherent light in a textbook double-slit experiment.",
        "key_insight": "Zero minimum intensity = perfect visibility.",
        "tags": [],
        "proof_role": "lemma",
    },
    "visibility_zero": {
        "display_name": "V = 0 (No Fringes)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_zero {I : R} (hI : I > 0) :\n    visibility I I = 0",
        "L3_math": "V = 0 when I_max = I_min (uniform intensity, no pattern)",
        "L2_physical": "When maximum and minimum intensity are equal, there's no pattern at all — just uniform illumination. This is the which-path limit: knowing which slit the particle went through destroys interference.",
        "L1_intuitive": "If everywhere is equally bright, there are no stripes. The pattern has been completely washed out. This happens when you 'spy' on which slit the particle uses.",
        "key_insight": "Equal max and min = pattern destroyed.",
        "tags": [],
        "proof_role": "lemma",
    },
    # ── §5b: V(eta) Bridge — THE central QBP prediction ──────────────────
    "visibility_eq_one_sub_quatFraction": {
        "display_name": "V = 1 - eta (Model A)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_eq_one_sub_quatFraction {n0 n1 : R}\n    (h0 : n0 > 0) (h1 : n1 >= 0) :\n    visibility (2*n0 + n1) n1 = 1 - quatFraction n0 n1",
        "L3_math": "V = 1 - eta where eta = n_1/(n_0 + n_1), I_max = 2n_0 + n_1, I_min = n_1",
        "L2_physical": "THE CENTRAL QBP PREDICTION (Model A). When the j-component acts as incoherent background, each percentage point of quaternionic fraction directly reduces visibility. V = 1 - eta is the experimentally testable relationship between the hidden quaternionic content and observable fringe contrast.",
        "L1_intuitive": "HERE'S THE BIG RESULT. The hidden quaternionic channel steals visibility from the interference pattern, point for point. 10% hidden = 10% less contrast. 50% hidden = half the fringes gone. If you can measure how the fringes fade, you can measure the quaternion.",
        "key_insight": "V = 1 - eta: quaternionic content directly degrades interference.",
        "tags": ["bridge"],
        "proof_role": "goal",
    },
    "visibility_eta_zero": {
        "display_name": "eta = 0 Gives V = 1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_eta_zero {n0 : R} (h0 : n0 > 0) :\n    visibility (2*n0 + 0) 0 = 1 - quatFraction n0 0",
        "L3_math": "V(eta=0) = 1 - 0 = 1 (standard QM limit)",
        "L2_physical": "When there's no j-component (standard QM), the V = 1 - eta formula gives V = 1. Standard QM predicts perfect interference — as observed.",
        "L1_intuitive": "No hidden channel, no fading. Everything is in the standard part, so you get the textbook perfect interference pattern. Our formula correctly reduces to the known physics.",
        "key_insight": "The formula correctly recovers standard QM.",
        "tags": ["bridge", "reduction"],
        "proof_role": "lemma",
    },
    "visibility_full_when_eta_zero": {
        "display_name": "1 - eta = 1 When eta = 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_full_when_eta_zero {n0 : R} (h0 : n0 > 0) :\n    1 - quatFraction n0 0 = 1",
        "L3_math": "1 - eta(n_0, 0) = 1 - 0 = 1",
        "L2_physical": "Direct computation: when n_1 = 0, the quatFraction is zero, so 1 - eta = 1. The complementary view of visibility_eta_zero.",
        "L1_intuitive": "Zero hidden means zero penalty. 1 minus nothing is still 1. Perfect visibility, as expected.",
        "key_insight": "No quaternionic content = no visibility penalty.",
        "tags": ["bridge", "reduction"],
        "proof_role": "lemma",
    },
    "visibility_antitone_background": {
        "display_name": "More Background = Less Visibility",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_antitone_background {n0 B1 B2 : R}\n    (h0 : n0 > 0) (hB1 : B1 >= 0) (hB2 : B2 >= 0) (hle : B1 <= B2) :\n    visibility (2*n0 + B2) B2 <= visibility (2*n0 + B1) B1",
        "L3_math": "B_1 <= B_2 => V(B_2) <= V(B_1) (visibility is anti-monotone in background)",
        "L2_physical": "Increasing the j-component background monotonically decreases visibility. The more quaternionic content, the worse the fringes. There's no way to add background and improve the pattern.",
        "L1_intuitive": "More noise always means less signal. Adding more hidden-channel background can only wash out the fringes further, never sharpen them. The degradation is one-way and irreversible.",
        "key_insight": "Quaternionic background monotonically degrades interference.",
        "tags": ["bridge"],
        "proof_role": "lemma",
    },
    "visibility_correlated": {
        "display_name": "Visibility Preserved (Model B)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem visibility_correlated {Imax Imin r : R}\n    (hge : Imax >= Imin) (hmin : Imin >= 0) (hmax : Imax > 0) (hr : r > -1) :\n    visibility ((1+r)*Imax) ((1+r)*Imin) = visibility Imax Imin",
        "L3_math": "V((1+r)*I_max, (1+r)*I_min) = V(I_max, I_min) — scaling cancels",
        "L2_physical": "THE SECOND QBP PREDICTION (Model B). When psi_1 has the same spatial pattern as psi_0 (correlated coupling), the total intensity just scales uniformly. The ratio cancels and visibility is preserved regardless of eta.",
        "L1_intuitive": "If the hidden channel makes the same pattern as the standard channel — same stripes in the same places — then adding it just makes everything proportionally brighter. The contrast ratio stays the same, like turning up brightness without changing contrast.",
        "key_insight": "Correlated coupling preserves visibility — Model B.",
        "tags": ["bridge"],
        "proof_role": "goal",
    },
    # ── §7: Complex Subspace Reduction ────────────────────────────────────
    "coupling_decouples_U1_zero": {
        "display_name": "U_1 = 0 Decouples System",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem coupling_decouples_U1_zero (U0 a0 b0 a1 b1 : R) :\n    (U0, 0, 0, 0) * (a0, b0, a1, b1) =\n    (U0*a0, U0*b0, U0*a1, U0*b1)",
        "L3_math": "(U_0 + 0*j)(psi) = U_0*psi (each component scales independently)",
        "L2_physical": "When U_1 = 0 (no quaternionic coupling), the potential just scales each component by U_0. The two channels decouple into independent Schrodinger equations — standard QM.",
        "L1_intuitive": "Turn off the coupling and the two channels ignore each other. Each evolves on its own, exactly like standard quantum mechanics says. QBP reduces to QM when the new physics is absent.",
        "key_insight": "No coupling = standard QM (the complex subspace reduction).",
        "tags": ["reduction"],
        "proof_role": "lemma",
    },
    "sympForm_zero_psi1": {
        "display_name": "psi_1 = 0 is Complex",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem sympForm_zero_psi1 (a0 b0 : R) :\n    isComplex (sympForm a0 b0 0 0)",
        "L3_math": "psi_0 + 0*j in C (the complex subspace)",
        "L2_physical": "A wavefunction with no j-component is a standard complex wavefunction. This confirms that the complex subspace is properly embedded in the quaternionic formalism.",
        "L1_intuitive": "If nothing is in the hidden channel, what remains is exactly a standard complex number. The quaternionic framework properly contains standard QM as a special case.",
        "key_insight": "QBP with empty j-channel IS standard QM.",
        "tags": ["reduction"],
        "proof_role": "lemma",
    },
    # ── §8: Decay Constant ────────────────────────────────────────────────
    "decayConstant": {
        "display_name": "Decay Constant kappa",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def decayConstant (U1 d : R) : R := U1 * d",
        "L3_math": "kappa = U_1 * d (dimensionless coupling proxy)",
        "L2_physical": "The decay constant measures how quickly interference fades with quaternionic coupling. It's the product of the coupling strength U_1 and the slit separation d.",
        "L1_intuitive": "How fast do the fringes fade? This number tells you. Stronger coupling or wider slits means faster fading. It's like a 'fade rate' for the interference pattern.",
        "key_insight": "kappa controls the rate of visibility loss.",
        "tags": ["decay"],
        "proof_role": "utility",
    },
    "decayLength": {
        "display_name": "Decay Length",
        "kind": "definition",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "noncomputable def decayLength (kappa : R) : R := 1 / kappa",
        "L3_math": "L_decay = 1/kappa (distance for 1/e visibility drop)",
        "L2_physical": "The characteristic distance over which visibility drops by a factor of 1/e. Longer decay length means the interference pattern persists further.",
        "L1_intuitive": "How far can you go before the fringes fade noticeably? This is that distance. A long decay length means fringes persist far from the slits; a short one means they fade quickly.",
        "key_insight": "L_decay sets the experimental length scale for testing QBP.",
        "tags": ["decay"],
        "proof_role": "utility",
    },
    "decayConstant_pos": {
        "display_name": "kappa > 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem decayConstant_pos {U1 d : R}\n    (hU1 : U1 > 0) (hd : d > 0) :\n    decayConstant U1 d > 0",
        "L3_math": "kappa > 0 when U_1 > 0 and d > 0",
        "L2_physical": "Any nonzero coupling with nonzero slit separation produces a positive decay constant. The fringes WILL fade eventually.",
        "L1_intuitive": "If there's any coupling at all and the slits are separated, the fading rate is positive. You can't have coupling that somehow sharpens fringes.",
        "key_insight": "Positive coupling always causes fading.",
        "tags": ["decay"],
        "proof_role": "lemma",
    },
    "decayLength_pos": {
        "display_name": "L_decay > 0",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem decayLength_pos {kappa : R} (hkappa : kappa > 0) :\n    decayLength kappa > 0",
        "L3_math": "L_decay > 0 when kappa > 0",
        "L2_physical": "The decay length is positive (finite). The fringes persist over some real distance before fading — they don't vanish instantly.",
        "L1_intuitive": "The fading happens over a real, finite distance — not instantaneously. You get some fringes before they fade. The experiment has a window to see the effect.",
        "key_insight": "Fading is gradual, not instantaneous.",
        "tags": ["decay"],
        "proof_role": "lemma",
    },
    "decayConstant_mono_U1": {
        "display_name": "kappa Increases with U_1",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem decayConstant_mono_U1 {U1 U1' d : R}\n    (hd : d > 0) (h : U1 < U1') :\n    decayConstant U1 d < decayConstant U1' d",
        "L3_math": "U_1 < U_1' => kappa(U_1) < kappa(U_1')",
        "L2_physical": "Stronger coupling means faster decay. The monotonicity ensures there's a clean experimental signature: more coupling = less interference.",
        "L1_intuitive": "Crank up the coupling and the fringes fade faster. There's no sweet spot where more coupling somehow helps — it always makes things worse for the fringes.",
        "key_insight": "Stronger coupling = faster decoherence (monotonic).",
        "tags": ["decay"],
        "proof_role": "lemma",
    },
    # ── §9: Edge Cases & Scenarios ────────────────────────────────────────
    "scenarioA_visibility": {
        "display_name": "Scenario A: Baseline (V = 1)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem scenarioA_visibility {I0 : R} (hI0 : I0 > 0) :\n    visibility I0 0 = 1",
        "L3_math": "V = 1 when I_min = 0 (Scenario A: no coupling, U_1 = 0)",
        "L2_physical": "Scenario A: standard double-slit with no quaternionic coupling. Perfect interference fringes, V = 1. This is the experimental baseline.",
        "L1_intuitive": "Run the experiment normally, no weird new physics. You get the textbook perfect interference pattern. This is what we compare everything else to.",
        "key_insight": "Standard double-slit gives perfect fringes (baseline).",
        "tags": ["reduction"],
        "proof_role": "lemma",
    },
    "scenarioB_visibility": {
        "display_name": "Scenario B: Which-Path (V = 0)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem scenarioB_visibility {I : R} (hI : I > 0) :\n    visibility I I = 0",
        "L3_math": "V = 0 when I_max = I_min (Scenario B: full which-path information)",
        "L2_physical": "Scenario B: full quaternionic coupling destroys all interference. Which-path information from the j-channel completely washes out the fringes.",
        "L1_intuitive": "Full coupling means full 'spying' on which slit the particle used. The fringes vanish completely. You can know the path OR see the pattern — never both.",
        "key_insight": "Full coupling destroys interference (complementarity).",
        "tags": [],
        "proof_role": "lemma",
    },
    "scenarioC_matches_scenarioA_at_detector": {
        "display_name": "Scenario C: Recovery (eta = 0)",
        "kind": "theorem",
        "source_file": "QBP/Experiments/DoubleSlit.lean",
        "L4_formal": "theorem scenarioC_matches_scenarioA_at_detector {n0 : R}\n    (hn0 : n0 > 0) :\n    quatFraction n0 0 = 0",
        "L3_math": "eta(n_0, 0) = 0 (measurement projects to complex subspace)",
        "L2_physical": "Scenario C: when psi_1 = 0 (no quaternionic component remains), eta = 0 and the system matches Scenario A. Physically, the decay theorems (Section 8) show coupling vanishes at large distance, so at the detector the state is effectively complex and full interference is recovered.",
        "L1_intuitive": "Measure the particle and collapse its hidden channel to zero. Now it's back in standard QM territory, and interference returns. The fringes come back because the quaternionic contamination was removed.",
        "key_insight": "Projecting away psi_1 recovers standard QM interference.",
        "tags": ["reduction"],
        "proof_role": "lemma",
    },
}


def build_doubleslit_viz() -> dict:
    """Build the DoubleSlit viz.json structure with 4-level descriptions."""
    # Parse Lean files for cross-referencing (L4 from source)
    ds_items = parse_lean_file(DS_LEAN)
    lean_by_name = {item["name"]: item for item in ds_items}

    # Build nodes dict (viz.json format: dict keyed by name)
    nodes = {}
    for name in DS_WALK_ORDER:
        node = dict(DS_NODES[name])  # copy the curated description
        node["depends_on"] = DS_DEPENDENCIES.get(name, [])

        # Override kind from Lean source if available
        if name in lean_by_name:
            lean_kind = lean_by_name[name]["kind"]
            # Keep "axiom" if manually set, otherwise use Lean's kind
            if node.get("kind") != "axiom":
                node["kind"] = lean_kind

        nodes[name] = node

    return {
        "_schema": {
            "description": "QBP Proof Visualization Schema v1.0",
            "levels": {
                "L4_formal": "Lean syntax - exact code from proof files, for proof assistant users",
                "L3_math": "Mathematical notation - conventional symbols, for physicists/mathematicians",
                "L2_physical": "Physics interpretation - what it means physically, for students",
                "L1_intuitive": "Plain English - accessible explanation, for general audience",
            },
            "guidelines": (
                "L4 should be copy-pasteable Lean. L3 uses standard math notation. "
                "L2 connects to observable phenomena. L1 uses analogies and avoids jargon."
            ),
        },
        "experiment_id": "03_double_slit",
        "title": "Double-Slit: V = 1 - eta (Quaternionic Visibility Bridge)",
        "description": (
            "Formal proof of the QBP visibility prediction. The quaternionic fraction "
            "eta measures how much of the wavefunction lives in the j-channel. "
            "Model A predicts V = 1 - eta (incoherent background), while Model B "
            "shows visibility is preserved under correlated coupling."
        ),
        "walk_order": DS_WALK_ORDER,
        "nodes": nodes,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Export QBP proof dependency graphs as JSON"
    )
    parser.add_argument(
        "--experiment",
        choices=["stern_gerlach", "double_slit"],
        default="stern_gerlach",
        help="Which experiment to export (default: stern_gerlach)",
    )
    args = parser.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)

    if args.experiment == "stern_gerlach":
        graph = build_stern_gerlach_graph()
        output = DATA_DIR / "proof_graph_01.json"
        with open(output, "w") as f:
            json.dump(graph, f, indent=2)
        print(f"Exported {len(graph['nodes'])} nodes to {output}")

    elif args.experiment == "double_slit":
        graph = build_doubleslit_viz()
        output = DATA_DIR / "doubleslit.viz.json"
        with open(output, "w") as f:
            json.dump(graph, f, indent=2)
        print(f"Exported {len(graph['nodes'])} nodes to {output}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
