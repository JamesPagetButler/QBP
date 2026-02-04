# experiments/02_angle_test/simulate_angle.py
"""
Angle-Dependent Measurement Test

This experiment validates the quantum mechanical prediction that the probability
of measuring spin-up along an axis at angle theta from the particle's spin direction
follows: P(+) = (1 + cos(theta))/2

This is a fundamental test of the Malus-like law for spin measurements.
"""

import numpy as np
import sys
import os
from datetime import datetime

# Add the project root to the Python path to allow imports from src
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


def run_angle_test(angles=None, num_particles=100000, seed=42):
    """
    Test P(+) = (1 + cos(theta))/2 at various angles.

    Args:
        angles: List of angles in degrees to test. Defaults to standard test angles.
        num_particles: Number of particles to simulate per angle.
        seed: Random seed for reproducibility.

    Returns:
        dict: Results containing angles, expected probabilities, and measured probabilities.
    """
    if angles is None:
        angles = [0, 30, 45, 60, 90, 120, 135, 150, 180]  # degrees

    results = {
        "angles": [],
        "expected_prob": [],
        "measured_prob": [],
        "deviation_sigma": [],
    }

    print("=" * 60)
    print("ANGLE-DEPENDENT MEASUREMENT TEST")
    print("=" * 60)
    print(f"Testing P(+) = (1 + cos(theta))/2 at various angles")
    print(f"Particles per angle: {num_particles}")
    print(f"Random seed: {seed}")
    print("-" * 60)

    # We measure against Z-axis
    observable = qphysics.SPIN_Z

    for i, angle_deg in enumerate(angles):
        theta = np.radians(angle_deg)

        # Create state at angle theta from Z-axis (in XZ plane)
        # State points along: (sin(theta), 0, cos(theta))
        state = qphysics.create_state_from_vector([np.sin(theta), 0, np.cos(theta)])

        # Use different seed for each angle to ensure independence
        angle_seed = seed + i if seed is not None else None

        # Perform batch measurement
        outcomes = qphysics.measure_batch(state, observable, num_particles, angle_seed)

        # Calculate measured probability of spin-up
        measured_prob = np.sum(outcomes == 1) / num_particles

        # Calculate expected probability
        expected_prob = (1 + np.cos(theta)) / 2

        # Calculate statistical deviation in sigma
        # Standard deviation of binomial: sqrt(p*(1-p)/n)
        std_dev = np.sqrt(expected_prob * (1 - expected_prob) / num_particles)
        deviation_sigma = (
            abs(measured_prob - expected_prob) / std_dev if std_dev > 0 else 0
        )

        results["angles"].append(angle_deg)
        results["expected_prob"].append(expected_prob)
        results["measured_prob"].append(measured_prob)
        results["deviation_sigma"].append(deviation_sigma)

        print(
            f"Angle {angle_deg:3d}°: Expected {expected_prob:.4f}, "
            f"Measured {measured_prob:.4f}, Deviation {deviation_sigma:.2f}σ"
        )

    print("-" * 60)

    # Summary statistics
    max_deviation = max(results["deviation_sigma"])
    avg_deviation = np.mean(results["deviation_sigma"])

    print(f"Maximum deviation: {max_deviation:.2f}σ")
    print(f"Average deviation: {avg_deviation:.2f}σ")

    if max_deviation < 3:
        print("PASS: All measurements within 3σ of expected values")
    else:
        print("WARNING: Some measurements exceed 3σ deviation")

    print("=" * 60)

    return results


def main():
    """Main entry point for the angle test experiment."""
    # Setup output logging
    output_dir = "results/02_angle_test"
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    output_file_path = os.path.join(output_dir, f"angle_test_output_{timestamp}.txt")

    # Redirect output to both console and file
    original_stdout = sys.stdout

    class Tee:
        def __init__(self, *files):
            self.files = files

        def write(self, obj):
            for f in self.files:
                f.write(obj)
                f.flush()

        def flush(self):
            for f in self.files:
                f.flush()

    with open(output_file_path, "w") as f:
        sys.stdout = Tee(original_stdout, f)

        try:
            print(f"Output saved to: {output_file_path}\n")
            run_angle_test()
        finally:
            sys.stdout = original_stdout


if __name__ == "__main__":
    main()
