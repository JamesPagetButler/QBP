# experiments/02_angle_dependent/simulate.py
"""
Angle-Dependent Measurement Simulation

This experiment validates the QBP prediction that the probability of measuring
spin-up along an axis at angle theta from the particle's spin direction follows:

    P(+) = (1 + cos(theta))/2 = cos²(theta/2)

This is the "Malus's law" for spin-1/2 measurements, a fundamental test of the
quaternionic framework's ability to reproduce quantum mechanical predictions.

Physical setup:
- Prepare particle with spin at angle θ from z-axis (in x-z plane)
- Measure spin along z-axis
- Record outcome (+1 or -1)
- Repeat N times and verify statistics match QM prediction

Ground truth: research/02_angle_dependent_expected_results.md
"""

import numpy as np
import pandas as pd
import sys
import os
from datetime import datetime

# Add the project root to the Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics

# Test angles as specified in ground truth document
TEST_ANGLES = [0, 30, 45, 60, 90, 120, 135, 150, 180]  # degrees

# Number of particles per angle (1M for statistical significance, per ground truth §7.2)
NUM_PARTICLES = 1_000_000


def expected_probability(theta_deg: float) -> float:
    """
    Calculate expected P(+) for angle theta.

    From QBP axioms: P(+) = (1 + cos(θ))/2
    Equivalent to QM: P(+) = cos²(θ/2)
    """
    theta_rad = np.radians(theta_deg)
    return (1 + np.cos(theta_rad)) / 2


def calculate_sigma(p: float, n: int) -> float:
    """
    Calculate standard deviation for binomial distribution.

    σ = sqrt(n * p * (1-p))

    Note: σ = 0 for p = 0 or p = 1 (deterministic cases)
    """
    if p == 0 or p == 1:
        return 0.0
    return np.sqrt(n * p * (1 - p))


def run_simulation(num_particles: int = NUM_PARTICLES, seed: int = 42) -> pd.DataFrame:
    """
    Run angle-dependent measurement simulation for all test angles.

    Args:
        num_particles: Number of particles to simulate per angle.
        seed: Random seed for reproducibility.

    Returns:
        DataFrame with results for all angles.
    """
    print("=" * 70)
    print("ANGLE-DEPENDENT MEASUREMENT SIMULATION")
    print("Experiment 02 - Sprint 2 Phase 2")
    print("=" * 70)
    print(f"Particles per angle: {num_particles:,}")
    print(f"Test angles: {TEST_ANGLES}")
    print(f"Random seed: {seed}")
    print("-" * 70)

    # Observable: measurement along z-axis
    observable = qphysics.SPIN_Z

    results = []

    for i, angle_deg in enumerate(TEST_ANGLES):
        theta_rad = np.radians(angle_deg)

        # Create state tilted by theta from z-axis toward x-axis
        # Using the new convenience function
        state = qphysics.create_tilted_state(theta_rad)

        # Use different seed for each angle to ensure statistical independence
        angle_seed = seed + i if seed is not None else None

        # Run batch measurement
        outcomes = qphysics.measure_batch(state, observable, num_particles, angle_seed)

        # Calculate statistics
        num_up = np.sum(outcomes == 1)
        num_down = np.sum(outcomes == -1)
        measured_prob = num_up / num_particles
        expected_prob = expected_probability(angle_deg)
        sigma = calculate_sigma(expected_prob, num_particles)

        # Calculate deviation in sigma units
        if sigma > 0:
            deviation_sigma = abs(measured_prob - expected_prob) / (sigma / num_particles)
            # Actually: deviation should be in terms of count, not probability
            deviation_sigma = abs(num_up - expected_prob * num_particles) / sigma if sigma > 0 else 0
        else:
            # Deterministic case: any deviation is infinite sigma
            deviation_sigma = 0 if num_up == int(expected_prob * num_particles) else float('inf')

        # Determine pass/fail (3σ criterion)
        passed = deviation_sigma <= 3.0

        results.append({
            'angle_deg': angle_deg,
            'angle_rad': theta_rad,
            'num_particles': num_particles,
            'num_up': num_up,
            'num_down': num_down,
            'measured_prob': measured_prob,
            'expected_prob': expected_prob,
            'sigma': sigma,
            'deviation_sigma': deviation_sigma,
            'passed': passed
        })

        status = "PASS" if passed else "FAIL"
        print(f"θ = {angle_deg:3d}°: P(+) expected={expected_prob:.4f}, "
              f"measured={measured_prob:.6f}, deviation={deviation_sigma:.2f}σ [{status}]")

    print("-" * 70)

    df = pd.DataFrame(results)
    return df


def save_results(df: pd.DataFrame, output_dir: str = "results/02_angle_dependent") -> str:
    """
    Save simulation results to timestamped CSV file.

    Args:
        df: DataFrame with simulation results.
        output_dir: Directory for output files.

    Returns:
        Path to saved CSV file.
    """
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    csv_path = os.path.join(output_dir, f"simulation_results_{timestamp}.csv")
    df.to_csv(csv_path, index=False)
    return csv_path


def print_summary(df: pd.DataFrame):
    """Print summary of simulation results."""
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    all_passed = df['passed'].all()
    max_deviation = df['deviation_sigma'].replace([np.inf], np.nan).max()

    print(f"\nTotal angles tested: {len(df)}")
    print(f"All tests passed: {'YES' if all_passed else 'NO'}")
    print(f"Maximum deviation: {max_deviation:.2f}σ")

    # Check edge cases specifically
    edge_cases = df[df['angle_deg'].isin([0, 90, 180])]
    print("\nEdge case verification:")
    for _, row in edge_cases.iterrows():
        angle = row['angle_deg']
        expected = row['expected_prob']
        measured = row['measured_prob']
        print(f"  θ={angle:3d}°: expected P(+)={expected:.1f}, measured={measured:.6f}")

    if all_passed:
        print("\n" + "=" * 70)
        print("EXPERIMENT PASSED: All angles within 3σ of QM prediction")
        print("QBP framework correctly predicts P(+) = cos²(θ/2)")
        print("=" * 70)
    else:
        print("\n" + "=" * 70)
        print("EXPERIMENT FAILED: Some angles exceed 3σ deviation")
        failed = df[~df['passed']]
        for _, row in failed.iterrows():
            print(f"  FAILED: θ={row['angle_deg']}° ({row['deviation_sigma']:.2f}σ)")
        print("=" * 70)


def main():
    """Main entry point for the simulation."""
    print(f"\nStarting simulation at {datetime.now().isoformat()}\n")

    # Run simulation
    df = run_simulation()

    # Save results
    csv_path = save_results(df)
    print(f"\nResults saved to: {csv_path}")

    # Print summary
    print_summary(df)

    # Return exit code based on pass/fail
    return 0 if df['passed'].all() else 1


if __name__ == "__main__":
    sys.exit(main())
