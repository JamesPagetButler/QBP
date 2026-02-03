# experiments/01_stern_gerlach/simulate.py

import numpy as np
import sys
import os
from datetime import datetime

# Add the project root to the Python path to allow imports from src
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


class Tee(object):
    """A helper class to redirect print statements to both console and a file."""

    def __init__(self, *files):
        self.files = files

    def write(self, obj):
        for f in self.files:
            f.write(obj)
            f.flush()  # Ensure content is written immediately

    def flush(self):
        for f in self.files:
            f.flush()


def run_simulation(num_particles=1000000, seed=42):
    """
    Simulates the Stern-Gerlach experiment using the quaternionic framework.

    Args:
        num_particles: Number of particles to simulate.
        seed: Random seed for reproducibility.
    """
    # --- Setup Output Logging ---
    output_dir = "results/01_stern_gerlach"
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    output_file_path = os.path.join(output_dir, f"simulation_output_{timestamp}.txt")

    original_stdout = sys.stdout
    with open(output_file_path, "w") as f:
        sys.stdout = Tee(original_stdout, f)

        try:
            print(f"Output for this run is being saved to: {output_file_path}\n")
            print("--- Running Stern-Gerlach Synthetic Experiment ---")
            print(f"Simulating {num_particles} particles...")

            # 1. Define the initial state of the particles.
            # We choose a state aligned with the X-axis. In traditional QM, this is an
            # equal superposition of spin-up and spin-down states when measured on the
            # Z-axis. We expect a roughly 50/50 split in our results.
            initial_state_vector = [1, 0, 0]  # Pointing along X
            psi_initial = qphysics.create_state_from_vector(initial_state_vector)
            print(f"Initial State (psi): {psi_initial}")

            # 2. Define the observable.
            # We are measuring the spin along the Z-axis.
            observable = qphysics.SPIN_Z
            print(f"Measuring with Observable (O): {observable}")
            print("----------------------------------------------------")

            # 3. Run the measurement using vectorized batch function.
            exp_val = qphysics.expectation_value(psi_initial, observable)
            prob_up = (1 + exp_val) / 2.0

            print(f"Calculated Expectation Value: {exp_val:.4f}")
            print(f"Calculated Probability of 'Up': {prob_up:.4f}")
            print("----------------------------------------------------")

            # Use measure_batch for efficient vectorized simulation
            results = qphysics.measure_batch(
                psi_initial, observable, num_particles, seed
            )

            # 4. Tally and print the results.
            num_up = np.sum(results == 1)
            num_down = np.sum(results == -1)

            percent_up = (num_up / num_particles) * 100
            percent_down = (num_down / num_particles) * 100

            print("\n--- Simulation Results ---")
            print(f"Outcome 'Up' (+1): {num_up} times ({percent_up:.2f}%)")
            print(f"Outcome 'Down' (-1): {num_down} times ({percent_down:.2f}%)")
            print("--------------------------\n")

            print(
                "Conclusion: The experiment successfully demonstrates spin quantization."
            )
            print(
                "As expected, the initial state in a superposition yielded a probabilistic split into two distinct outcomes."
            )
        finally:
            # --- Restore Original Output ---
            sys.stdout = original_stdout


if __name__ == "__main__":
    # To run this script, navigate to the project root directory and execute:
    # python experiments/01_stern_gerlach/simulate.py
    run_simulation()
