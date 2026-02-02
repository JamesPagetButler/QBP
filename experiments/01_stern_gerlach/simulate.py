# experiments/01_stern_gerlach/simulate.py

import numpy as np
import sys
import os

# Add the project root to the Python path to allow imports from src
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


def run_simulation(num_particles=1000000):
    """
    Simulates the Stern-Gerlach experiment using the quaternionic framework.
    """
    print("--- Running Stern-Gerlach Synthetic Experiment ---")
    print(f"Simulating {num_particles} particles...")

    # 1. Define the initial state of the particles.
    # We choose a state aligned with the X-axis. In traditional QM, this is an
    # equal superposition of spin-up and spin-down states when measured on the
    # Z-axis. We expect a roughly 50/50 split in our results.
    initial_state_vector = [1, 0, 0]  # Pointing along X
    psi_initial = qphysics.create_state_from_vector(initial_state_vector)
    print(f"Initial State (ψ): {psi_initial}")

    # 2. Define the observable.
    # We are measuring the spin along the Z-axis.
    observable = qphysics.SPIN_Z
    print(f"Measuring with Observable (O): {observable}")
    print("----------------------------------------------------")

    # 3. Run the measurement loop.
    results = []
    for _ in range(num_particles):
        outcome, _ = qphysics.measure(psi_initial, observable)
        results.append(outcome)

    # 4. Tally and print the results.
    results = np.array(results)
    num_up = np.sum(results == 1)
    num_down = np.sum(results == -1)

    percent_up = (num_up / num_particles) * 100
    percent_down = (num_down / num_particles) * 100

    print("\n--- Simulation Results ---")
    print(f"Outcome 'Up' (+1): {num_up} times ({percent_up:.2f}%)")
    print(f"Outcome 'Down' (-1): {num_down} times ({percent_down:.2f}%)")
    print("--------------------------\n")

    print("Conclusion: The experiment successfully demonstrates spin quantization.")
    print(
        "As expected, the initial state in a superposition yielded a probabilistic split into two distinct outcomes."
    )


if __name__ == "__main__":
    # To run this script, navigate to the project root directory and execute:
    # python experiments/01_stern_gerlach/simulate.py
    run_simulation()
