# qphysics.py
# The computational heart of our quaternion-based physics project.

from __future__ import annotations

import numpy as np
import quaternion

# --- Axiom 1: The Quaternionic State ---


def create_state(a: float, b: float, c: float, d: float) -> np.quaternion:
    """
    Creates a normalized quaternionic state from four components, enforcing the
    unit quaternion constraint of Axiom 1.

    Args:
        a: The scalar component.
        b: The 'i' component.
        c: The 'j' component.
        d: The 'k' component.

    Returns:
        A normalized quaternion representing the state psi.
    """
    q = np.quaternion(a, b, c, d)
    norm = q.norm()
    if norm == 0:
        # Default to a neutral state if norm is zero to avoid division errors
        return np.quaternion(1, 0, 0, 0)
    return q / norm


def create_state_from_vector(vec: list | np.ndarray) -> np.quaternion:
    """
    A user-friendly helper to create a quaternionic state aligned with a 3D vector.
    The scalar part is set to 0, and the vector part is normalized. This is useful
    for representing pure spin states.

    Args:
        vec: A 3-D vector [x, y, z].

    Returns:
        A normalized quaternion representing the state psi.
    """
    if len(vec) != 3:
        raise ValueError("Input vector must be 3-dimensional [x, y, z]")
    return create_state(0, vec[0], vec[1], vec[2])


def get_state_vector(psi: np.quaternion) -> np.ndarray:
    """
    Utility function to get the vector part of a quaternionic state.

    Args:
        psi: The quaternionic state.

    Returns:
        The 3D vector part [x, y, z].
    """
    return quaternion.as_vector_part(psi)


# --- Axiom 2: Quaternionic Observables ---


def create_observable(vec: list | np.ndarray) -> np.quaternion:
    """
    Creates a pure quaternion operator to represent an observable, as per Axiom 2.

    Args:
        vec: A 3-D vector [x, y, z] defining the observable axis.

    Returns:
        A pure quaternion representing the observable O.
    """
    if len(vec) != 3:
        raise ValueError("Input vector must be 3-dimensional [x, y, z]")
    return np.quaternion(0, vec[0], vec[1], vec[2])


# Pre-defined observables for convenience, mapping to the Pauli matrices
SPIN_X = np.quaternion(0, 1, 0, 0)  # Corresponds to i
SPIN_Y = np.quaternion(0, 0, 1, 0)  # Corresponds to j
SPIN_Z = np.quaternion(0, 0, 0, 1)  # Corresponds to k


# --- Axiom 3: Quaternionic Evolution ---


def evolve_state(
    psi_initial: np.quaternion, hamiltonian: np.quaternion, time: float
) -> np.quaternion:
    """
    Evolves a state psi through time t under a given Hamiltonian H, as per Axiom 3.

    Args:
        psi_initial: The initial state of the system, psi(0).
        hamiltonian: The Hamiltonian operator H, which must be a
                     pure quaternion (observable).
        time: The duration of the evolution, t.

    Returns:
        The final state of the system, psi(t).
    """
    if hamiltonian.w != 0:
        raise ValueError(
            "Hamiltonian must be a pure quaternion (scalar part must be zero)."
        )

    # The evolution operator U = exp(-Ht)
    # For a pure quaternion H, this is a rotation.
    evolution_operator = np.exp(-hamiltonian * time)

    # Apply the evolution operator to the initial state
    psi_final = evolution_operator * psi_initial

    return psi_final


# --- Measurement Postulate ---


def expectation_value(psi: np.quaternion, observable: np.quaternion) -> float:
    """
    Calculates the expectation value for a given observable and state.
    This is defined as the dot product of the vector parts of the state
    and the observable.

    Args:
        psi: The quaternionic state.
        observable: The pure quaternion observable.

    Returns:
        The expectation value, a scalar between -1 and 1.
    """
    if observable.w != 0:
        raise ValueError("Observable must be a pure quaternion.")

    # Normalize the observable's vector part to be safe
    obs_vec = quaternion.as_vector_part(observable)
    obs_norm = np.linalg.norm(obs_vec)
    if obs_norm == 0:
        return 0.0

    # The state psi is assumed to have a non-zero vector part
    psi_vec = get_state_vector(psi)

    return float(np.dot(psi_vec, obs_vec / obs_norm))


def measure(
    psi: np.quaternion, observable: np.quaternion, seed: int | None = None
) -> tuple[int, np.quaternion]:
    """
    Performs a measurement of a state against an observable.

    This function is probabilistic. It calculates the probabilities of "up" (+1)
    and "down" (-1) outcomes, then "rolls the dice" to collapse the state into
    one of the two corresponding eigenstates.

    Args:
        psi: The quaternionic state to be measured.
        observable: The pure quaternion observable.
        seed: Optional random seed for reproducibility.

    Returns:
        A tuple containing the outcome (+1 or -1) and the new,
        collapsed state (a pure quaternion aligned or anti-aligned
        with the observable).
    """
    rng = np.random.default_rng(seed)
    exp_val = expectation_value(psi, observable)

    # Probability of measuring the "up" state (+1)
    prob_up = (1 + exp_val) / 2.0

    # "Roll the dice"
    if rng.random() < prob_up:
        # Outcome is "up" (+1), collapse state to be aligned with observable
        collapsed_state = create_state_from_vector(
            quaternion.as_vector_part(observable)
        )
        return +1, collapsed_state
    else:
        # Outcome is "down" (-1), collapse state to be anti-aligned
        collapsed_state = create_state_from_vector(
            -quaternion.as_vector_part(observable)
        )
        return -1, collapsed_state


def measure_batch(
    psi: np.quaternion, observable: np.quaternion, n: int, seed: int | None = None
) -> np.ndarray:
    """
    Perform n measurements in a vectorized manner.

    This is more efficient than calling measure() n times when you only need
    the measurement outcomes (not the collapsed states).

    Args:
        psi: The quaternionic state to be measured.
        observable: The pure quaternion observable.
        n: Number of measurements to perform.
        seed: Optional random seed for reproducibility.

    Returns:
        An array of n measurement outcomes (+1 or -1).
    """
    rng = np.random.default_rng(seed)
    exp_val = expectation_value(psi, observable)
    prob_up = (1 + exp_val) / 2.0
    randoms = rng.random(n)
    return np.where(randoms < prob_up, 1, -1)
