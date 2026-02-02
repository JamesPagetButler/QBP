# qphysics.py
# The computational heart of our quaternion-based physics project.

import numpy as np
import quaternion

# --- Axiom 1: The Quaternionic State ---


def create_state(a, b, c, d):
    """
    Creates a normalized quaternionic state from four components, enforcing the
    unit quaternion constraint of Axiom 1.

    Args:
        a (float): The scalar component.
        b (float): The 'i' component.
        c (float): The 'j' component.
        d (float): The 'k' component.

    Returns:
        np.quaternion: A normalized quaternion representing the state ψ.
    """
    q = np.quaternion(a, b, c, d)
    norm = q.norm()
    if norm == 0:
        # Default to a neutral state if norm is zero to avoid division errors
        return np.quaternion(1, 0, 0, 0)
    return q / norm


def create_state_from_vector(vec):
    """
    A user-friendly helper to create a quaternionic state aligned with a 3D vector.
    The scalar part is set to 0, and the vector part is normalized. This is useful
    for representing pure spin states.

    Args:
        vec (list or np.array): A 3-D vector [x, y, z].

    Returns:
        np.quaternion: A normalized quaternion representing the state ψ.
    """
    if len(vec) != 3:
        raise ValueError("Input vector must be 3-dimensional [x, y, z]")
    return create_state(0, vec[0], vec[1], vec[2])


def get_state_vector(psi):
    """
    Utility function to get the vector part of a quaternionic state.

    Args:
        psi (np.quaternion): The quaternionic state.

    Returns:
        np.array: The 3D vector part [x, y, z].
    """
    return quaternion.as_vector_part(psi)


# --- Axiom 2: Quaternionic Observables ---


def create_observable(vec):
    """
    Creates a pure quaternion operator to represent an observable, as per Axiom 2.

    Args:
        vec (list or np.array): A 3-D vector [x, y, z] defining the observable axis.

    Returns:
        np.quaternion: A pure quaternion representing the observable O.
    """
    if len(vec) != 3:
        raise ValueError("Input vector must be 3-dimensional [x, y, z]")
    return np.quaternion(0, vec[0], vec[1], vec[2])


# Pre-defined observables for convenience, mapping to the Pauli matrices
SPIN_X = np.quaternion(0, 1, 0, 0)  # Corresponds to i
SPIN_Y = np.quaternion(0, 0, 1, 0)  # Corresponds to j
SPIN_Z = np.quaternion(0, 0, 0, 1)  # Corresponds to k


# --- Axiom 3: Quaternionic Evolution ---


def evolve_state(psi_initial, hamiltonian, time):
    """
    Evolves a state ψ through time t under a given Hamiltonian H, as per Axiom 3.

    Args:
        psi_initial (np.quaternion): The initial state of the system, ψ(0).
        hamiltonian (np.quaternion): The Hamiltonian operator H, which must be a
                                     pure quaternion (observable).
        time (float): The duration of the evolution, t.

    Returns:
        np.quaternion: The final state of the system, ψ(t).
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


def expectation_value(psi, observable):
    """
    Calculates the expectation value for a given observable and state.
    This is defined as the dot product of the vector parts of the state
    and the observable.

    Args:
        psi (np.quaternion): The quaternionic state.
        observable (np.quaternion): The pure quaternion observable.

    Returns:
        float: The expectation value, a scalar between -1 and 1.
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

    return np.dot(psi_vec, obs_vec / obs_norm)


def measure(psi, observable):
    """
    Performs a measurement of a state against an observable.

    This function is probabilistic. It calculates the probabilities of "up" (+1)
    and "down" (-1) outcomes, then "rolls the dice" to collapse the state into
    one of the two corresponding eigenstates.

    Args:
        psi (np.quaternion): The quaternionic state to be measured.
        observable (np.quaternion): The pure quaternion observable.

    Returns:
        tuple: A tuple containing the outcome (+1 or -1) and the new,
               collapsed state (a pure quaternion aligned or anti-aligned
               with the observable).
    """
    exp_val = expectation_value(psi, observable)

    # Probability of measuring the "up" state (+1)
    prob_up = (1 + exp_val) / 2.0

    # "Roll the dice"
    if np.random.rand() < prob_up:
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
