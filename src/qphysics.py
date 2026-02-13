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
    # Note: q.norm() returns |q|^2, so we use np.abs(q) for the actual norm |q|
    abs_q = np.abs(q)
    if abs_q == 0:
        # Default to a neutral state if norm is zero to avoid division errors
        return np.quaternion(1, 0, 0, 0)
    return q / abs_q


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


# --- Rotation Operations ---


def create_rotation(theta: float, axis: list | np.ndarray) -> np.quaternion:
    """
    Create a rotation quaternion for rotation by angle theta about the given axis.

    The rotation quaternion uses the half-angle formula:
        q = cos(θ/2) + sin(θ/2) * (axis)

    This reflects the SU(2) double-cover of SO(3): rotating a spin state by 2π
    returns -ψ, not +ψ. A full 4π rotation is needed to return to the original state.

    Args:
        theta: Rotation angle in radians.
        axis: A 3D unit vector [x, y, z] defining the rotation axis.

    Returns:
        A unit quaternion representing the rotation.
    """
    if len(axis) != 3:
        raise ValueError("Axis must be 3-dimensional [x, y, z]")

    # Normalize the axis
    axis = np.array(axis, dtype=float)
    norm = np.linalg.norm(axis)
    if norm == 0:
        raise ValueError("Rotation axis cannot be zero vector")
    axis = axis / norm

    # Half-angle formula: q = cos(θ/2) + sin(θ/2) * axis
    half_theta = theta / 2.0
    w = np.cos(half_theta)
    xyz = np.sin(half_theta) * axis

    return np.quaternion(w, xyz[0], xyz[1], xyz[2])


def rotate_observable(
    observable: np.quaternion, theta: float, axis: list | np.ndarray
) -> np.quaternion:
    """
    Rotate an observable (pure quaternion) by angle theta about the given axis.

    Uses the quaternion rotation formula: O' = q * O * q⁻¹

    Physical meaning: This rotates the measurement axis in 3D space.
    For example, rotating SPIN_Z by θ about the y-axis gives a measurement
    axis tilted θ from z toward x.

    Args:
        observable: The pure quaternion observable to rotate.
        theta: Rotation angle in radians.
        axis: A 3D unit vector defining the rotation axis.

    Returns:
        The rotated observable (still a pure quaternion).
    """
    if observable.w != 0:
        raise ValueError("Observable must be a pure quaternion.")

    q = create_rotation(theta, axis)
    q_conj = q.conjugate()

    # O' = q * O * q⁻¹ (for unit quaternion, q⁻¹ = q*)
    rotated = q * observable * q_conj

    # The result should be pure (real part ≈ 0), but clean up numerical noise
    return np.quaternion(0, rotated.x, rotated.y, rotated.z)


def rotate_state(
    psi: np.quaternion, theta: float, axis: list | np.ndarray
) -> np.quaternion:
    """
    Rotate a state quaternion by angle theta about the given axis.

    Uses the same rotation formula as observables: ψ' = q * ψ * q⁻¹

    This is equivalent to physically rotating the spin preparation apparatus.

    Args:
        psi: The quaternionic state to rotate.
        theta: Rotation angle in radians.
        axis: A 3D unit vector defining the rotation axis.

    Returns:
        The rotated state (normalized pure quaternion).
    """
    q = create_rotation(theta, axis)
    q_conj = q.conjugate()

    rotated = q * psi * q_conj

    # Ensure result is pure and normalized
    return create_state(0, rotated.x, rotated.y, rotated.z)


def create_tilted_state(theta: float) -> np.quaternion:
    """
    Create a spin state tilted by angle theta from the z-axis toward the x-axis.

    This is a convenience function for angle-dependent measurement experiments.
    The state lies in the x-z plane:
        ψ(θ) = sin(θ)·i + cos(θ)·k

    Physical meaning:
        θ = 0°   → spin along +z (fully up)
        θ = 90°  → spin along +x (orthogonal to z)
        θ = 180° → spin along -z (fully down)

    Args:
        theta: Tilt angle in radians from the z-axis.

    Returns:
        A pure unit quaternion representing the tilted state.
    """
    return create_state(0, np.sin(theta), 0, np.cos(theta))


def create_general_state(theta: float, phi: float) -> np.quaternion:
    """
    Create a spin state pointing in an arbitrary direction on the Bloch sphere.

    Generalizes create_tilted_state to full 3D using spherical coordinates:
        ψ(θ,φ) = sin(θ)cos(φ)·i + sin(θ)sin(φ)·j + cos(θ)·k

    Physical meaning:
        θ: polar angle from z-axis (0 to π)
        φ: azimuthal angle in xy-plane from x-axis (0 to 2π)

    Special cases:
        φ = 0 recovers create_tilted_state(theta) (xz-plane)
        θ = 0 gives spin-up along z regardless of φ
        θ = π gives spin-down along z regardless of φ

    Args:
        theta: Polar angle from z-axis in radians.
        phi: Azimuthal angle in xy-plane in radians.

    Returns:
        A pure unit quaternion representing the state.
    """
    return create_state(
        0,
        np.sin(theta) * np.cos(phi),
        np.sin(theta) * np.sin(phi),
        np.cos(theta),
    )


def angle_between_states(psi: np.quaternion, observable: np.quaternion) -> float:
    """
    Calculate the angle between a state and an observable direction.

    For pure unit quaternions, this is the angle γ such that:
        cos(γ) = vecDot(ψ, O) = ⟨O⟩

    This angle satisfies: P(+) = cos²(γ/2)

    Args:
        psi: A pure unit quaternion state.
        observable: A pure unit quaternion observable.

    Returns:
        The angle γ in radians between the two directions.
    """
    dot = expectation_value(psi, observable)
    # Clamp to [-1, 1] for numerical safety
    dot = max(-1.0, min(1.0, dot))
    return float(np.arccos(dot))
