"""
Quaternion Rotation Visualization

Demonstrates quaternion-based rotation in 3D using vpython.
Opens an interactive browser window showing:
- A coordinate frame (RGB = XYZ)
- An arrow being rotated by a quaternion
- Real-time animation of the rotation

Physical connection: Quaternions encode 3D rotations without gimbal lock,
fundamental to representing spin states in our QBP formalism.

Run: python src/viz/quaternion_rotation.py
"""

import numpy as np
from vpython import (
    canvas, vector, arrow, sphere, ring, rate,
    color, label, slider, wtext, sqrt, cos, sin
)


def quaternion_multiply(q1, q2):
    """Multiply two quaternions q = (w, x, y, z)."""
    w1, x1, y1, z1 = q1
    w2, x2, y2, z2 = q2
    return np.array([
        w1*w2 - x1*x2 - y1*y2 - z1*z2,
        w1*x2 + x1*w2 + y1*z2 - z1*y2,
        w1*y2 - x1*z2 + y1*w2 + z1*x2,
        w1*z2 + x1*y2 - y1*x2 + z1*w2
    ])


def quaternion_conjugate(q):
    """Conjugate of quaternion q = (w, x, y, z)."""
    return np.array([q[0], -q[1], -q[2], -q[3]])


def rotate_vector_by_quaternion(v, q):
    """Rotate vector v by quaternion q using q * v * q^-1."""
    # Represent vector as pure quaternion (0, vx, vy, vz)
    v_quat = np.array([0, v[0], v[1], v[2]])
    q_conj = quaternion_conjugate(q)

    # q * v * q^-1
    result = quaternion_multiply(quaternion_multiply(q, v_quat), q_conj)
    return result[1:4]  # Return vector part


def axis_angle_to_quaternion(axis, angle_rad):
    """Convert axis-angle to quaternion."""
    axis = np.array(axis, dtype=float)
    axis = axis / np.linalg.norm(axis)  # Normalize

    w = np.cos(angle_rad / 2)
    xyz = axis * np.sin(angle_rad / 2)
    return np.array([w, xyz[0], xyz[1], xyz[2]])


def create_scene():
    """Create the vpython scene with coordinate frame."""
    scene = canvas(
        title='<b>Quaternion Rotation Visualization</b>',
        width=900,
        height=700,
        center=vector(0, 0, 0),
        background=vector(0.95, 0.95, 0.95)  # Light gray - easier on eyes
    )
    scene.caption = "\n<b>Controls:</b> Drag to rotate | Scroll to zoom | Ctrl+C to exit\n\n"

    # Coordinate frame (RGB = XYZ convention)
    axis_length = 2
    axis_thickness = 0.05

    # X-axis (red)
    arrow(pos=vector(0,0,0), axis=vector(axis_length,0,0),
          color=color.red, shaftwidth=axis_thickness)
    label(pos=vector(axis_length+0.3,0,0), text='X', color=color.red,
          box=False, opacity=0)

    # Y-axis (green)
    arrow(pos=vector(0,0,0), axis=vector(0,axis_length,0),
          color=color.green, shaftwidth=axis_thickness)
    label(pos=vector(0,axis_length+0.3,0), text='Y', color=color.green,
          box=False, opacity=0)

    # Z-axis (blue)
    arrow(pos=vector(0,0,0), axis=vector(0,0,axis_length),
          color=color.blue, shaftwidth=axis_thickness)
    label(pos=vector(0,0,axis_length+0.3), text='Z', color=color.blue,
          box=False, opacity=0)

    return scene


def visualize_rotation(axis=[0, 0, 1], angle_degrees=360, duration=4.0):
    """
    Visualize a quaternion rotation.

    Parameters:
        axis: Rotation axis [x, y, z]
        angle_degrees: Total rotation angle
        duration: Animation duration in seconds
    """
    scene = create_scene()

    # Object to rotate - a yellow arrow pointing in +X initially
    obj = arrow(
        pos=vector(0, 0, 0),
        axis=vector(1.5, 0, 0),
        color=color.orange,
        shaftwidth=0.1
    )

    # Show rotation axis
    axis_norm = np.array(axis) / np.linalg.norm(axis)
    ring(
        pos=vector(0, 0, 0),
        axis=vector(axis_norm[0], axis_norm[1], axis_norm[2]),
        radius=1.5,
        thickness=0.02,
        color=color.gray(0.7)
    )

    # Info display
    info = label(
        pos=vector(0, -2.5, 0),
        text=f'Axis: [{axis[0]}, {axis[1]}, {axis[2]}]\nAngle: 0°',
        color=color.black,
        box=False,
        height=14
    )

    # Animation parameters
    fps = 60
    frames = int(duration * fps)
    angle_rad = np.radians(angle_degrees)
    initial_vec = np.array([1.5, 0, 0])

    # Animation loop
    for i in range(frames):
        rate(fps)

        # Current angle
        current_angle = (i / frames) * angle_rad
        current_degrees = (i / frames) * angle_degrees

        # Create quaternion for current rotation
        q = axis_angle_to_quaternion(axis, current_angle)

        # Rotate the vector
        rotated = rotate_vector_by_quaternion(initial_vec, q)

        # Update visualization
        obj.axis = vector(rotated[0], rotated[1], rotated[2])

        # Update info
        info.text = (
            f'Axis: [{axis[0]:.1f}, {axis[1]:.1f}, {axis[2]:.1f}]\n'
            f'Angle: {current_degrees:.1f}°\n'
            f'q = ({q[0]:.3f}, {q[1]:.3f}i, {q[2]:.3f}j, {q[3]:.3f}k)'
        )

    # Keep scene open
    while True:
        rate(30)


def demo_menu():
    """Show demo options."""
    print("\nQuaternion Rotation Demos:")
    print("  1. Z-axis rotation (default)")
    print("  2. X-axis rotation")
    print("  3. Y-axis rotation")
    print("  4. Diagonal axis [1,1,1]")
    print("  5. Custom axis\n")

    choice = input("Select demo [1-5]: ").strip() or "1"

    demos = {
        "1": ([0, 0, 1], "Z-axis"),
        "2": ([1, 0, 0], "X-axis"),
        "3": ([0, 1, 0], "Y-axis"),
        "4": ([1, 1, 1], "Diagonal"),
    }

    if choice in demos:
        axis, name = demos[choice]
        print(f"\nStarting {name} rotation...")
        return axis
    elif choice == "5":
        try:
            x = float(input("  X component: ") or "0")
            y = float(input("  Y component: ") or "0")
            z = float(input("  Z component: ") or "1")
            return [x, y, z]
        except ValueError:
            print("Invalid input, using Z-axis")
            return [0, 0, 1]
    else:
        return [0, 0, 1]


if __name__ == '__main__':
    print("=" * 50)
    print("  QBP Quaternion Rotation Visualization")
    print("=" * 50)

    axis = demo_menu()

    print("\nOpening browser...")
    print("Press Ctrl+C to exit\n")

    visualize_rotation(
        axis=axis,
        angle_degrees=360,
        duration=4.0
    )
