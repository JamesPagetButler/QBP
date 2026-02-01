"""
Quaternion Rotation Visualization

Demonstrates quaternion-based rotation in 3D using vpython.
Opens an interactive browser window showing:
- A coordinate frame (steampunk themed: Crimson/Verdigris/Teal = XYZ)
- A brass arrow being rotated by a quaternion
- Real-time animation of the rotation

Physical connection: Quaternions encode 3D rotations without gimbal lock,
fundamental to representing spin states in our QBP formalism.

Run: python src/viz/quaternion_rotation.py
"""

import numpy as np
from vpython import canvas, vector, arrow, sphere, ring, rate, label

# Import our design system
from .theme import COLORS, PALETTE


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
    v_quat = np.array([0, v[0], v[1], v[2]])
    q_conj = quaternion_conjugate(q)
    result = quaternion_multiply(quaternion_multiply(q, v_quat), q_conj)
    return result[1:4]


def axis_angle_to_quaternion(axis, angle_rad):
    """Convert axis-angle to quaternion."""
    axis = np.array(axis, dtype=float)
    axis = axis / np.linalg.norm(axis)
    w = np.cos(angle_rad / 2)
    xyz = axis * np.sin(angle_rad / 2)
    return np.array([w, xyz[0], xyz[1], xyz[2]])


def create_scene(dark_mode=False):
    """Create the vpython scene with steampunk-themed coordinate frame."""

    # Choose background based on mode
    if dark_mode:
        bg = COLORS.DARK_SLATE.vpython
        text_color = COLORS.IVORY.vpython
    else:
        bg = COLORS.PARCHMENT.vpython
        text_color = COLORS.SHADOW.vpython

    scene = canvas(
        title='<b style="font-family: Georgia, serif;">⚙ Quaternion Rotation Visualization ⚙</b>',
        width=900,
        height=700,
        center=vector(0, 0, 0),
        background=bg
    )
    scene.caption = "\n<b>Controls:</b> Drag to rotate | Scroll to zoom | Ctrl+C to exit\n\n"

    # Coordinate frame with steampunk colors
    axis_length = 2
    axis_thickness = 0.05

    # X-axis: Crimson (heat, energy)
    arrow(pos=vector(0,0,0), axis=vector(axis_length,0,0),
          color=PALETTE.AXIS_X.vpython, shaftwidth=axis_thickness)
    label(pos=vector(axis_length+0.3,0,0), text='X', color=PALETTE.AXIS_X.vpython,
          box=False, opacity=0, height=16)

    # Y-axis: Verdigris (patina, growth)
    arrow(pos=vector(0,0,0), axis=vector(0,axis_length,0),
          color=PALETTE.AXIS_Y.vpython, shaftwidth=axis_thickness)
    label(pos=vector(0,axis_length+0.3,0), text='Y', color=PALETTE.AXIS_Y.vpython,
          box=False, opacity=0, height=16)

    # Z-axis: Teal (depth, mystery)
    arrow(pos=vector(0,0,0), axis=vector(0,0,axis_length),
          color=PALETTE.AXIS_Z.vpython, shaftwidth=axis_thickness)
    label(pos=vector(0,0,axis_length+0.3), text='Z', color=PALETTE.AXIS_Z.vpython,
          box=False, opacity=0, height=16)

    return scene, text_color


def visualize_rotation(axis=[0, 0, 1], angle_degrees=360, duration=4.0, dark_mode=False):
    """
    Visualize a quaternion rotation with steampunk aesthetics.

    Parameters:
        axis: Rotation axis [x, y, z]
        angle_degrees: Total rotation angle
        duration: Animation duration in seconds
        dark_mode: Use dark background (default: False)
    """
    scene, text_color = create_scene(dark_mode)

    # Object to rotate - a BRASS arrow (our primary color)
    obj = arrow(
        pos=vector(0, 0, 0),
        axis=vector(1.5, 0, 0),
        color=COLORS.BRASS.vpython,
        shaftwidth=0.12
    )

    # Small sphere at arrow tip for visual clarity
    tip = sphere(
        pos=vector(1.5, 0, 0),
        radius=0.08,
        color=COLORS.GOLD.vpython,
        emissive=True  # Glowing effect
    )

    # Show rotation axis as a steel ring
    axis_norm = np.array(axis) / np.linalg.norm(axis)
    ring(
        pos=vector(0, 0, 0),
        axis=vector(axis_norm[0], axis_norm[1], axis_norm[2]),
        radius=1.5,
        thickness=0.02,
        color=COLORS.STEEL.vpython
    )

    # Info display with amber glow effect
    info = label(
        pos=vector(0, -2.5, 0),
        text=f'Axis: [{axis[0]}, {axis[1]}, {axis[2]}]\nAngle: 0°',
        color=text_color,
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

        current_angle = (i / frames) * angle_rad
        current_degrees = (i / frames) * angle_degrees

        q = axis_angle_to_quaternion(axis, current_angle)
        rotated = rotate_vector_by_quaternion(initial_vec, q)

        # Update arrow
        obj.axis = vector(rotated[0], rotated[1], rotated[2])

        # Update glowing tip
        tip.pos = vector(rotated[0], rotated[1], rotated[2])

        # Update info with quaternion display
        info.text = (
            f'Axis: [{axis[0]:.1f}, {axis[1]:.1f}, {axis[2]:.1f}]\n'
            f'Angle: {current_degrees:.1f}°\n'
            f'q = ({q[0]:.3f}, {q[1]:.3f}i, {q[2]:.3f}j, {q[3]:.3f}k)'
        )

    # Keep scene open
    while True:
        rate(30)


def demo_menu():
    """Show demo options with steampunk flair."""
    print("\n" + "=" * 50)
    print("  ⚙  QUATERNION ROTATION DEMOS  ⚙")
    print("=" * 50)
    print("\n  1. Z-axis rotation (default)")
    print("  2. X-axis rotation")
    print("  3. Y-axis rotation")
    print("  4. Diagonal axis [1,1,1]")
    print("  5. Custom axis")
    print("  6. Toggle dark mode\n")

    choice = input("  Select [1-6]: ").strip() or "1"

    demos = {
        "1": ([0, 0, 1], "Z-axis", False),
        "2": ([1, 0, 0], "X-axis", False),
        "3": ([0, 1, 0], "Y-axis", False),
        "4": ([1, 1, 1], "Diagonal", False),
    }

    if choice in demos:
        axis, name, dark = demos[choice]
        print(f"\n  Starting {name} rotation...")
        return axis, dark
    elif choice == "5":
        try:
            x = float(input("    X component: ") or "0")
            y = float(input("    Y component: ") or "0")
            z = float(input("    Z component: ") or "1")
            return [x, y, z], False
        except ValueError:
            print("  Invalid input, using Z-axis")
            return [0, 0, 1], False
    elif choice == "6":
        print("\n  Dark mode enabled. Select rotation:")
        sub = input("    Axis [1=Z, 2=X, 3=Y, 4=Diagonal]: ").strip() or "1"
        axes = {"1": [0,0,1], "2": [1,0,0], "3": [0,1,0], "4": [1,1,1]}
        return axes.get(sub, [0,0,1]), True
    else:
        return [0, 0, 1], False


if __name__ == '__main__':
    # When running directly, fix import path
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent.parent))

    from viz.theme import show_palette
    show_palette()

    axis, dark_mode = demo_menu()

    print("\n  Opening browser...")
    print("  Press Ctrl+C to exit\n")

    visualize_rotation(
        axis=axis,
        angle_degrees=360,
        duration=4.0,
        dark_mode=dark_mode
    )
