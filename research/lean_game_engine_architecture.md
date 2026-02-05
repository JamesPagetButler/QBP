# Research: Game Engine Architecture for a Lean-Driven Physics Laboratory

This document investigates the feasibility of using a real-time game engine as an interactive 3D visualization front-end, driven by a formal proof assistant (Lean 4). It builds upon the previous research (`lean_golang_architecture.md`) and proposes a more powerful and practical architecture.

---

## 1. Executive Summary

**Conclusion:** Using a game engine is not only **feasible but highly recommended** over building a custom renderer in Go.

*   **The Right Tool for the Job:** Game engines are specialized for creating real-time, interactive 3D environments. Leveraging a mature game engine is far more efficient than writing low-level graphics code from scratch.
*   **Recommended Engine: Godot:** The Godot Engine is the ideal candidate due to its open-source nature (MIT license), excellent command-line support, and simple yet powerful scripting language (GDScript).
*   **Recommended Architecture: The Lean + Godot Hybrid Model:** As with the Go proposal, a hybrid model where Lean computes the core physics and sends high-level commands to the Godot application for visualization is the most robust and performant approach.

---

## 2. The Vision: The "Lean-Driven Physics Laboratory"

The goal is to create a virtual 3D laboratory where experiments can be visualized. Lean 4 remains the "brain," ensuring scientific rigor, while the game engine acts as the "world," providing a rich, interactive, and high-performance visualization of the experiment as it unfolds based on Lean's commands.

---

## 3. Analysis of Game Engine Candidates

### 3.1 Godot Engine (Recommended)

*   **Pros:**
    *   **Fully Open Source (MIT License):** No restrictions on use or distribution.
    *   **Excellent Command-Line Interface:** Can be launched and controlled from an external script, which is essential for our Lean driver.
    *   **Easy Scripting (GDScript):** The Python-like GDScript is easy to learn and perfectly suited for tasks like parsing JSON commands, manipulating 3D objects, and creating UI elements.
    *   **Lightweight & Fast:** The engine itself is small and starts quickly.
    *   **Mature 3D Environment:** Comes with a full 3D editor, physics engine (which we can use for non-experimental objects), animation system, and UI toolkit.

*   **Cons:**
    *   While performant, it doesn't have the same raw graphical power as top-tier AAA engines like Unreal. This is not a significant drawback for our scientific visualization needs.

### 3.2 Unreal Engine

*   **Pros:**
    *   **Unmatched Visual Fidelity:** Capable of producing photorealistic graphics.
*   **Cons:**
    *   **Complexity:** Extremely complex C++-based engine with a steep learning curve.
    *   **Overkill:** Its feature set is far beyond our project's scope.
    *   **Licensing:** While source-available, it has royalty-based licensing that is less straightforward than Godot's MIT license.

### 3.3 Unity

*   **Pros:**
    *   Popular and well-documented.
*   **Cons:**
    *   Recent controversial licensing changes make it a less attractive option for open-source research projects.
    *   Not as lightweight or command-line friendly as Godot.

---

## 4. Proposed Architecture: The Lean + Godot Hybrid Model

This architecture maximizes both rigor and visualization quality while minimizing development effort.

**Workflow:**

1.  **Lean (The "Brain"):**
    *   Performs the Phase 1 Ground Truth derivation.
    *   Formally proves the expected outcome of an experiment (e.g., `P(+) = 0.5`).
    *   Uses the `IO.Process.run` function to execute the Godot application.

2.  **Communication (File-based):**
    *   Lean writes a simple JSON file with a high-level command. This is the most robust method.
    *   *Example `command.json`*:
        ```json
        {
          "experiment_id": "01_stern_gerlach",
          "parameters": {
            "particle_count": 1000,
            "prob_up": 0.5
          }
        }
        ```
    *   Lean then launches Godot: `godot --headless --script /path/to/runner.gd -- /path/to/command.json`. The Godot project is launched in a headless mode to run the simulation based on the command file. For visualization, it would be launched normally, reading the command file on startup.

3.  **Godot (The "Interactive Lab"):**
    *   A Godot project is created containing the 3D assets for the laboratory (magnets, detectors, etc.).
    *   A main GDScript file reads the `command.json` on startup.
    *   Based on the `experiment_id`, it loads the correct scene and initiates the simulation.
    *   It uses the `parameters` from Lean to run the visual part of the experiment. For example, it doesn't *calculate* `prob_up`; it *uses* the `prob_up` value provided by Lean to run a random number generator and decide the particle's path.
    *   It handles all rendering, animation, camera controls, and UI, providing a rich, interactive experience.

---

## 5. Comparison of Visualization Approaches

| Approach | Rigor | Visual Fidelity | Performance | Dev Effort |
|---|---|---|---|---|
| **Python / VPython** | Low (Logic in Python) | Low-Medium | Low | **Very Low** |
| **Custom Go Renderer** | High (Hybrid Model) | Low-Medium | High | **Very High** |
| **Game Engine (Godot)**| High (Hybrid Model) | **High** | **High** | **Medium** |

The Game Engine approach strikes the best balance. The development effort is "Medium" because we are leveraging a massive, pre-built engine, but it is not "Low" because we still need to build the specific lab scenes and scripting logic within Godot.

---

## 6. Recommendation

The use of a game engine, specifically **Godot**, is the superior architectural choice for creating a "Lean-driven Physics Laboratory." It provides a far better balance of visual fidelity, performance, and development effort than a custom Go renderer, while maintaining the same level of scientific rigor through the **Lean + Godot Hybrid Model**.

**Proposed Next Step:**
A small proof-of-concept (PoC) should be developed to validate the communication pipeline:
1.  Create a simple Lean 4 program that writes a `{"message": "Hello from Lean"}` JSON file.
2.  Create a simple Godot project with a label.
3.  Write a GDScript that, on startup, reads the JSON file and displays the message in the label.
4.  Have the Lean program launch the Godot project from the command line.

Successfully implementing this PoC would validate the entire architecture before committing to a full-scale implementation for one of the physics experiments.
