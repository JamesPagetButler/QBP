# Research: Game Engine Architecture for a Lean-Driven Physics Laboratory

This document investigates the feasibility of using a real-time game engine as an interactive 3D visualization front-end, driven by a formal proof assistant (Lean 4). It builds upon the previous research (`architecture_studies/lean_golang_architecture.md`) and proposes a more powerful and practical architecture.

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

### 3.1 Godot Engine (High-Level & Mature)

*   **Pros:**
    *   **Fully Open Source (MIT License):** No restrictions on use or distribution.
    *   **Excellent Command-Line Interface:** Can be launched and controlled from an external script, which is essential for our Lean driver.
    *   **Easy Scripting (GDScript):** The Python-like GDScript is extremely easy to learn and perfectly suited for the simple logic required (parsing JSON, triggering animations). This leads to very low development effort for the "Lab" side of the project.
    *   **Mature Ecosystem:** Massive community, extensive documentation, tutorials, and a large asset library.

*   **Cons:**
    *   While performant, it doesn't have the same raw graphical power as top-tier AAA engines like Unreal. This is not a significant drawback for our scientific visualization needs.

### 3.2 Kaiju Engine (Go-Native & Modern)

*   **Pros:**
    *   **Written in Go:** Directly aligns with the original user interest in a Go-based visualization engine. This allows for a unified language on the "visualization/simulation" side of the architecture.
    *   **Modern Backend (Vulkan):** Utilizes a modern, high-performance graphics API.
    *   **Full-Featured:** Includes a built-in editor, physics, animation, and UI systems, representing a massive advantage over a custom Go renderer.
    *   **Open Source (MIT License):** Fully open for any use case.

*   **Cons:**
    *   **Ecosystem and Maturity:** As a newer, less-common engine, it has a much smaller community, fewer learning resources, and a less-developed asset ecosystem compared to Godot.
    *   **Development Language:** While powerful, Go is more verbose and lower-level than GDScript. The development effort to write the simulation/visualization logic in Go would be higher than in Godot for the same result.

### 3.3 Unreal Engine

*   **Pros:**
    *   **Unmatched Visual Fidelity:** Capable of producing photorealistic graphics.
*   **Cons:**
    *   **Complexity:** Extremely complex C++-based engine with a steep learning curve.
    *   **Overkill:** Its feature set is far beyond our project's scope.
    *   **Licensing:** While source-available, it has royalty-based licensing that is less straightforward than Godot's MIT license.

### 3.4 Unity

*   **Pros:**
    *   Popular and well-documented.
*   **Cons:**
    *   Recent controversial licensing changes make it a less attractive option for open-source research projects.
    *   Not as lightweight or command-line friendly as Godot.

---

## 4. Proposed Architecture: The Lean + Game Engine Hybrid Model

This architecture maximizes both rigor and visualization quality. The core idea is the same regardless of the chosen engine (Godot or Kaiju).

**Workflow:**

1.  **Lean (The "Brain"):**
    *   Performs the Phase 1 Ground Truth derivation.
    *   Formally proves the expected outcome of an experiment (e.g., `P(+) = 0.5`).
    *   Uses the `IO.Process.run` function to execute the chosen game engine.

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
    *   Lean then launches the engine, passing the command file path as an argument.

3.  **Game Engine (The "Interactive Lab"):**
    *   A project is created containing the 3D assets for the laboratory.
    *   A main script file (in GDScript for Godot, or Go for Kaiju) reads the `command.json` on startup.
    *   Based on the `experiment_id`, it loads the correct scene and initiates the simulation logic.
    *   It uses the `parameters` from Lean to run the visual part of the experiment. It does not calculate the physics itself.
    *   It handles all rendering, animation, camera controls, and UI.

---

## 5. Comparison of Visualization Approaches

| Approach | Rigor (Lean Driven) | Visual Fidelity | Performance | Dev Effort | Ecosystem |
|---|---|---|---|---|---|
| **Python / VPython** | Low (Logic in Python) | Low-Medium | Low | **Very Low** | Excellent |
| **Custom Go Renderer** | High (Hybrid Model) | Low-Medium | High | **Very High** | Minimal |
| **Game Engine (Godot)**| High (Hybrid Model) | **High** | **High** | **Medium-Low** | **Excellent** |
| **Game Engine (Kaiju)**| High (Hybrid Model) | **High** | **High** | **Medium-High**| Growing |

The Game Engine approach strikes the best balance. The development effort for Godot is rated "Medium-Low" due to the ease of GDScript, while Kaiju is "Medium-High" because writing the same logic in Go requires more effort.

---

## 6. Clarification: Physics Engines vs. Game Engines for QBP

The user's research prompt included a link to a list of open-source *physics engines* (e.g., Bullet, Jolt, Project Chrono). It is important to clarify the role of these libraries in contrast to a *game engine*.

*   A **Physics Engine** is a library that simulates classical mechanics—forces, collisions, rigid bodies. It does **not** handle rendering, sound, or user input. It is a component that a game engine uses internally.
*   A **Game Engine** is a complete framework that includes a rendering engine, audio engine, input system, and typically, a built-in physics engine.

**For the QBP project, a third-party classical physics engine is not what we need for our core simulation.** Our goal is to simulate *quantum* phenomena based on our own bespoke axioms, which are defined in Lean. The "physics" of our experiments (e.g., the probabilistic deflection in a Stern-Gerlach experiment) is an emergent property of the QBP axioms, not something that can be calculated by a classical engine like Bullet.

In effect, our combination of **Lean proofs + the `qphysics` library constitutes our own "Quantum Physics Engine."**

Therefore, a full **Game Engine (like Godot or Kaiju)** is the correct tool for the job because we need its **rendering, animation, and interaction** capabilities, not its physics simulation. The fact that these game engines come bundled with their own classical physics engines is a useful bonus for any secondary, environmental effects (e.g., making lab equipment movable), but it is not the primary reason for choosing them.

This analysis reinforces the conclusion to use a game engine as the "interactive lab" front-end, as it provides the necessary visualization layer for the results computed by our unique, Lean-driven physics.

## 7. Recommendation

The use of a game engine is the superior architectural choice for creating a "Lean-driven Physics Laboratory." This leaves a choice between two excellent candidates: Godot and Kaiju.

*   **Choose Godot if the priority is...**
    *   **Rapid Development and Ease of Use:** GDScript is significantly easier and faster for writing the necessary control scripts.
    *   **Leveraging a Mature Ecosystem:** Access to a vast library of tutorials, assets, and community support.

*   **Choose Kaiju if the priority is...**
    *   **A Pure Go Environment:** Adhering to the original interest in using Go for the visualization side.
    *   **A Modern, Opinionated Architecture:** Working with a newer engine built from the ground up on Go and Vulkan.

**Final Recommendation:** For this project, **Godot remains the most pragmatic choice** because its ease of scripting (GDScript) will minimize the development time needed for the non-core (visualization) part of the task, allowing more focus on the Lean-based physics. However, Kaiju is a powerful and valid alternative if a Go-native environment is strongly preferred.

**Proposed Next Step:**
The proof-of-concept (PoC) outlined previously remains the correct next step. It can be implemented with **Godot** to quickly validate the architecture.
1.  Create a simple Lean 4 program that writes a `{"message": "Hello from Lean"}` JSON file.
2.  Create a simple Godot project with a label.
3.  Write a GDScript that, on startup, reads the JSON file and displays the message in the label.
4.  Have the Lean program launch the Godot project from the command line.

Successfully implementing this PoC would validate the entire architecture before committing to a full-scale implementation for one of the physics experiments.
