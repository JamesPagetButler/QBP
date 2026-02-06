# Research: Lean 4 + Go Architecture for Physics Experiments

This document explores the feasibility of a novel architecture where Lean 4, a formal proof assistant, drives a visualization engine written in Go.

---

## 1. Executive Summary

**Conclusion:** The proposed architecture is **feasible but challenging**, with significant trade-offs.

*   **Feasibility:** Lean 4's `IO` monad and `IO.Process` library provide robust mechanisms for executing and communicating with external processes like a Go program. The most viable architecture is a **Hybrid Model** where Lean calculates high-level physical predictions and Go executes performance-intensive simulations based on those predictions.
*   **Challenges:** The Go ecosystem for scientific visualization is immature compared to Python's. Implementing this architecture would require writing a significant amount of low-level graphics code using OpenGL bindings, as there is no direct equivalent to a high-level library like VPython.
*   **Recommendation:** For the current project, **sticking with the Python ecosystem is more practical and efficient.** However, the "Hybrid Model" presents a compelling paradigm for future research where formal verification of the core logic is paramount.

---

## 2. The Vision

The core idea is to leverage Lean 4's theorem proving capabilities to drive the logic of our physics experiments, while using a compiled, high-performance language like Go to handle the visualization. This would, in theory, combine the ultimate scientific rigor with high-performance graphics.

---

## 3. Core Challenge 1: Lean 4 Interoperability

Our research shows that Lean 4 can interact with the outside world using the `IO` monad. The `IO.Process` namespace is the key tool.

*   **`IO.Process.run` & `IO.Process.output`:** These functions allow Lean to execute an external command (like `go run main.go`), pass it arguments, and wait for it to complete. `output` is more robust as it captures stdout, stderr, and the exit code, allowing for error handling.
*   **`IO.Process.spawn`:** This function allows for asynchronous, interactive communication with a running process via its stdin and stdout pipes.

This confirms that Lean can indeed "drive" a Go program. Communication would be text-based, likely using a structured format like JSON passed over stdin/stdout or via temporary files.

---

## 4. Core Challenge 2: The Go Visualization Ecosystem

This is the most significant hurdle.

*   **Lack of High-Level Libraries:** Unlike Python's rich ecosystem (`VPython`, `Manim`, `Matplotlib`, `Mayavi`), Go lacks mature, "batteries-included" scientific visualization libraries.
*   **Low-Level Approach Required:** The most viable path is to use Go bindings for a graphics API like OpenGL (e.g., using the `go-gl` library). This approach requires the developer to write significant boilerplate code to manage the window, rendering loop, shaders, and 3D object transformations.
*   **2D Plotting is Feasible:** For 2D data plotting (histograms, line graphs), the `gonum/plot` library is a mature and excellent choice.

---

## 5. Architectural Options

Based on the research, we can define three possible architectures. We assume communication via JSON messages.

### Architecture A: Lean as Real-time Orchestrator

*   **How it Works:** Lean runs the main simulation loop. In each frame, it computes the state of all objects, prints a JSON description to stdout, and a long-running Go program reads stdin to render the frame.
*   **Pros:** Maximum formal verification. The entire simulation logic is proven in Lean.
*   **Cons:** **Prohibitively slow.** The per-frame overhead of process communication and JSON serialization/deserialization makes real-time animation impossible for any non-trivial number of objects.

### Architecture B: Lean as Initializer

*   **How it Works:** Lean's role is reduced to generating a configuration file (e.g., `config.json`). It then executes a self-contained Go program which reads the config and runs the entire simulation and visualization internally.
*   **Pros:** Highest performance. Simple interoperability.
*   **Cons:** **Defeats the purpose.** The core physics logic is duplicated in Go without formal verification, completely losing the benefit of using Lean.

### Architecture C: Hybrid Model (Recommended)

*   **How it Works:** A balance of power. Lean performs the logically critical, but computationally inexpensive, "thinking" work. Go performs the computationally expensive, but logically simple, "doing" work.
*   **Example (Stern-Gerlach):**
    1.  **Lean**: Defines the state `ψ=i` and observable `O=k`.
    2.  **Lean**: Formally proves that the expected probability is `P(+) = 0.5`.
    3.  **Lean**: Executes the Go program, passing it a high-level command: `{"experiment": "stern_gerlach", "particles": 1000000, "prob_up": 0.5}`.
    4.  **Go**: Receives this command. It does not derive `prob_up`; it *uses* it. It then runs a fast internal loop to simulate 1,000,000 trials based on this probability and handles all the visualization.
*   **Pros:**
    *   Maintains the core principle of formal verification for the physics logic.
    *   Leverages Go's performance for the brute-force simulation and rendering part.
    *   Minimizes communication overhead.
*   **Cons:**
    *   Requires designing a clear "command API" for each experiment type.
    *   Still requires significant custom graphics programming in Go.

---

## 6. Application to the 9 Experiments

*   **Particle-based simulations (Stern-Gerlach, Double Slit, Bell Test):** The Hybrid Model would work well. Lean calculates probabilities and parameters, Go simulates N particles according to those parameters.
*   **Spectrum/Energy Level simulations (Lamb Shift, Hydrogen Spectrum, Positronium):** The Hybrid Model is also applicable. Lean could solve the core theoretical equations to find the expected energy levels, and Go could be tasked with plotting these levels or generating a visual representation of the spectrum. The `gonum/plot` library would be very effective here.
*   **Abstract Derivations (Particle Statistics):** These are purely theoretical and may not have a visual component, making them a task for Lean alone.
*   **Complex Field/Interaction simulations (g-2, Gravity):** These are the most challenging. A hybrid model is possible, but the "command API" from Lean to Go would be highly complex, potentially requiring Lean to pass entire vector fields or potential functions as data.

---

## 7. Final Recommendation

While the "Hybrid Model" is a technically fascinating and rigorous architecture, the immaturity of the Go visualization ecosystem presents a significant practical barrier. The development effort required to create compelling visualizations in Go would be an order of magnitude higher than with Python and VPython.

For the QBP project, **it is recommended to continue using the Python-based workflow**. The existing combination of Python for simulation logic and VPython/Matplotlib for visualization is far more productive.

The exploration of a Lean-driven architecture should be considered a **valuable future research direction** for projects where the absolute, provable correctness of every logical step, from theory to simulation, is the primary goal, and where the resources are available to develop a custom visualization engine.
