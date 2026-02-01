# QBP Project TODO

Our overall goal is to work through the Eight-Fold Path. Our current focus is **#1: The Stern-Gerlach Experiment**.

Following our workflow (Paper -> Source -> Experiment):

## Stage 1: Paper (Theorize)

- [ ] **Task 1:** In `paper/quaternion_physics.md`, write a new section describing the Stern-Gerlach experiment in the language of traditional quantum mechanics (using state vectors and Pauli matrices).
- [ ] **Task 2:** In the same document, formulate a hypothesis for how to represent a spin-1/2 particle's state and the magnetic field interaction using quaternions. We need to define what a "quaternion state" is and how it should behave.

## Stage 2: Source (Build)

- [ ] **Task 3:** Implement or choose a quaternion library in `src/qphysics.py`. We need to be able to create quaternions and perform basic operations (addition, multiplication, conjugate, norm).
- [ ] **Task 4:** Based on the hypothesis from Task 2, implement the "quaternion state" and any necessary operators in `src/qphysics.py`.

## Stage 3: Experiment (Test)

- [ ] **Task 5:** Create a script `experiments/01_stern_gerlach/simulate.py`.
- [ ] **Task 6:** In the simulation script, use the library from `src/qphysics.py` to build the initial state of the particle, apply the magnetic field operator, and evolve the state.
- [ ] **Task 7:** The simulation must show that the final state is always one of two discrete outcomes, mirroring the "spin up" and "spin down" results of the real experiment.

---
This `TODO.md` will be updated as we complete each task.
