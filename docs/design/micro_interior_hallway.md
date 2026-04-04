# QBP Facility Micro-Interior — Main Research Hallway

**Lead Bio-Synthesist:** Paget
**Status:** Concept Synthesized (Sprint 3 / Phase 4e)

## Architectural Synthesis
The final design for the main research hallway fuses the sweeping structural elegance of our initial concepts with a highly functional, symmetrical configuration. This serves as the primary blueprint for the Engine Cartographer (Kaiju/Raylib 3D integration) in Sprint 3.

### 1. Form and Elegance (The Bio-Synthetic Curve)
- **Arches and Ribs:** The load-bearing structures draw from Victorian greenhouse aesthetics. Heavy, swept circular arches—constructed from dark slate and brushed steel, and accented with polished brass—curve gracefully upward to support the vaulted glass ceiling.
- **Overhead Cultivation:** Following the "Living Anchor" philosophy, lush tropical greenery (ferns, orchids, hanging vines) is cultivated high up near the glass roof. The sweeping curves of the architecture keep this biomass elevated, leaving the researchers' floor entirely unobstructed and pristine.

### 2. Functional Configuration (The Symmetry of Utility)
- **Modular Expansion:** This hallway is designed as a single repeatable *module*. As the QBP project expands beyond the initial 10 experiments, additional hallway modules can be appended, branching off the main atrium or central hubs.
- **Symmetrical Layout:** Five (5) dedicated experiment labs flank *each* side of the hallway (10 labs total per module).
- **Module Entry: Gear & Preparation Room:** Located at the entrance of each hallway module (the transition point from the atrium or hub) is a dedicated gear room. This room serves as the staging area for the module's 10 labs.
  - **Locker Systems:** Rows of polished natural wood and brass lockers store vacuum-rated suits, hazard gear, and clean-room attire.
  - **Suit-Up Benches:** Ergonomic slate and wood benches for personnel to don protective equipment.
  - **BSLS Status Terminal:** A large central display showing the collective environmental status of all 10 labs in the module.
  - **Aesthetic:** The room maintains the "Old Growth Forest" atmosphere, providing a calm, focused environment for preparation.
- **The Entry Sequence:** As a researcher approaches a lab, the architecture dictates a specific workflow:
  1.  **The Viewport:** Positioned *before* the door is a large, circular, reinforced glass viewport set into the wall, allowing for non-disruptive observation of the active experiment inside.
  2.  **Environmental Status Display:** A sleek, vertical LED/LCD panel set into the slate wall between the viewport and the door. This panel displays the real-time environmental variables of the lab (Temperature, Pressure, Gravity, etc.) and highlights any **deviations from ambient baseline** in amber.
  3.  **The Signage:** Glowing amber nameplates project *perpendicularly* from the wall above each door, ensuring immediate readability while walking down the corridor.
  4.  **The Outer Door & Lock:** Heavy, rectangular wood and brass doors with elegant arched tops. Entry requires a hybrid locking mechanism: a modern electronic key-fob scan paired with the physical actuation of a heavy, ornate brass mechanical lever.
  5.  **The Airlock Chamber:** Upon passing the outer door, researchers enter a small, pressurized airlock chamber. This ensures the integrity of the lab environment (e.g., maintaining high vacuum or sterile conditions). All scientists entering the lab are assumed to be wearing appropriate protective gear (donned in the Gear Room) before the inner door cycles open.
- **The Clear Path:** The hallway itself contains no control desks or workstations. It is a conduit of pure transit, thought, and observation.

### 3. The Atrium Destination
At the far end of the hallway, the corridor opens into a bright, open gathering atrium. Expansive, floor-to-ceiling greenhouse windows provide a panoramic view of the turquoise Pacific Ocean and the glowing carbon-nanotube tether of the Celestial Axis (Space Elevator) ascending into the sky.

---

## Implementation Notes for Engine Cartographer
- **Visual References:** Synthesize the curved arches and elegant greenhouse structure of `a_photorealistic_wideangle_inter.png` (Iteration 1) with the strict door/viewport/signage layout of `a_photorealistic_wideangle_inter_6.png` (Iteration 6).
- **Lighting Dynamics:** Engine should utilize warm, natural directional light from the glass ceiling and atrium, creating dynamic reflections off the polished wood floors and brass accents.
