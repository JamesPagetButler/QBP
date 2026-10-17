# Port ↔ Experiment-Space Interface — what QBP needs from the Port

**Owner (QBP side):** Engine Cartographer persona (retained), via qbp-oppenheimer
**Counterpart (Port side):** hutchins, craft-implementor — steward of the craft family Port
**Status:** DRAFT v0.1 — QBP's statement of need. The contract (how a space is rendered/loaded, and where it plugs in) is the Port steward's to finalize. Tracking: QBP#711.
**Beekeeper framing (2026-10-17):** QBP produces, per experiment space, the set of specs and interfaces it needs from the Port; the Port steward tells QBP where to plug the experiment in.

---

## 1. Division of labour

| Concern | Who | Where it lives |
|---|---|---|
| The Port as a coherent whole (island, Celestial/Abyssal Axes, hallways, hub, docks) | Port steward (hutchins) | `JamesPagetButler/craft` |
| Family-default design system (Academic Steampunk → Solarpunk) | Port steward | craft (QBP keeps a frozen pointer) |
| Each **experiment space**: its instruments, parameters, data feeds, monitors, V&V | QBP (Engine Cartographer) | QBP: one spec per space (§3) + the space's own build if bespoke |
| **Plug-in point** for each space (berth, hallway door, altitude, orientation, footprint) | Port steward | the Port's manifest; returned to QBP as a `PlugIn` record (§4) |
| Spec-first rendering of a space in the shared design system | Port steward | craft render surfaces (inter#96 Squam/Cockpit, inter#152 Milano, …) |
| Bespoke geometry (escape hatch) | QBP builds, Port loads | QBP Kaiju scene or equivalent; the Port only needs a scene handle (type to be named by the steward; nothing called `Scene` exists in `kaiju/game` today) |
| **Design-system build inputs** `src/viz/theme.py`, `src/viz/interactive/src/theme.h` | **QBP** (live build inputs) | QBP `master`; craft `port/design-system/` holds snapshots; QBP re-syncs by PR when Port tokens change |
| **Canonical home of experiment-space code** (e.g. `src/bakeoff/kaiju/game/`) | **QBP** | QBP `master`. Not imported into craft (craft PR #2 dropped `port/kaiju/` at `5c6955b`); the Port takes the versioned spec, not the Go — one home per artefact (hand-off condition b). Any reusable Port-substrate subset is a separate curated import |

Working read agreed on the bridge (live-test seq 2915/2916): **spec-first**, Kaiju-scene-load as the escape hatch.

## 2. What an experiment space is, to the Port

An experiment space is a room-sized unit with: a stable **ID** and display name; a set of **devices**, each with named, bounded, unit-carrying parameters; one or more **data streams** (events the devices emit); **surfaces** where the Port renders device state and streams (monitors, HUD, overlays); **controls** that let a visitor change parameters or select presets; and a **verification checklist** that states when the space is "working". The Port owns the walls, light, and door; QBP owns everything in the preceding sentence.

## 3. Per-space spec (what QBP hands the Port)

One file per space, `docs/design/spaces/<id>-<slug>.md` (or the Port's chosen schema once fixed). Required sections:

| Section | Content | Instance zero (double-slit) source |
|---|---|---|
| `space` | `id`, `display_name`, QBP experiment number, status, **`spec_version`** (semver; the experiment's build records the version it was built against so the crossing cannot drift silently — qbp-architecture, live-test seq 2920) | `DSRoom.ID()` = `"03"`, `DisplayName()` = "Experiment 03: Double-Slit" |
| `time_base` | The space's clock: what `t=0` means (per run / per room start / absolute Port time), tick source (frame `dt` vs wall clock), whether time can be frozen/stepped, and the latency budget from device event to rendered surface | ds_room: `simTime += dt` per frame, **seconds since room start**, resets with the room, freezable (`timeFrozen`); event latency = one frame. **Gap:** `DSDetector` emits `DataEvent` without setting `Timestamp` (ds_devices.go:211) — instance-zero spec must fix or declare it |
| `footprint` | Requested interior volume (m), floor shape, required clearances (beam line length!), ceiling | ds_room: linear bench; emitter → slit → detector screen along one axis |
| `devices[]` | For each: `name`, role, `params[]` as `{name, min, max, default, log_scale, unit}`, status enum, start/stop, **`on_out_of_range`** (one of `reject` / `clamp` / `fail_safe`), and **failure states** (what the device reports when it cannot run and how it recovers) | `DSEmitter` (`rate` 10–5000 Hz, default 500); `DSSlit` (`separation` 0.1–10 µm log, default 1 µm; `width` 0.01–1 µm log, default 0.1 µm); `DSDetector` (start/stop/reset; visibility, fringe-spacing estimate); `DSOracle` (prediction feed). Out-of-range: **`reject`** — `Set` returns an error and leaves the value unchanged (ds_devices.go:51–62, 105–116); no clamping, no wrap |
| `streams[]` | Event schema per device: `{timestamp, source, payload}`; payload types enumerated; **`sampling`** (`event-driven` or a rate in Hz, with the expected peak event rate); **`buffer`** (who allocates, capacity, `drop_policy` on overflow: `drop_newest` / `drop_oldest` / `block`); **`retention`** (what is kept across the run, when it is flushed) | `DataEvent`; `HitRecord{PhysX, NDUX, NDUY, Bin}` from the detector; oracle predictions. Sampling: event-driven at the emitter `rate` (10–5000 Hz peak). Buffer: detector channel cap 256, oracle 16, allocated by the device, **non-blocking send ⇒ `drop_newest`** when the consumer lags (ds_devices.go:211). Retention: `Hits` and `Histogram` grow unbounded until `Reset()` — a per-run cap belongs in the instance-zero spec |
| `surfaces[]` | Monitors/HUD/overlays the Port must render, with the stream each binds to and the design-system constraints (axis colours, type) | desk monitors (3D histogram bars), CPU-rasterized monitor text, minimal HUD, oracle overlay (toggle) |
| `controls[]` | Physical/UI controls and what they call: parameter set, preset select, start/stop/reset, overlay toggle | desk buttons under labels EXPERIMENT / PARAMETERS / PRESETS; `LabControlCallbacks` |
| `presets[]` | Named parameter bundles | `applyPreset(id)` over `Preset` (package `game`, `lab_physics.go:33`) |
| `vv_checklist[]` | Items + the verdict function that flips them | `VVChecklist`, `VVVerdict`; measured visibility & fringe spacing vs oracle |
| `audio` | Optional ambient/event cues | `lab_audio.go` |
| `escape_hatch` | If the space cannot be expressed spec-first: the scene handle the Port loads and the engine it needs | Kaiju (Go/Vulkan) scene: `src/bakeoff/kaiju/game/ds_room.go` + `ds_devices.go` |

Everything in the right-hand column is already in code on QBP `master` @ `18ec30e`; the spec file is a restatement of those interfaces, so the first spec can be written without inventing anything.

## 4. What the Port hands back: the `PlugIn` record

For each accepted space, the Port steward returns one record QBP can build against:

| Field | Meaning |
|---|---|
| `berth` | Where in the Port: hub tier / hallway door / axis station / altitude |
| `frame` | A **4×4 affine transform** (column-major, metres, right-handed) mapping the space's local frame into Port coordinates, plus the Port's named up axis. Not negotiable per space: the Port fixes the convention once in its manifest and every `PlugIn` record carries the matrix |
| `clock` | How the space's `time_base` maps to Port time: offset + rate (1.0 unless the Port scales time), and whether the Port may freeze/step the space's clock |
| `footprint_granted` | Volume actually allotted (may differ from requested; QBP adapts or escalates) |
| `door` / `approach` | How visitors arrive; which side the entrance is on |
| `surfaces_available` | Which of the requested surfaces the Port renders natively, which fall to the escape hatch |
| `design_tokens` | The design-system tokens this space must use (or the override allowed) |
| `render_targets` | Which family surfaces will show this space (Cockpit 2D, Milano 3D, …) |
| `plugin_version` | **SemVer** of the Port manifest this record is valid against (major = breaking change to any field above; minor = additive; patch = text) |
| `spec_version_accepted` | The QBP `spec_version` this record answers |

A change to any `PlugIn` field is a Port-side change and gets communicated to QBP before it lands; a change to any §3 field is a QBP-side change and gets communicated to the steward the same way.

## 5. Process

1. QBP (Engine Cartographer) writes or updates the §3 spec → PR on QBP, reviewed as usual.
2. Steward reads the spec, returns the §4 `PlugIn` record (craft PR or an issue comment cross-linked from the QBP issue for that space). **QBP files one issue per space** (Engine Cartographer via qbp-oppenheimer); the PlugIn record is accepted QBP-side by qbp-oppenheimer's sign-off on that issue.
3. If spec-first suffices, the steward renders it; if not, QBP builds the bespoke scene and the Port loads it by handle.
4. The space's `vv_checklist` is the acceptance test on both sides: the Port shows it, QBP's physics decides it.
5. Version pinning: both `spec_version` and `plugin_version` are SemVer. A `PlugIn` record names the `spec_version` it answers; QBP's build names the `(spec_version, plugin_version)` pair it was built against. A major bump on either side invalidates the pair and requires a re-exchange; minor/patch bumps are recorded, not re-negotiated. Either side bumping is a visible event, not a silent drift.

## 6. Open questions for the steward

- Schema: markdown tables (this doc) vs a machine-readable spec (YAML/JSON) the Port can validate. QBP has no preference beyond "one source, diffable".
- Which up axis the Port fixes in its manifest (§4 `frame` requires metres + right-handed + one named up axis; the Kaiju lab is metres along the bench with NDU display units on the screen).
- Latency budget the Port can guarantee from device event to rendered surface (§3 `time_base`).
- Whether the Port renders data streams itself or hosts a QBP-provided renderer per surface.
- Lifetime: does the Port keep a space's last state between visits, or does QBP's device state own that?
- The scene handle type for the escape hatch (§1, §3 `escape_hatch`) — steward names it.

## 7. QBP-side follow-ups (owned, not yet filed)

- `docs/design/spaces/03-double-slit.md` — first versioned space spec (`spec_version 0.1.0`), written by the Engine Cartographer via qbp-oppenheimer; the `spaces/` directory does not exist yet. Filed as a QBP issue after #711 closes. Must resolve the two instance-zero gaps named in §3: detector events carry no `Timestamp`; `Hits` retention is unbounded.
- PlugIn record request for space `03` to the steward, cross-linked from that issue.

---

**Provenance:** QBP-authored 2026-10-17 by qbp-oppenheimer (Engine Cartographer remit) from the double-slit lab code on QBP `master` @ `18ec30e`. The Port, facility docs, and design system are stewarded in `JamesPagetButler/craft` (see the frozen pointers in `docs/design/`).
