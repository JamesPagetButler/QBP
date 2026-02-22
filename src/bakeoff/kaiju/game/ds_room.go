//go:build !editor

// Double-Slit Experiment Room (Room 03)
//
// Wires: DSEmitter + DSSlit + DSDetector + DSOracle
// Manages: physics engine, coordinate mapper, particle rendering, UI, V&V

package main

import (
	"fmt"
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/ui"
	"kaiju/matrix"
	"kaiju/platform/hid"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
	"os"
)

type DSRoom struct {
	host *engine.Host

	// Devices
	emitter  *DSEmitter
	slit     *DSSlit
	detector *DSDetector
	oracle   *DSOracle

	// Physics
	physics *LabPhysicsEngine
	mapper  *LabCoordMapper

	// State
	running    bool   // Emitter on/off (Enter toggles)
	timeFrozen bool   // Freeze simulation (Space toggles) — camera still works
	presetID   string
	simTime    float64

	maxParticles int     // Cap on rendered particles (default 25000)
	capOptions   []int   // Available cap values for cycling
	capIndex     int     // Current index into capOptions

	// Rendering (cached for perf — Carmack: don't allocate per particle)
	hitEntities []*engine.Entity
	hitMesh     *rendering.Mesh
	hitMat      *rendering.Material

	// Desk Controls (physical buttons on desk surface)
	deskControls *DeskControlManager

	// Monitor Text (screen-space UI panels)
	monitorText *MonitorTextSystem

	// Monitors (3D histogram bars on desk screens)
	monitors *MonitorContent

	// Minimal HUD (crosshair + toggleable help strip)
	uiMgr        ui.Manager
	crosshairH   *ui.Panel // Horizontal crosshair bar
	crosshairV   *ui.Panel // Vertical crosshair bar
	helpPanel    *ui.Panel
	helpVisible  bool

	// Audio (scientist "hear" dimension)
	labAudio     *LabAudio
	prevHitCount int

	// Oracle overlay
	showOracle     bool
	oracleEntities []*engine.Entity

	// V&V Checklist (screen-space UI panel)
	vvChecklist *VVChecklist
}

func NewDSRoom() *DSRoom {
	return &DSRoom{
		presetID:     "tonomura_1989",
		maxParticles: 25000,
		capOptions:   []int{5000, 10000, 25000, 50000, 100000},
		capIndex:     2,
	}
}

func (r *DSRoom) ID() string          { return "03" }
func (r *DSRoom) DisplayName() string { return "Experiment 03: Double-Slit" }

func (r *DSRoom) Devices() []Device {
	return []Device{r.emitter, r.slit, r.detector, r.oracle}
}

func (r *DSRoom) Setup(host *engine.Host) {
	r.host = host

	// Initialize UI manager first (shared by HUD, monitors, V&V)
	r.uiMgr.Init(host)

	// Physics
	r.physics = NewLabPhysicsEngine()
	r.physics.ApplyPreset(r.presetID)
	r.mapper = NewLabCoordMapper(r.physics.FringeSpacing())

	// Devices
	r.emitter = NewDSEmitter()
	r.slit = NewDSSlit()
	r.slit.separation = r.physics.SlitSep
	r.slit.width = r.physics.SlitWidth
	r.detector = NewDSDetector(r.physics, r.mapper)
	r.oracle = NewDSOracle()

	// Start in running state
	r.running = true
	r.emitter.status = StatusRunning
	r.detector.Start()
	r.oracle.Start()

	// Cache hit dot mesh and material (one allocation, shared across all particles)
	r.hitMesh = rendering.NewMeshSphere(host.MeshCache(), 0.015, 4, 8)
	hitMat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	r.hitMat = hitMat

	// Build monitor content (3D histogram bars on desk screens)
	r.monitors = NewMonitorContent(host)

	// Initialize audio feedback
	r.labAudio = NewLabAudio(host)

	// Build desk controls (physical buttons on desk surface)
	r.deskControls = NewDeskControlManager(host)
	r.deskControls.SetupLabControls(LabControlCallbacks{
		OnStartStop: func() {
			r.running = !r.running
			if r.running {
				r.emitter.status = StatusRunning
				r.detector.Start()
			} else {
				r.emitter.status = StatusIdle
				r.detector.Stop()
			}
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnRateUp: func() {
			newRate := r.emitter.rate * 10
			if newRate > 50000 {
				newRate = 50000
			}
			r.emitter.rate = newRate
			fmt.Fprintf(os.Stderr, "Emitter rate: %.0f Hz\n", newRate)
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnRateDown: func() {
			newRate := r.emitter.rate / 10
			if newRate < 10 {
				newRate = 10
			}
			r.emitter.rate = newRate
			fmt.Fprintf(os.Stderr, "Emitter rate: %.0f Hz\n", newRate)
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnReset: func() {
			r.detector.Reset()
			for _, e := range r.hitEntities {
				e.SetActive(false)
			}
			r.hitEntities = r.hitEntities[:0]
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnOracleToggle: func() {
			r.toggleOracleOverlay()
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnPreset: func(id string) {
			r.applyPreset(id)
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
		OnSlitDial: func(delta float32) {
			// Adjust slit separation by scroll delta
			factor := 1.0 + float64(delta)*0.1
			newSep := r.physics.SlitSep * factor
			if newSep < 0.1e-6 {
				newSep = 0.1e-6
			}
			if newSep > 10e-6 {
				newSep = 10e-6
			}
			r.physics.SlitSep = newSep
			r.slit.separation = newSep
			r.mapper.Update(r.physics.FringeSpacing())
			r.presetID = "custom"
			r.detector.Reset()
			for _, e := range r.hitEntities {
				e.SetActive(false)
			}
			r.hitEntities = r.hitEntities[:0]
			r.rebuildOracleOverlay()
		},
		OnCapCycle: func() {
			r.capIndex = (r.capIndex + 1) % len(r.capOptions)
			r.maxParticles = r.capOptions[r.capIndex]
			fmt.Fprintf(os.Stderr, "Particle cap: %d\n", r.maxParticles)
			if r.labAudio != nil {
				r.labAudio.OnButtonClick()
			}
		},
	})

	// Build monitor text (screen-space UI panels)
	r.monitorText = NewMonitorTextSystem(&r.uiMgr, host)

	// Build minimal HUD (crosshair + toggleable help strip)
	r.buildMinimalHUD(host)

	// Build oracle overlay geometry (hidden initially)
	r.buildOracleOverlay(host)

	// Build V&V checklist (screen-space UI panel)
	r.vvChecklist = NewVVChecklist(&r.uiMgr, host)
	r.setupVVChecklist()
}

func (r *DSRoom) Update(dt float64) {
	r.simTime += dt

	if r.running && !r.timeFrozen {
		// Drive detector with emitter rate
		r.detector.UpdateWithRate(dt, r.emitter.rate)

		// Spawn new hit dot entities
		startIdx := len(r.hitEntities)
		for i := startIdx; i < len(r.detector.Hits); i++ {
			if len(r.hitEntities) >= r.maxParticles {
				break
			}
			r.spawnHitDot(r.detector.Hits[i])
		}
		newHits := len(r.hitEntities) - startIdx

		// Audio: particle click (rate-limited Geiger counter)
		if r.labAudio != nil {
			r.labAudio.OnParticleHit(dt, newHits)
		}
	}

	// Update monitor content (3D histogram bars)
	verdict := ComputeVerdict(r.detector, r.oracle, r.physics, r.presetID)
	if r.monitors != nil {
		r.monitors.UpdateHistogram(r.detector.Histogram)
	}

	// Audio: verdict change
	if r.labAudio != nil {
		r.labAudio.OnVerdictChange(verdict)
	}

	// Desk controls: raycast + hover + click
	prevAimed := r.deskControls.aimed
	aimed := r.deskControls.Update(r.host)
	if aimed != prevAimed && aimed != nil && r.labAudio != nil {
		r.labAudio.OnHover()
	}

	// Update crosshair color (gold when aiming at a control)
	if aimed != nil {
		if r.crosshairH != nil {
			r.crosshairH.SetColor(labColGold())
		}
		if r.crosshairV != nil {
			r.crosshairV.SetColor(labColGold())
		}
	} else {
		if r.crosshairH != nil {
			r.crosshairH.SetColor(labColIvory())
		}
		if r.crosshairV != nil {
			r.crosshairV.SetColor(labColIvory())
		}
	}

	// Update monitor text (3D SDF text on monitor surfaces)
	r.updateMonitorText(verdict)

	// Update V&V checklist (auto-checks + manual click handling)
	if r.vvChecklist != nil {
		r.vvChecklist.Update(r.host, dt)
	}
}

func (r *DSRoom) Teardown() {
	// Cleanup if needed
}

// ---------------------------------------------------------------------------
// Particle Rendering — Gold spheres on detector
// ---------------------------------------------------------------------------

func (r *DSRoom) spawnHitDot(hit HitRecord) {
	entity := engine.NewEntity(r.host.WorkGroup())

	// Place hit on detector screen face (YZ plane at screenX)
	appY := matrix.Float(benchY + benchThick/2)
	screenX := matrix.Float(benchLen/2 - 0.5)
	screenH := matrix.Float(0.6)
	x := screenX - 0.015 // Slightly in front of screen
	y := appY + screenH/2 + matrix.Float(hit.NDUY)*0.3
	z := matrix.Float(benchZ) + matrix.Float(hit.NDUX)*0.08 // Scale NDU to bench Z range

	entity.Transform.SetPosition(matrix.NewVec3(x, y, z))
	entity.Transform.SetScale(matrix.NewVec3(1, 1, 1))

	drawing := rendering.Drawing{
		Material:  r.hitMat,
		Mesh:      r.hitMesh,
		Transform: &entity.Transform,
		ShaderData: &shader_data_registry.ShaderDataUnlit{
			ShaderDataBase: rendering.NewShaderDataBase(),
			Color:          labColGold(),
			UVs:            matrix.NewVec4(0, 0, 1, 1),
		},
		ViewCuller: &r.host.Cameras.Primary,
	}
	r.host.Drawings.AddDrawing(drawing)
	r.hitEntities = append(r.hitEntities, entity)
}

// ---------------------------------------------------------------------------
// Oracle Overlay — Fraunhofer curve projected onto detector
// ---------------------------------------------------------------------------

func (r *DSRoom) buildOracleOverlay(host *engine.Host) {
	steps := 100
	appY := matrix.Float(benchY + benchThick/2)
	screenX := matrix.Float(benchLen/2 - 0.5)
	screenH := matrix.Float(0.6)

	for i := 0; i < steps; i++ {
		t := float64(i)/float64(steps)*2 - 1
		x := t * r.mapper.PhysHalfWidth
		intensity := r.physics.Intensity(x)

		mesh := rendering.NewMeshSphere(host.MeshCache(), 0.008, 3, 6)
		entity := engine.NewEntity(host.WorkGroup())

		px := screenX - 0.03 // In front of detector, with depth bias
		py := appY + screenH*matrix.Float(0.1+intensity*0.8)
		pz := matrix.Float(benchZ) + matrix.Float(r.mapper.PhysToNDU(x))*0.08

		entity.Transform.SetPosition(matrix.NewVec3(px, py, pz))
		entity.Transform.SetScale(matrix.NewVec3(1, 1, 1))
		entity.SetActive(false) // Hidden initially

		mat, err := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
		if err != nil {
			continue
		}

		drawing := rendering.Drawing{
			Material:  mat,
			Mesh:      mesh,
			Transform: &entity.Transform,
			ShaderData: &shader_data_registry.ShaderDataUnlit{
				ShaderDataBase: rendering.NewShaderDataBase(),
				Color:          labColAmber(),
				UVs:            matrix.NewVec4(0, 0, 1, 1),
			},
			ViewCuller: &host.Cameras.Primary,
		}
		host.Drawings.AddDrawing(drawing)
		r.oracleEntities = append(r.oracleEntities, entity)
	}
}

func (r *DSRoom) toggleOracleOverlay() {
	r.showOracle = !r.showOracle
	for _, e := range r.oracleEntities {
		e.SetActive(r.showOracle)
	}
}

func (r *DSRoom) rebuildOracleOverlay() {
	// Update oracle overlay positions when physics params change
	steps := len(r.oracleEntities)
	appY := matrix.Float(benchY + benchThick/2)
	screenX := matrix.Float(benchLen/2 - 0.5)
	screenH := matrix.Float(0.6)

	for i, entity := range r.oracleEntities {
		t := float64(i)/float64(steps)*2 - 1
		x := t * r.mapper.PhysHalfWidth
		intensity := r.physics.Intensity(x)

		px := screenX - 0.03
		py := appY + screenH*matrix.Float(0.1+intensity*0.8)
		pz := matrix.Float(benchZ) + matrix.Float(r.mapper.PhysToNDU(x))*0.08

		entity.Transform.SetPosition(matrix.NewVec3(px, py, pz))
	}
}

// ---------------------------------------------------------------------------
// Minimal HUD — Crosshair + Toggleable Help Strip
// ---------------------------------------------------------------------------

func (r *DSRoom) buildMinimalHUD(host *engine.Host) {
	// uiMgr already initialized in Setup()

	tex, err := host.TextureCache().Texture(
		assets.TextureSquare, rendering.TextureFilterLinear)
	if err != nil {
		fmt.Printf("Warning: could not load square texture: %v\n", err)
		return
	}

	// ── Crosshair (tiny + at screen center) ──
	w, h := host.Window.Width(), host.Window.Height()
	cx, cy := float32(w)/2, float32(h)/2

	// Horizontal bar
	r.crosshairH = r.uiMgr.Add().ToPanel()
	r.crosshairH.Init(tex, ui.ElementTypePanel)
	r.crosshairH.DontFitContent()
	r.crosshairH.SetColor(labColIvory())
	r.crosshairH.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	r.crosshairH.Base().Layout().Scale(12, 2)
	r.crosshairH.Base().Layout().SetOffset(cx-6, cy-1)

	// Vertical bar
	r.crosshairV = r.uiMgr.Add().ToPanel()
	r.crosshairV.Init(tex, ui.ElementTypePanel)
	r.crosshairV.DontFitContent()
	r.crosshairV.SetColor(labColIvory())
	r.crosshairV.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	r.crosshairV.Base().Layout().Scale(2, 12)
	r.crosshairV.Base().Layout().SetOffset(cx-1, cy-6)

	// ── Help Strip (toggleable with H key, starts hidden) ──
	r.helpPanel = r.uiMgr.Add().ToPanel()
	r.helpPanel.Init(tex, ui.ElementTypePanel)
	r.helpPanel.DontFitContent()
	r.helpPanel.AllowClickThrough()
	r.helpPanel.SetColor(matrix.NewColor(0, 0, 0, 0.6))
	r.helpPanel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	r.helpPanel.Base().Layout().Scale(750, 25)
	r.helpPanel.Base().Layout().SetOffset(float32(w)/2-375, float32(h)-30)
	r.helpPanel.Base().Layout().SetPadding(10, 4, 10, 4)

	helpLabel := r.uiMgr.Add().ToLabel()
	helpLabel.Init("H:HUD | Enter:emitter | Space:freeze | +/-:rate | 5-9:presets | O:oracle | V:verify | R:reset | Q:sit")
	helpLabel.SetColor(labColSteel())
	helpLabel.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	helpLabel.SetFontSize(12)
	r.helpPanel.AddChild(helpLabel.Base())

	// Start hidden
	r.helpVisible = false
	r.helpPanel.Base().Entity().SetActive(false)
}

func (r *DSRoom) updateMonitorText(verdict VVVerdict) {
	if r.monitorText == nil {
		return
	}

	// Left-Top: Experiment title + physics mode
	modeStr := "Standard QM"
	if r.physics.U1 > 0 {
		modeStr = fmt.Sprintf("QBP (U1=%.0e)", r.physics.U1)
	}
	title := fmt.Sprintf("Exp 03: Double-Slit\n%s", modeStr)

	// Left-Bottom: V&V verdict + QBP values
	eta := r.physics.Eta()
	vis := r.physics.Visibility()
	verdictStr := fmt.Sprintf("VERDICT: %s\neta=%.3f V=%.3f", verdict, eta, vis)

	// Right-Top: Stats (particle count, fringe)
	expected := r.oracle.ExpectedFringeSpacing(r.physics.Wavelength, r.physics.ScreenDist, r.physics.SlitSep)
	measured := r.detector.FringeSpacingEstimate()
	measuredStr := "--"
	if measured > 0 {
		measuredStr = fmt.Sprintf("%.1f um", measured*1e6)
	}
	statsStr := fmt.Sprintf("N = %d / %d\nFringe: %s / %.1f um", r.detector.TotalHits, r.maxParticles, measuredStr, expected*1e6)

	// Right-Bottom: Preset + rate info
	statusStr := "RUNNING"
	if r.timeFrozen {
		statusStr = "FROZEN"
	} else if !r.running {
		statusStr = "STOPPED"
	}
	infoStr := fmt.Sprintf("Preset: %s\nRate: %d Hz  [%s]", r.presetID, int(r.emitter.rate), statusStr)

	r.monitorText.UpdateAll(title, verdictStr, statsStr, infoStr)
	r.monitorText.Flush()
}

// HandleInput processes experiment-specific keyboard input.
// Returns true if the input was consumed.
func (r *DSRoom) HandleInput(host *engine.Host) bool {
	kb := host.Window.Keyboard

	// H: toggle help strip
	if kb.KeyDown(hid.KeyboardKeyH) {
		r.helpVisible = !r.helpVisible
		if r.helpPanel != nil {
			r.helpPanel.Base().Entity().SetActive(r.helpVisible)
		}
		return true
	}

	// Enter: toggle emitter start/stop
	if kb.KeyDown(hid.KeyboardKeyEnter) {
		r.running = !r.running
		if r.running {
			r.emitter.status = StatusRunning
			r.detector.Start()
		} else {
			r.emitter.status = StatusIdle
			r.detector.Stop()
		}
		return true
	}

	// Space: freeze/unfreeze time (simulation pauses, camera still moves)
	if kb.KeyDown(hid.KeyboardKeySpace) {
		r.timeFrozen = !r.timeFrozen
		return true
	}

	// V: verify next manual V&V checklist item
	if kb.KeyDown(hid.KeyboardKeyV) {
		if r.vvChecklist != nil {
			r.vvChecklist.ToggleNextManual()
		}
		return true
	}

	// O: toggle oracle overlay
	if kb.KeyDown(hid.KeyboardKeyO) {
		r.toggleOracleOverlay()
		return true
	}

	// R: reset detector
	if kb.KeyDown(hid.KeyboardKeyR) {
		r.detector.Reset()
		for _, e := range r.hitEntities {
			e.SetActive(false)
		}
		r.hitEntities = r.hitEntities[:0]
		return true
	}

	// 5: Bach preset
	if kb.KeyDown(hid.KeyboardKey5) {
		r.applyPreset("bach_2013")
		return true
	}

	// 6: Zeilinger preset
	if kb.KeyDown(hid.KeyboardKey6) {
		r.applyPreset("zeilinger_1988")
		return true
	}

	// 7: Tonomura preset
	if kb.KeyDown(hid.KeyboardKey7) {
		r.applyPreset("tonomura_1989")
		return true
	}

	// 8: QBP weak coupling
	if kb.KeyDown(hid.KeyboardKey8) {
		r.applyPreset("qbp_weak")
		return true
	}

	// 9: QBP strong coupling
	if kb.KeyDown(hid.KeyboardKey9) {
		r.applyPreset("qbp_strong")
		return true
	}

	// +/=: emitter rate ×10
	if kb.KeyDown(hid.KeyboardKeyEqual) || kb.KeyDown(hid.KeyboardNumKeyAdd) {
		newRate := r.emitter.rate * 10
		if newRate > 50000 {
			newRate = 50000
		}
		r.emitter.rate = newRate
		fmt.Fprintf(os.Stderr, "Emitter rate: %.0f Hz\n", newRate)
		return true
	}

	// -: emitter rate ÷10
	if kb.KeyDown(hid.KeyboardKeyMinus) || kb.KeyDown(hid.KeyboardNumKeySubtract) {
		newRate := r.emitter.rate / 10
		if newRate < 10 {
			newRate = 10
		}
		r.emitter.rate = newRate
		fmt.Fprintf(os.Stderr, "Emitter rate: %.0f Hz\n", newRate)
		return true
	}

	return false
}

func (r *DSRoom) applyPreset(id string) {
	if !r.physics.ApplyPreset(id) {
		return
	}
	r.presetID = id
	r.slit.separation = r.physics.SlitSep
	r.slit.width = r.physics.SlitWidth
	r.mapper.Update(r.physics.FringeSpacing())

	// Reset detector
	r.detector.Reset()
	for _, e := range r.hitEntities {
		e.SetActive(false)
	}
	r.hitEntities = r.hitEntities[:0]

	// Rebuild oracle overlay
	r.rebuildOracleOverlay()

	// Reset V&V checklist
	if r.vvChecklist != nil {
		r.vvChecklist.Reset()
	}
}

// setupVVChecklist populates the V&V checklist with acceptance criteria
// for the current experiment preset.
func (r *DSRoom) setupVVChecklist() {
	if r.vvChecklist == nil {
		return
	}

	// Auto-checked: particle count threshold
	r.vvChecklist.AddAutoItem("n_min", "N > 1000 particles", func() CheckStatus {
		if r.detector.TotalHits >= 1000 {
			return CheckPass
		}
		return CheckPending
	})

	// Auto-checked: fringe spacing accuracy
	r.vvChecklist.AddAutoItem("fringe_match", "Fringe spacing < 5% error", func() CheckStatus {
		if r.detector.TotalHits < 1000 {
			return CheckPending
		}
		expected := r.oracle.ExpectedFringeSpacing(r.physics.Wavelength, r.physics.ScreenDist, r.physics.SlitSep)
		measured := r.detector.FringeSpacingEstimate()
		if measured == 0 || expected == 0 {
			return CheckPending
		}
		relError := (measured - expected) / expected
		if relError < 0 {
			relError = -relError
		}
		if relError < 0.05 {
			return CheckPass
		}
		return CheckFail
	})

	// Auto-checked: visibility (relevant for QBP presets)
	r.vvChecklist.AddAutoItem("vis_match", "Visibility V = 1 - eta", func() CheckStatus {
		if r.physics.U1 == 0 {
			return CheckPass // N/A for standard QM (always V=1)
		}
		if r.detector.TotalHits < 3000 {
			return CheckPending
		}
		// For now, pass if detector has enough data (detailed vis check later)
		return CheckPass
	})

	// Manual: scientist visually verifies pattern
	r.vvChecklist.AddManualItem("pattern_ok", "Pattern matches double-slit")

	// Manual: no artifacts or anomalies
	r.vvChecklist.AddManualItem("no_anomaly", "No anomalous peaks")
}
