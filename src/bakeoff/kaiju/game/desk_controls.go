//go:build !editor

// QBP Phase 4e — Desk Controls
//
// Physical buttons and dials on the desk surface that the scientist
// interacts with via FPS crosshair raycast (Minecraft/Portal style).
// Hover highlights the control; click triggers the callback.

package main

import (
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/collision"
	"kaiju/matrix"
	"kaiju/platform/hid"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
)

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

// DeskControl represents a single interactive control on the desk surface.
type DeskControl struct {
	ID         string
	AABB       collision.AABB
	Entity     *engine.Entity
	SD         *shader_data_registry.ShaderDataUnlit
	BaseColor  matrix.Color
	HoverColor matrix.Color
	OnClick    func()
	IsToggle   bool // For toggle-style controls (oracle)
	IsActive   bool // Current toggle state
}

// DeskControlManager manages all desk controls and handles raycast interaction.
type DeskControlManager struct {
	host     *engine.Host
	controls []*DeskControl
	aimed    *DeskControl // Currently hovered

	// Click-lock state for dial controls
	dialLocked   bool
	lockedDial   *DeskControl
	dialCallback func(delta float32) // Called with mouse Y delta when dial is locked
}

// LabControlCallbacks provides the functions to wire up to desk controls.
type LabControlCallbacks struct {
	OnStartStop    func()
	OnRateUp       func()
	OnRateDown     func()
	OnReset        func()
	OnOracleToggle func()
	OnPreset       func(id string)
	OnSlitDial     func(delta float32) // delta in scroll units
}

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

// brightenColor mixes base toward white by the given factor (0..1).
func brightenColor(base matrix.Color, factor float32) matrix.Color {
	r := base.R() + (1-base.R())*factor
	g := base.G() + (1-base.G())*factor
	b := base.B() + (1-base.B())*factor
	return matrix.NewColor(r, g, b, 1)
}

// ---------------------------------------------------------------------------
// Constructor
// ---------------------------------------------------------------------------

// NewDeskControlManager creates a new manager (no controls yet).
func NewDeskControlManager(host *engine.Host) *DeskControlManager {
	return &DeskControlManager{
		host:     host,
		controls: make([]*DeskControl, 0, 16),
	}
}

// ---------------------------------------------------------------------------
// Adding controls
// ---------------------------------------------------------------------------

// AddButton creates a cube button entity sitting on the desk surface.
func (m *DeskControlManager) AddButton(
	id string,
	posX, posZ float32,
	size float32,
	baseColor matrix.Color,
	onClick func(),
) *DeskControl {
	host := m.host

	// Position: sits on desk surface, slightly raised
	pos := matrix.NewVec3(posX, deskY+size/2+0.01, posZ)
	scale := matrix.NewVec3(size, size, size)

	// Create entity + drawing
	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(pos)
	entity.Transform.SetScale(scale)

	mat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	sd := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          baseColor,
		UVs:            matrix.NewVec4(0, 0, 1, 1),
	}
	drawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &entity.Transform,
		ShaderData: sd,
		ViewCuller: &host.Cameras.Primary,
	}
	host.Drawings.AddDrawing(drawing)

	// AABB: extended upward by 0.05 for easier targeting from steep angles
	aabb := collision.AABB{
		Center: pos,
		Extent: matrix.NewVec3(size/2+0.02, size/2+0.05, size/2+0.02),
	}

	hoverColor := brightenColor(baseColor, 0.4)

	ctrl := &DeskControl{
		ID:         id,
		AABB:       aabb,
		Entity:     entity,
		SD:         sd,
		BaseColor:  baseColor,
		HoverColor: hoverColor,
		OnClick:    onClick,
	}
	m.controls = append(m.controls, ctrl)
	return ctrl
}

// AddDial creates a wider/flatter cube for dial-style controls (e.g. slit separation).
func (m *DeskControlManager) AddDial(
	id string,
	posX, posZ float32,
	sizeX, sizeZ float32,
	baseColor matrix.Color,
	onScroll func(delta float32),
) *DeskControl {
	host := m.host

	// Position: thin, nearly flush with desk
	pos := matrix.NewVec3(posX, deskY+0.02, posZ)
	scale := matrix.NewVec3(sizeX, 0.02, sizeZ)

	// Create entity + drawing
	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(pos)
	entity.Transform.SetScale(scale)

	mat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	sd := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          baseColor,
		UVs:            matrix.NewVec4(0, 0, 1, 1),
	}
	drawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &entity.Transform,
		ShaderData: sd,
		ViewCuller: &host.Cameras.Primary,
	}
	host.Drawings.AddDrawing(drawing)

	// AABB: extended upward for easier targeting
	aabb := collision.AABB{
		Center: pos,
		Extent: matrix.NewVec3(sizeX/2+0.02, 0.01+0.05, sizeZ/2+0.02),
	}

	hoverColor := brightenColor(baseColor, 0.4)

	// The OnClick for a dial toggles the click-lock
	scrollCb := onScroll
	ctrl := &DeskControl{
		ID:         id,
		AABB:       aabb,
		Entity:     entity,
		SD:         sd,
		BaseColor:  baseColor,
		HoverColor: hoverColor,
	}
	// Wire click to toggle the dial lock on the manager
	ctrl.OnClick = func() {
		if m.dialLocked && m.lockedDial == ctrl {
			// Release
			m.dialLocked = false
			m.lockedDial = nil
			m.dialCallback = nil
		} else {
			// Grab
			m.dialLocked = true
			m.lockedDial = ctrl
			m.dialCallback = scrollCb
		}
	}

	m.controls = append(m.controls, ctrl)
	return ctrl
}

// ---------------------------------------------------------------------------
// Per-frame update
// ---------------------------------------------------------------------------

// Update performs per-frame raycast hit-testing and interaction.
// Returns the currently aimed control (or nil), useful for crosshair color.
func (m *DeskControlManager) Update(host *engine.Host) *DeskControl {
	mouse := &host.Window.Mouse

	// --- Dial lock mode ---
	if m.dialLocked && m.dialCallback != nil {
		// Apply scroll wheel as dial input
		scrollDelta := mouse.ScrollY
		if scrollDelta != 0 {
			m.dialCallback(scrollDelta)
		}

		// Click releases the dial lock
		if mouse.Pressed(hid.MouseButtonLeft) {
			m.dialLocked = false
			m.lockedDial = nil
			m.dialCallback = nil
		}
		return m.lockedDial
	}

	// --- Normal mode: raycast from screen center ---
	cam := host.PrimaryCamera()
	w, h := host.Window.Width(), host.Window.Height()
	screenCenter := matrix.NewVec2(float32(w)/2, float32(h)/2)
	ray := cam.RayCast(screenCenter)

	// Hit-test all controls, pick the closest hit
	var closest *DeskControl
	var closestDist matrix.Float = 1e9

	for _, ctrl := range m.controls {
		hitPos, hit := ctrl.AABB.RayHit(ray)
		if hit {
			dist := ray.Origin.Distance(hitPos)
			if dist < closestDist {
				closestDist = dist
				closest = ctrl
			}
		}
	}

	// Hover state transitions
	if closest != m.aimed {
		// Unhighlight old
		if m.aimed != nil {
			m.aimed.SD.Color = m.aimed.BaseColor
		}
		// Highlight new
		if closest != nil {
			closest.SD.Color = closest.HoverColor
		}
		m.aimed = closest
	}

	// Click handling
	if mouse.Pressed(hid.MouseButtonLeft) && m.aimed != nil {
		if m.aimed.IsToggle {
			m.aimed.IsActive = !m.aimed.IsActive
		}
		if m.aimed.OnClick != nil {
			m.aimed.OnClick()
		}
	}

	return m.aimed
}

// ---------------------------------------------------------------------------
// Lab control layout
// ---------------------------------------------------------------------------

// SetupLabControls creates all the standard desk controls for the QBP lab.
func (m *DeskControlManager) SetupLabControls(callbacks LabControlCallbacks) {
	const controlZ float32 = deskZ + 0.35 // -5.15

	// RESET
	m.AddButton("reset", -0.30, controlZ, 0.05,
		labColCopper(), callbacks.OnReset)

	// SLIT DIAL (wider/flatter)
	m.AddDial("slit_dial", -0.18, controlZ, 0.10, 0.06,
		labColBrass(), callbacks.OnSlitDial)

	// RATE -
	m.AddButton("rate_down", -0.06, controlZ, 0.04,
		labColBrass(), callbacks.OnRateDown)

	// RATE +
	m.AddButton("rate_up", 0.00, controlZ, 0.04,
		labColBrass(), callbacks.OnRateUp)

	// START/STOP (green)
	m.AddButton("start_stop", 0.10, controlZ, 0.08,
		matrix.NewColor(0.3, 0.9, 0.4, 1), callbacks.OnStartStop)

	// Preset buttons: Bach, Zeilinger, Tonomura
	m.AddButton("bach_2013", 0.22, controlZ, 0.03,
		labColSteel(), func() { callbacks.OnPreset("bach_2013") })

	m.AddButton("zeilinger_1988", 0.26, controlZ, 0.03,
		labColSteel(), func() { callbacks.OnPreset("zeilinger_1988") })

	m.AddButton("tonomura_1989", 0.30, controlZ, 0.03,
		labColSteel(), func() { callbacks.OnPreset("tonomura_1989") })

	// QBP preset buttons
	m.AddButton("qbp_weak", 0.34, controlZ, 0.03,
		labColAmber(), func() { callbacks.OnPreset("qbp_weak") })

	m.AddButton("qbp_strong", 0.38, controlZ, 0.03,
		labColAmber(), func() { callbacks.OnPreset("qbp_strong") })

	// ORACLE (toggle)
	oracle := m.AddButton("oracle", 0.46, controlZ, 0.05,
		matrix.NewColor(0.3, 0.5, 0.8, 1), callbacks.OnOracleToggle)
	oracle.IsToggle = true
}
