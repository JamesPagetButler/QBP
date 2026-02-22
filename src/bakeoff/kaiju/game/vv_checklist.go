//go:build !editor

// vv_checklist.go — Physical V&V checklist panel on the scientist's desk.
//
// NASA go/no-go style verification: auto-checked criteria (fringe spacing,
// particle count, visibility) plus manual checkboxes the scientist clicks.
// Traffic-light summary (GREEN/AMBER/RED) shows overall experiment status.

package main

import (
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/collision"
	"kaiju/matrix"
	"kaiju/platform/hid"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
	"math"
)

// ---------------------------------------------------------------------------
// Status types
// ---------------------------------------------------------------------------

type CheckStatus int

const (
	CheckPending CheckStatus = iota
	CheckPass
	CheckFail
)

// CheckStatusColor returns the NASA-standard color for a status.
func CheckStatusColor(s CheckStatus) matrix.Color {
	switch s {
	case CheckPass:
		return matrix.NewColor(0.2, 0.9, 0.3, 1) // GREEN
	case CheckFail:
		return matrix.NewColor(0.9, 0.1, 0.1, 1) // RED
	default:
		return matrix.NewColor(0.9, 0.7, 0.1, 1) // AMBER
	}
}

// ---------------------------------------------------------------------------
// VVChecklistItem — one acceptance criterion
// ---------------------------------------------------------------------------

type VVChecklistItem struct {
	ID        string
	Label     string
	Status    CheckStatus
	AutoCheck func() CheckStatus // nil = manual (scientist clicks to toggle)

	// 3D entities
	checkboxEntity *engine.Entity
	checkboxSD     *shader_data_registry.ShaderDataUnlit
	aabb           collision.AABB
}

// ---------------------------------------------------------------------------
// VVChecklist — the physical checklist panel
// ---------------------------------------------------------------------------

type VVChecklist struct {
	host         *engine.Host
	items        []*VVChecklistItem
	summarySD    *shader_data_registry.ShaderDataUnlit
	updateTimer  float64 // Throttle auto-checks to 2 Hz
	panelCenterX float32
	panelCenterZ float32
	nextItemIdx  int // Tracks vertical stacking
}

// NewVVChecklist creates the V&V panel on the desk surface, centered in front
// of the scientist's seated position.
func NewVVChecklist(host *engine.Host) *VVChecklist {
	vc := &VVChecklist{
		host:         host,
		panelCenterX: 0,
		panelCenterZ: float32(deskZ) + 0.0, // Center of desk, front area
	}
	vc.buildPanel(host)
	return vc
}

func (vc *VVChecklist) buildPanel(host *engine.Host) {
	// Background panel — dark slate
	panelW := matrix.Float(0.50)
	panelD := matrix.Float(0.30)
	panelY := matrix.Float(deskY + 0.005)

	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(matrix.NewVec3(
		matrix.Float(vc.panelCenterX), panelY, matrix.Float(vc.panelCenterZ)))
	entity.Transform.SetScale(matrix.NewVec3(panelW, 0.005, panelD))

	mat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	sd := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          matrix.NewColor(0.08, 0.10, 0.14, 1), // Dark slate
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

	// Traffic-light summary — cube at top of panel
	lightEntity := engine.NewEntity(host.WorkGroup())
	lightEntity.Transform.SetPosition(matrix.NewVec3(
		matrix.Float(vc.panelCenterX-0.20),
		panelY+0.02,
		matrix.Float(vc.panelCenterZ)-panelD/2+0.03))
	lightEntity.Transform.SetScale(matrix.NewVec3(0.03, 0.03, 0.03))

	lightSD := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          CheckStatusColor(CheckPending),
		UVs:            matrix.NewVec4(0, 0, 1, 1),
	}
	lightDrawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &lightEntity.Transform,
		ShaderData: lightSD,
		ViewCuller: &host.Cameras.Primary,
	}
	host.Drawings.AddDrawing(lightDrawing)
	vc.summarySD = lightSD

	// Title text: "V&V CHECKLIST"
	titleEntity := engine.NewEntity(host.WorkGroup())
	titleEntity.Transform.SetPosition(matrix.NewVec3(
		matrix.Float(vc.panelCenterX),
		panelY+0.015,
		matrix.Float(vc.panelCenterZ)-panelD/2+0.03))
	titleEntity.Transform.SetScale(matrix.NewVec3(1, 1, 1))
	// Text faces +Y (up from desk) — rotate -90° around X
	titleEntity.Transform.SetRotation(matrix.NewVec3(
		matrix.Float(-math.Pi/2), 0, 0))

	bgColor := matrix.NewColor(0, 0, 0, 0)
	rootScale := matrix.NewVec3(1, 1, 1)

	titleDrawings := host.FontCache().RenderMeshes(
		host,
		"V&V CHECKLIST",
		0, 0, 0,
		0.018,
		0,
		labColIvory(),
		bgColor,
		rendering.FontJustifyCenter,
		rendering.FontBaselineTop,
		rootScale,
		true,
		true,
		rendering.FontRegular,
		0,
		&host.Cameras.Primary,
	)
	for i := range titleDrawings {
		titleDrawings[i].Transform = &titleEntity.Transform
	}
	host.Drawings.AddDrawings(titleDrawings)
}

// ---------------------------------------------------------------------------
// Adding items
// ---------------------------------------------------------------------------

// AddAutoItem adds an auto-checked criterion. The checker function is called
// periodically (2 Hz) and its return value determines the checkbox color.
func (vc *VVChecklist) AddAutoItem(id, label string, checker func() CheckStatus) {
	vc.addItem(id, label, checker)
}

// AddManualItem adds a manually-verified criterion. The scientist clicks the
// checkbox to toggle between PENDING and PASS.
func (vc *VVChecklist) AddManualItem(id, label string) {
	vc.addItem(id, label, nil)
}

func (vc *VVChecklist) addItem(id, label string, checker func() CheckStatus) {
	host := vc.host
	idx := vc.nextItemIdx
	vc.nextItemIdx++

	panelD := float32(0.30)
	rowZ := vc.panelCenterZ - panelD/2 + 0.08 + float32(idx)*0.04
	checkboxX := vc.panelCenterX - 0.20
	checkboxY := float32(deskY) + 0.015

	// Checkbox cube
	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(matrix.NewVec3(
		matrix.Float(checkboxX), matrix.Float(checkboxY), matrix.Float(rowZ)))
	entity.Transform.SetScale(matrix.NewVec3(0.018, 0.018, 0.018))

	mat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	sd := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          CheckStatusColor(CheckPending),
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

	// AABB for raycast hit (generous for steep viewing angles)
	aabb := collision.AABB{
		Center: matrix.NewVec3(matrix.Float(checkboxX), matrix.Float(checkboxY), matrix.Float(rowZ)),
		Extent: matrix.NewVec3(0.02, 0.04, 0.02),
	}

	// Label text (3D SDF, lying on desk surface)
	labelEntity := engine.NewEntity(host.WorkGroup())
	labelEntity.Transform.SetPosition(matrix.NewVec3(
		matrix.Float(checkboxX+0.03), matrix.Float(checkboxY+0.005), matrix.Float(rowZ)))
	labelEntity.Transform.SetScale(matrix.NewVec3(1, 1, 1))
	labelEntity.Transform.SetRotation(matrix.NewVec3(
		matrix.Float(-math.Pi/2), 0, 0))

	bgColor := matrix.NewColor(0, 0, 0, 0)
	rootScale := matrix.NewVec3(1, 1, 1)

	labelDrawings := host.FontCache().RenderMeshes(
		host,
		label,
		0, 0, 0,
		0.012,
		0.35,
		labColIvory(),
		bgColor,
		rendering.FontJustifyLeft,
		rendering.FontBaselineTop,
		rootScale,
		true,
		true,
		rendering.FontRegular,
		0,
		&host.Cameras.Primary,
	)
	for i := range labelDrawings {
		labelDrawings[i].Transform = &labelEntity.Transform
	}
	host.Drawings.AddDrawings(labelDrawings)

	item := &VVChecklistItem{
		ID:             id,
		Label:          label,
		Status:         CheckPending,
		AutoCheck:      checker,
		checkboxEntity: entity,
		checkboxSD:     sd,
		aabb:           aabb,
	}
	vc.items = append(vc.items, item)
}

// ---------------------------------------------------------------------------
// Per-frame update
// ---------------------------------------------------------------------------

// Update runs auto-checkers (throttled to 2 Hz) and handles manual checkbox
// clicks via raycast.
func (vc *VVChecklist) Update(host *engine.Host, dt float64) {
	// Throttle auto-checks
	vc.updateTimer += dt
	if vc.updateTimer >= 0.5 {
		vc.updateTimer = 0
		for _, item := range vc.items {
			if item.AutoCheck != nil {
				newStatus := item.AutoCheck()
				if newStatus != item.Status {
					item.Status = newStatus
					item.checkboxSD.Color = CheckStatusColor(newStatus)
				}
			}
		}
		vc.updateTrafficLight()
	}

	// Manual checkbox click via raycast
	mouse := &host.Window.Mouse
	if mouse.Pressed(hid.MouseButtonLeft) {
		cam := host.PrimaryCamera()
		w, h := host.Window.Width(), host.Window.Height()
		screenCenter := matrix.NewVec2(float32(w)/2, float32(h)/2)
		ray := cam.RayCast(screenCenter)

		for _, item := range vc.items {
			if item.AutoCheck != nil {
				continue // Don't allow manual toggle on auto items
			}
			_, hit := item.aabb.RayHit(ray)
			if hit {
				// Toggle between PENDING and PASS
				if item.Status == CheckPass {
					item.Status = CheckPending
				} else {
					item.Status = CheckPass
				}
				item.checkboxSD.Color = CheckStatusColor(item.Status)
				vc.updateTrafficLight()
				break
			}
		}
	}
}

func (vc *VVChecklist) updateTrafficLight() {
	if vc.summarySD == nil {
		return
	}
	vc.summarySD.Color = CheckStatusColor(vc.OverallStatus())
}

// OverallStatus returns the aggregate V&V status.
func (vc *VVChecklist) OverallStatus() CheckStatus {
	allPass := true
	for _, item := range vc.items {
		if item.Status == CheckFail {
			return CheckFail
		}
		if item.Status != CheckPass {
			allPass = false
		}
	}
	if allPass && len(vc.items) > 0 {
		return CheckPass
	}
	return CheckPending
}

// Reset clears all checklist items (used when switching presets).
func (vc *VVChecklist) Reset() {
	for _, item := range vc.items {
		item.Status = CheckPending
		item.checkboxSD.Color = CheckStatusColor(CheckPending)
	}
	vc.updateTrafficLight()
}
