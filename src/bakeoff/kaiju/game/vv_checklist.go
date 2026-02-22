//go:build !editor

// vv_checklist.go — V&V checklist as screen-space UI panel.
//
// NASA go/no-go style verification displayed as a cockpit-style panel
// at the bottom of the screen. Auto-checked criteria (fringe spacing,
// particle count, visibility) update at 2 Hz. Manual checkboxes are
// toggled with the V key. Traffic-light title color shows overall status.

package main

import (
	"fmt"
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/ui"
	"kaiju/matrix"
	"kaiju/rendering"
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

func checkStatusTag(s CheckStatus) string {
	switch s {
	case CheckPass:
		return "PASS"
	case CheckFail:
		return "FAIL"
	default:
		return "PEND"
	}
}

// ---------------------------------------------------------------------------
// VVChecklistItem — one acceptance criterion
// ---------------------------------------------------------------------------

type VVChecklistItem struct {
	ID        string
	Label     string
	Status    CheckStatus
	AutoCheck func() CheckStatus // nil = manual (scientist presses V to toggle)
	uiLabel   *ui.Label
}

// ---------------------------------------------------------------------------
// VVChecklist — screen-space checklist panel
// ---------------------------------------------------------------------------

type VVChecklist struct {
	host        *engine.Host
	uiMgr       *ui.Manager
	panel       *ui.Panel
	titleLabel  *ui.Label
	items       []*VVChecklistItem
	updateTimer float64
}

// NewVVChecklist creates the V&V panel at the bottom-center of the screen.
func NewVVChecklist(uiMgr *ui.Manager, host *engine.Host) *VVChecklist {
	tex, _ := host.TextureCache().Texture(
		assets.TextureSquare, rendering.TextureFilterLinear)

	w := float32(host.Window.Width())
	h := float32(host.Window.Height())

	panelW := float32(320)
	panelH := float32(150)

	// Position: bottom-center, above the help strip
	panel := uiMgr.Add().ToPanel()
	panel.Init(tex, ui.ElementTypePanel)
	panel.DontFitContent()
	panel.AllowClickThrough()
	panel.SetColor(matrix.NewColor(0.04, 0.06, 0.10, 0.88))
	panel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	panel.Base().Layout().Scale(panelW, panelH)
	panel.Base().Layout().SetOffset(w/2-panelW/2, h-panelH-40)
	panel.Base().Layout().SetPadding(12, 8, 12, 8)

	bc := matrix.NewColor(0.25, 0.3, 0.4, 0.6)
	panel.SetBorderSize(1, 1, 1, 1)
	panel.SetBorderColor(bc, bc, bc, bc)

	// Title label — color reflects overall status (traffic light)
	title := uiMgr.Add().ToLabel()
	title.Init("V&V CHECKLIST")
	title.SetColor(CheckStatusColor(CheckPending))
	title.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	title.SetFontSize(13)
	panel.AddChild(title.Base())

	return &VVChecklist{
		host:       host,
		uiMgr:      uiMgr,
		panel:      panel,
		titleLabel: title,
	}
}

// ---------------------------------------------------------------------------
// Adding items
// ---------------------------------------------------------------------------

// AddAutoItem adds an auto-checked criterion. The checker function is called
// periodically (2 Hz) and its return value determines the status display.
func (vc *VVChecklist) AddAutoItem(id, label string, checker func() CheckStatus) {
	vc.addItem(id, label, checker)
}

// AddManualItem adds a manually-verified criterion. The scientist presses V
// to toggle the next pending manual item to PASS.
func (vc *VVChecklist) AddManualItem(id, label string) {
	vc.addItem(id, label, nil)
}

func (vc *VVChecklist) addItem(id, label string, checker func() CheckStatus) {
	text := fmt.Sprintf("[%s] %s", checkStatusTag(CheckPending), label)
	if checker == nil {
		text += "  (V)" // Hint: press V to verify
	}

	uiLabel := vc.uiMgr.Add().ToLabel()
	uiLabel.Init(text)
	uiLabel.SetColor(CheckStatusColor(CheckPending))
	uiLabel.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	uiLabel.SetFontSize(12)
	vc.panel.AddChild(uiLabel.Base())

	item := &VVChecklistItem{
		ID:        id,
		Label:     label,
		Status:    CheckPending,
		AutoCheck: checker,
		uiLabel:   uiLabel,
	}
	vc.items = append(vc.items, item)
}

// ---------------------------------------------------------------------------
// Per-frame update
// ---------------------------------------------------------------------------

// Update runs auto-checkers (throttled to 2 Hz).
func (vc *VVChecklist) Update(host *engine.Host, dt float64) {
	vc.updateTimer += dt
	if vc.updateTimer >= 0.5 {
		vc.updateTimer = 0
		for _, item := range vc.items {
			if item.AutoCheck != nil {
				newStatus := item.AutoCheck()
				if newStatus != item.Status {
					item.Status = newStatus
					item.uiLabel.SetText(fmt.Sprintf("[%s] %s",
						checkStatusTag(newStatus), item.Label))
					item.uiLabel.SetColor(CheckStatusColor(newStatus))
				}
			}
		}
		vc.updateTrafficLight()
	}
}

func (vc *VVChecklist) updateTrafficLight() {
	if vc.titleLabel != nil {
		vc.titleLabel.SetColor(CheckStatusColor(vc.OverallStatus()))
	}
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

// ToggleNextManual toggles the first PENDING manual item to PASS.
// If all manual items are already PASS, resets them all to PENDING.
func (vc *VVChecklist) ToggleNextManual() {
	// Find first pending manual item
	for _, item := range vc.items {
		if item.AutoCheck == nil && item.Status == CheckPending {
			item.Status = CheckPass
			item.uiLabel.SetText(fmt.Sprintf("[%s] %s  (V)",
				checkStatusTag(CheckPass), item.Label))
			item.uiLabel.SetColor(CheckStatusColor(CheckPass))
			vc.updateTrafficLight()
			return
		}
	}
	// All manual items PASS — reset them to PENDING
	for _, item := range vc.items {
		if item.AutoCheck == nil {
			item.Status = CheckPending
			item.uiLabel.SetText(fmt.Sprintf("[%s] %s  (V)",
				checkStatusTag(CheckPending), item.Label))
			item.uiLabel.SetColor(CheckStatusColor(CheckPending))
		}
	}
	vc.updateTrafficLight()
}

// Reset clears all checklist items (used when switching presets).
func (vc *VVChecklist) Reset() {
	for _, item := range vc.items {
		item.Status = CheckPending
		text := fmt.Sprintf("[%s] %s", checkStatusTag(CheckPending), item.Label)
		if item.AutoCheck == nil {
			text += "  (V)"
		}
		item.uiLabel.SetText(text)
		item.uiLabel.SetColor(CheckStatusColor(CheckPending))
	}
	vc.updateTrafficLight()
}
