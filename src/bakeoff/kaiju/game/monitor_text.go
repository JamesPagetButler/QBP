//go:build !editor

// monitor_text.go — Screen-space UI panels for lab data display.
//
// Replaces the broken 3D SDF text approach with Kaiju's HTML/CSS UI system.
// Four panels at screen corners show experiment info, verdict, stats, and
// status — styled as translucent cockpit instruments over the 3D lab view.

package main

import (
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/ui"
	"kaiju/matrix"
	"kaiju/rendering"
)

// ---------------------------------------------------------------------------
// MonitorTextBlock — one screen-space info panel
// ---------------------------------------------------------------------------

// MonitorTextBlock manages a screen-space UI panel with a header label
// and a content label. Text updates use a dirty-flag pattern — the label
// only redraws when content actually changes.
type MonitorTextBlock struct {
	header   *ui.Label
	content  *ui.Label
	lastText string
}

// newMonitorTextBlock creates a panel with header and content labels.
func newMonitorTextBlock(uiMgr *ui.Manager, tex *rendering.Texture,
	x, y, w, h float32, headerText string, fgColor matrix.Color) *MonitorTextBlock {

	// Background panel — dark translucent slate
	panel := uiMgr.Add().ToPanel()
	panel.Init(tex, ui.ElementTypePanel)
	panel.DontFitContent()
	panel.AllowClickThrough()
	panel.SetColor(matrix.NewColor(0.05, 0.07, 0.12, 0.85))
	panel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	panel.Base().Layout().Scale(w, h)
	panel.Base().Layout().SetOffset(x, y)
	panel.Base().Layout().SetPadding(10, 8, 10, 8)

	// Subtle border
	bc := matrix.NewColor(0.25, 0.3, 0.4, 0.6)
	panel.SetBorderSize(1, 1, 1, 1)
	panel.SetBorderColor(bc, bc, bc, bc)

	// Header label (small, amber)
	header := uiMgr.Add().ToLabel()
	header.Init(headerText)
	header.SetColor(labColAmber())
	header.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	header.SetFontSize(11)
	panel.AddChild(header.Base())

	// Content label
	content := uiMgr.Add().ToLabel()
	content.Init("")
	content.SetColor(fgColor)
	content.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	content.SetFontSize(14)
	panel.AddChild(content.Base())

	return &MonitorTextBlock{
		header:  header,
		content: content,
	}
}

// SetText updates the content label. No-op if text hasn't changed.
func (mt *MonitorTextBlock) SetText(text string) {
	if text == mt.lastText {
		return
	}
	mt.lastText = text
	mt.content.SetText(text)
}

// ---------------------------------------------------------------------------
// MonitorTextSystem — manages the four cockpit-style info panels
// ---------------------------------------------------------------------------

// MonitorTextSystem owns the four MonitorTextBlocks positioned at the
// screen corners, replacing the old 3D monitor text approach.
type MonitorTextSystem struct {
	leftTop     *MonitorTextBlock // Experiment title + mode
	leftBottom  *MonitorTextBlock // V&V verdict + QBP values
	rightTop    *MonitorTextBlock // Stats (N, fringe contrast)
	rightBottom *MonitorTextBlock // Preset + emission rate info
}

// NewMonitorTextSystem creates the four UI panels at screen corners.
func NewMonitorTextSystem(uiMgr *ui.Manager, host *engine.Host) *MonitorTextSystem {
	tex, _ := host.TextureCache().Texture(
		assets.TextureSquare, rendering.TextureFilterLinear)

	w := float32(host.Window.Width())

	// Layout: two columns at screen edges
	panelW := float32(260)
	panelH := float32(80)
	margin := float32(15)
	gap := float32(8)

	mts := &MonitorTextSystem{}

	mts.leftTop = newMonitorTextBlock(uiMgr, tex,
		margin, margin, panelW, panelH,
		"EXPERIMENT", labColIvory())

	mts.leftBottom = newMonitorTextBlock(uiMgr, tex,
		margin, margin+panelH+gap, panelW, panelH,
		"VERDICT", labColAmber())

	mts.rightTop = newMonitorTextBlock(uiMgr, tex,
		w-margin-panelW, margin, panelW, panelH,
		"STATISTICS", labColIvory())

	mts.rightBottom = newMonitorTextBlock(uiMgr, tex,
		w-margin-panelW, margin+panelH+gap, panelW, panelH,
		"STATUS", labColIvory())

	return mts
}

// UpdateAll sets text on all four panels. Each block only updates the
// label if its text actually changed.
func (mts *MonitorTextSystem) UpdateAll(title, verdict, stats, info string) {
	mts.leftTop.SetText(title)
	mts.leftBottom.SetText(verdict)
	mts.rightTop.SetText(stats)
	mts.rightBottom.SetText(info)
}

// Flush is a no-op — UI labels update immediately via SetText.
// Kept for API compatibility with the old 3D SDF approach.
func (mts *MonitorTextSystem) Flush() {}
