//go:build !editor

// monitor_text.go — 3D SDF text rendering on virtual lab monitor surfaces.
//
// Each of the 4 desk monitors shows text content (experiment info, stats,
// verdict, etc.) using dirty-flag updates: text only re-renders when
// content actually changes.

package main

import (
	"kaiju/engine"
	"kaiju/matrix"
	"kaiju/rendering"
	"math"
)

// ---------------------------------------------------------------------------
// MonitorTextBlock — a single monitor's text overlay
// ---------------------------------------------------------------------------

// MonitorTextBlock manages SDF text rendering for one monitor surface.
// It tracks the last-rendered string and only rebuilds geometry when the
// content actually changes (dirty-flag pattern).
type MonitorTextBlock struct {
	host     *engine.Host
	entity   *engine.Entity // Parent entity positioned at monitor location
	drawings []rendering.Drawing
	lastText string
	dirty    bool
	position matrix.Vec3
	fontSize float32
	maxWidth float32
	fgColor  matrix.Color
}

// NewMonitorTextBlock creates a text block anchored at the given world
// position (the center of a monitor's XY slab face).
func NewMonitorTextBlock(host *engine.Host, position matrix.Vec3, fontSize, maxWidth float32, fgColor matrix.Color) *MonitorTextBlock {
	return &MonitorTextBlock{
		host:     host,
		position: position,
		fontSize: fontSize,
		maxWidth: maxWidth,
		fgColor:  fgColor,
	}
}

// SetText updates the text to render. If the text is identical to the
// last-rendered string, this is a no-op (dirty flag stays false).
func (mt *MonitorTextBlock) SetText(text string) {
	if text == mt.lastText {
		return
	}
	mt.lastText = text
	mt.dirty = true
}

// Flush rebuilds the SDF text geometry if (and only if) the content has
// changed since the last Flush. Old text is hidden by deactivating its
// parent entity; a new entity + drawing set is created for the updated
// string.
func (mt *MonitorTextBlock) Flush() {
	if !mt.dirty {
		return
	}
	mt.dirty = false

	// Hide old text by deactivating the previous parent entity.
	// Child drawings inherit the parent's active state, so they
	// disappear without needing per-drawing removal.
	if mt.entity != nil {
		mt.entity.SetActive(false)
	}

	// Create a fresh parent entity at the monitor position.
	mt.entity = engine.NewEntity(mt.host.WorkGroup())
	mt.entity.Transform.SetPosition(mt.position)
	mt.entity.Transform.SetScale(matrix.NewVec3(1, 1, 1))
	// Rotate 180° around Y so text quads face -Z (toward scientist).
	mt.entity.Transform.SetRotation(matrix.NewVec3(0, matrix.Float(math.Pi), 0))

	// Render SDF text meshes.
	// rootScale mirrors X so text reads left-to-right after Y rotation.
	bgColor := matrix.NewColor(0, 0, 0, 0) // Transparent background
	rootScale := matrix.NewVec3(-1, 1, 1)   // Mirror X (combined with Y rotation = correct reading order)

	mt.drawings = mt.host.FontCache().RenderMeshes(
		mt.host,
		mt.lastText,
		0, 0, 0,         // x, y, z offset
		mt.fontSize,      // scale
		mt.maxWidth,      // max width before wrap (0 = no wrap)
		mt.fgColor,       // foreground color
		bgColor,          // background color
		rendering.FontJustifyLeft,  // horizontal justify
		rendering.FontBaselineTop,  // vertical baseline
		rootScale,        // parent transform scale
		true,             // instanced
		true,             // is3D (world-space text)
		rendering.FontRegular,      // font face
		1.3,              // line height multiplier
		&mt.host.Cameras.Primary,   // camera container for 3D text
	)

	// Attach every glyph drawing to the parent entity so they move
	// together and can be deactivated as a group.
	for i := range mt.drawings {
		mt.drawings[i].Transform = &mt.entity.Transform
	}
	mt.host.Drawings.AddDrawings(mt.drawings)
}

// ---------------------------------------------------------------------------
// MonitorTextSystem — manages all 4 desk monitors
// ---------------------------------------------------------------------------

// MonitorTextSystem owns the four MonitorTextBlocks that correspond to
// the 2x2 monitor layout on the scientist's desk.
type MonitorTextSystem struct {
	host        *engine.Host
	leftTop     *MonitorTextBlock // Experiment title + mode
	leftBottom  *MonitorTextBlock // V&V verdict + QBP values
	rightTop    *MonitorTextBlock // Stats (N, fringe contrast)
	rightBottom *MonitorTextBlock // Preset + emission rate info
}

// NewMonitorTextSystem creates the four text blocks positioned at the
// monitor surfaces defined in buildPlatform (lab_game.go).
func NewMonitorTextSystem(host *engine.Host) *MonitorTextSystem {
	// Match flat monitor geometry from buildPlatform (lab_game.go).
	// Flat screens at monitorZ = deskZ + 0.4 = -5.1, facing -Z.
	monitorZ := float32(deskZ + 0.4)
	textZ := monitorZ - 0.02 // Slightly in front of screen surface

	screenH := float32(0.35)
	screenW := float32(0.50)
	gap := float32(0.03)

	bottomEdgeY := float32(camStartY - 0.05 - screenH - screenH/2)
	botCenterY := bottomEdgeY + screenH/2
	topCenterY := bottomEdgeY + screenH + gap + screenH/2

	lCenterX := float32(-0.40) // Left wing center
	rCenterX := float32(0.40)  // Right wing center

	// Text rendering parameters
	fontSize := float32(0.04)
	maxWidth := screenW * 0.9 // Slight inset from screen edge

	mts := &MonitorTextSystem{host: host}

	// Left-Top: experiment title + mode
	mts.leftTop = NewMonitorTextBlock(host,
		matrix.NewVec3(
			matrix.Float(lCenterX),
			matrix.Float(topCenterY),
			matrix.Float(textZ)),
		fontSize, maxWidth, labColIvory())

	// Left-Bottom: V&V verdict + QBP values (amber for emphasis)
	mts.leftBottom = NewMonitorTextBlock(host,
		matrix.NewVec3(
			matrix.Float(lCenterX),
			matrix.Float(botCenterY),
			matrix.Float(textZ)),
		fontSize, maxWidth, labColAmber())

	// Right-Top: stats (particle count, fringe contrast)
	mts.rightTop = NewMonitorTextBlock(host,
		matrix.NewVec3(
			matrix.Float(rCenterX),
			matrix.Float(topCenterY),
			matrix.Float(textZ)),
		fontSize, maxWidth, labColIvory())

	// Right-Bottom: preset name + emission rate info
	mts.rightBottom = NewMonitorTextBlock(host,
		matrix.NewVec3(
			matrix.Float(rCenterX),
			matrix.Float(botCenterY),
			matrix.Float(textZ)),
		fontSize, maxWidth, labColIvory())

	return mts
}

// UpdateAll sets text on all four monitors. Each block only marks itself
// dirty if its text actually changed, so unchanged monitors cost nothing.
func (mts *MonitorTextSystem) UpdateAll(title, verdict, stats, info string) {
	mts.leftTop.SetText(title)
	mts.leftBottom.SetText(verdict)
	mts.rightTop.SetText(stats)
	mts.rightBottom.SetText(info)
}

// Flush is called once per frame. Only monitors whose text changed since
// the last Flush will rebuild their SDF geometry.
func (mts *MonitorTextSystem) Flush() {
	mts.leftTop.Flush()
	mts.leftBottom.Flush()
	mts.rightTop.Flush()
	mts.rightBottom.Flush()
}
