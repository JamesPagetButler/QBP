//go:build !editor

// Virtual Monitor System for QBP Lab
//
// Each physical monitor on the desk is a "VM" that displays 3D content on its
// surface. Since Kaiju doesn't expose the Renderer to game code (needed for
// texture.WritePixels), we render monitor content as 3D entities positioned
// ON the monitor surface — colored cubes for histogram bars, verdict blocks, etc.
//
// This approach (recommended by Gemini review) is faster than texture uploads
// and stays within Kaiju's entity/transform model.

package main

import (
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/matrix"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
)

// MonitorContent represents the 3D entities rendered on a monitor surface.
// Verdict and stats display is now handled by MonitorTextSystem (3D SDF text).
// This struct retains only the histogram bars on the right monitor.
type MonitorContent struct {
	host *engine.Host

	// Histogram bars (right monitor)
	histBars    []*engine.Entity
	histDrawing []rendering.Drawing
	numBars     int
}

const monitorHistBars = 40 // Number of histogram bars on monitor

// NewMonitorContent creates the 3D entities for both monitors.
// Left monitor = stats/verdict, Right monitor = histogram.
func NewMonitorContent(host *engine.Host) *MonitorContent {
	mc := &MonitorContent{
		host:    host,
		numBars: monitorHistBars,
	}
	mc.buildHistogramMonitor(host)
	return mc
}

// ---------------------------------------------------------------------------
// Right Monitor — Histogram (3D bars on the XY slab)
// ---------------------------------------------------------------------------
//
// Right monitor XY slab is at:
//   center X = rCornerX - halfW/2 = 0.65 - 0.15 = 0.50
//   center Z = cornerZ = deskZ + 0.4 = -5.1
//   The slab faces -Z (toward scientist)
//   Screen area: halfW=0.30 wide (X), screenH=0.35 tall (Y)
//   Two stacked — use bottom one for histogram

func (mc *MonitorContent) buildHistogramMonitor(host *engine.Host) {
	rCenterX := matrix.Float(0.65) // Match flat monitor layout
	screenW := matrix.Float(0.50)
	screenH := matrix.Float(0.35)
	bottomEdgeY := matrix.Float(camStartY - 0.05 - screenH - screenH/2)
	monitorZ := matrix.Float(deskZ + 0.4)

	// Histogram bars on the bottom-right flat screen
	barAreaW := screenW * 0.85 // Leave margin
	barW := barAreaW / matrix.Float(monitorHistBars)
	barMaxH := screenH * 0.8
	startX := rCenterX - screenW/2 + (screenW-barAreaW)/2 + barW/2

	mc.histBars = make([]*engine.Entity, monitorHistBars)
	mc.histDrawing = make([]rendering.Drawing, monitorHistBars)

	for i := 0; i < monitorHistBars; i++ {
		mesh := rendering.NewMeshCube(host.MeshCache())
		entity := engine.NewEntity(host.WorkGroup())

		x := startX + matrix.Float(i)*barW
		y := bottomEdgeY + barMaxH*0.01 // Base of bar
		z := monitorZ - 0.015           // Slightly in front of screen surface

		entity.Transform.SetPosition(matrix.NewVec3(x, y, z))
		entity.Transform.SetScale(matrix.NewVec3(barW*0.8, 0.001, 0.005)) // Thin, almost invisible initially

		mat, err := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
		if err != nil {
			continue
		}

		sd := &shader_data_registry.ShaderDataUnlit{
			ShaderDataBase: rendering.NewShaderDataBase(),
			Color:          labColOchre(),
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

		mc.histBars[i] = entity
		mc.histDrawing[i] = drawing
	}

	_ = barMaxH // used in UpdateHistogram
}

// ---------------------------------------------------------------------------
// Per-frame Updates
// ---------------------------------------------------------------------------

// UpdateHistogram updates the 3D histogram bars from detector data.
func (mc *MonitorContent) UpdateHistogram(histogram [dsHistogramBins]int) {
	// Find max bin value
	maxBin := 1
	for _, v := range histogram {
		if v > maxBin {
			maxBin = v
		}
	}

	screenH := matrix.Float(0.35)
	barMaxH := screenH * 0.8
	bottomEdgeY := matrix.Float(camStartY - 0.05 - screenH - screenH/2)

	binsPerBar := dsHistogramBins / monitorHistBars

	for i := 0; i < monitorHistBars && i < len(mc.histBars); i++ {
		// Sum bins for this bar
		total := 0
		for j := 0; j < binsPerBar; j++ {
			idx := i*binsPerBar + j
			if idx < dsHistogramBins {
				total += histogram[idx]
			}
		}

		h := matrix.Float(total) / matrix.Float(maxBin) * barMaxH
		if h < 0.001 {
			h = 0.001
		}

		entity := mc.histBars[i]
		pos := entity.Transform.Position()
		screenW := matrix.Float(0.50)
		barAreaW := screenW * 0.85
		barW := barAreaW / matrix.Float(monitorHistBars)

		entity.Transform.SetScale(matrix.NewVec3(barW*0.8, h, 0.005))
		entity.Transform.SetPosition(matrix.NewVec3(pos.X(), bottomEdgeY+h/2, pos.Z()))
	}
}

