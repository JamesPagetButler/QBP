// Package ui provides parameter sliders and V&V status display for the simulation.
package ui

import (
	"fmt"
	"math"

	rl "github.com/gen2brain/raylib-go/raylib"
)

// Controls holds the interactive UI state.
type Controls struct {
	ThetaDeg    float32 // angle in degrees (0-180)
	Paused      bool
	ShowHelp    bool
	SliderRect  rl.Rectangle
	dragging    bool
}

// NewControls creates controls with default settings.
func NewControls() *Controls {
	return &Controls{
		ThetaDeg:   90,
		SliderRect: rl.NewRectangle(20, 60, 200, 20),
	}
}

// ThetaRad returns the current angle in radians.
func (c *Controls) ThetaRad() float64 {
	return float64(c.ThetaDeg) * math.Pi / 180.0
}

// Update processes input for the controls.
func (c *Controls) Update() {
	mouse := rl.GetMousePosition()

	// Slider interaction
	sliderArea := rl.NewRectangle(c.SliderRect.X-5, c.SliderRect.Y-5,
		c.SliderRect.Width+10, c.SliderRect.Height+10)

	if rl.IsMouseButtonPressed(rl.MouseLeftButton) &&
		rl.CheckCollisionPointRec(mouse, sliderArea) {
		c.dragging = true
	}
	if rl.IsMouseButtonReleased(rl.MouseLeftButton) {
		c.dragging = false
	}

	if c.dragging {
		t := (mouse.X - c.SliderRect.X) / c.SliderRect.Width
		if t < 0 {
			t = 0
		}
		if t > 1 {
			t = 1
		}
		c.ThetaDeg = t * 180
	}

	// Keyboard shortcuts
	if rl.IsKeyPressed(rl.KeySpace) {
		c.Paused = !c.Paused
	}
	if rl.IsKeyPressed(rl.KeyH) {
		c.ShowHelp = !c.ShowHelp
	}
	if rl.IsKeyPressed(rl.KeyR) {
		// Reset signal handled in main
	}

	// Arrow keys for fine angle adjustment
	if rl.IsKeyDown(rl.KeyRight) {
		c.ThetaDeg += 0.5
		if c.ThetaDeg > 180 {
			c.ThetaDeg = 180
		}
	}
	if rl.IsKeyDown(rl.KeyLeft) {
		c.ThetaDeg -= 0.5
		if c.ThetaDeg < 0 {
			c.ThetaDeg = 0
		}
	}
}

// DrawSlider renders the angle parameter slider.
func (c *Controls) DrawSlider() {
	// Background
	rl.DrawRectangleRec(c.SliderRect, rl.NewColor(60, 60, 60, 200))
	rl.DrawRectangleLinesEx(c.SliderRect, 1, rl.Gray)

	// Fill
	t := c.ThetaDeg / 180.0
	fillRect := rl.NewRectangle(c.SliderRect.X, c.SliderRect.Y,
		c.SliderRect.Width*t, c.SliderRect.Height)
	rl.DrawRectangleRec(fillRect, rl.NewColor(100, 200, 255, 180))

	// Thumb
	thumbX := c.SliderRect.X + c.SliderRect.Width*t
	rl.DrawCircle(int32(thumbX), int32(c.SliderRect.Y+c.SliderRect.Height/2),
		8, rl.White)

	// Label
	label := fmt.Sprintf("theta = %.1f deg", c.ThetaDeg)
	rl.DrawText(label, int32(c.SliderRect.X), int32(c.SliderRect.Y)-18, 16, rl.White)
}

// DrawVVStatus renders the Verification & Validation status panel.
func (c *Controls) DrawVVStatus(screenW, probUp, probDown float64,
	simUp, simDown, simTotal int) {

	panelX := int32(screenW) - 280
	panelY := int32(20)
	panelW := int32(260)

	// Background
	rl.DrawRectangle(panelX, panelY, panelW, 200, rl.NewColor(30, 30, 30, 220))
	rl.DrawRectangleLines(panelX, panelY, panelW, 200, rl.Gray)

	// Title
	rl.DrawText("V&V Status", panelX+10, panelY+10, 18, rl.White)
	rl.DrawLine(panelX+10, panelY+32, panelX+panelW-10, panelY+32, rl.Gray)

	// Oracle predictions
	rl.DrawText("Oracle (Lean-proven):", panelX+10, panelY+40, 14, rl.LightGray)
	oracleUp := fmt.Sprintf("  P(+) = %.4f", probUp)
	oracleDown := fmt.Sprintf("  P(-) = %.4f", probDown)
	rl.DrawText(oracleUp, panelX+10, panelY+58, 14, rl.NewColor(100, 255, 255, 255))
	rl.DrawText(oracleDown, panelX+10, panelY+74, 14, rl.NewColor(255, 150, 50, 255))

	// Simulation results
	rl.DrawText("Simulation:", panelX+10, panelY+96, 14, rl.LightGray)
	if simTotal > 0 {
		simProbUp := float64(simUp) / float64(simTotal)
		simProbDown := float64(simDown) / float64(simTotal)
		simUpStr := fmt.Sprintf("  P(+) = %.4f (%d/%d)", simProbUp, simUp, simTotal)
		simDownStr := fmt.Sprintf("  P(-) = %.4f (%d/%d)", simProbDown, simDown, simTotal)
		rl.DrawText(simUpStr, panelX+10, panelY+114, 14, rl.NewColor(100, 255, 255, 255))
		rl.DrawText(simDownStr, panelX+10, panelY+130, 14, rl.NewColor(255, 150, 50, 255))

		// V&V verdict
		diff := math.Abs(probUp - simProbUp)
		verdict := "PASS"
		verdictColor := rl.Green
		if simTotal < 100 {
			verdict = "COLLECTING..."
			verdictColor = rl.Yellow
		} else if diff > 0.05 { // 5% tolerance for visual
			verdict = "DIVERGENCE"
			verdictColor = rl.Red
		}
		rl.DrawText(fmt.Sprintf("Verdict: %s (d=%.4f)", verdict, diff),
			panelX+10, panelY+155, 14, verdictColor)
		rl.DrawText(fmt.Sprintf("N = %d", simTotal), panelX+10, panelY+175, 12, rl.Gray)
	} else {
		rl.DrawText("  (no data yet)", panelX+10, panelY+114, 14, rl.Gray)
	}
}

// DrawHelp renders the help overlay.
func (c *Controls) DrawHelp(screenW, screenH int32) {
	if !c.ShowHelp {
		// Just show hint
		rl.DrawText("Press H for help", 20, screenH-25, 12, rl.Gray)
		return
	}

	// Semi-transparent overlay
	rl.DrawRectangle(screenW/4, screenH/4, screenW/2, screenH/2,
		rl.NewColor(20, 20, 20, 230))
	rl.DrawRectangleLines(screenW/4, screenH/4, screenW/2, screenH/2, rl.White)

	x := screenW/4 + 20
	y := screenH/4 + 20
	rl.DrawText("QBP Verified Simulation — Controls", x, y, 20, rl.White)
	y += 35
	rl.DrawText("Mouse drag    Rotate camera", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("Scroll        Zoom in/out", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("Left/Right    Adjust angle", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("Slider        Set theta (0-180 deg)", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("Space         Pause/Resume", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("R             Reset statistics", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("H             Toggle this help", x, y, 14, rl.LightGray)
	y += 20
	rl.DrawText("ESC           Quit", x, y, 14, rl.LightGray)
	y += 35
	rl.DrawText("V&V: Oracle predictions from Lean proofs.", x, y, 12, rl.Gray)
	y += 18
	rl.DrawText("Simulation uses same physics, run stochastically.", x, y, 12, rl.Gray)
}

// DrawPauseIndicator shows a pause indicator when simulation is paused.
func (c *Controls) DrawPauseIndicator(screenW int32) {
	if c.Paused {
		rl.DrawText("PAUSED", screenW/2-40, 20, 24, rl.Yellow)
	}
}
