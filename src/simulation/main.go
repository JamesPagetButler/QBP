// QBP Verified Simulation Engine (Phase 4e)
//
// Interactive 3D simulation of the Stern-Gerlach experiment with real-time
// Verification & Validation against Lean-proven physics oracle.
//
// Usage:
//
//	cd src/simulation && go run .
//
// Prerequisites:
//
//	Go 1.21+, system graphics libs (see README.md)
package main

import (
	"fmt"
	"log"
	"path/filepath"

	rl "github.com/gen2brain/raylib-go/raylib"

	"github.com/JamesPagetButler/QBP/simulation/physics"
	"github.com/JamesPagetButler/QBP/simulation/scene"
	"github.com/JamesPagetButler/QBP/simulation/ui"
)

const (
	screenWidth  = 1200
	screenHeight = 700
	title        = "QBP Verified Simulation — Stern-Gerlach"
)

func main() {
	// Find project root for oracle data
	root, err := physics.FindProjectRoot()
	if err != nil {
		log.Fatal("Cannot find QBP project root: ", err)
	}

	// Initialize oracle with committed predictions
	oracle := physics.NewOracle(filepath.Join(root, "proofs"))
	oraclePath := filepath.Join(root, "tests", "oracle_predictions.json")
	if err := oracle.LoadPredictions(oraclePath); err != nil {
		log.Printf("Warning: Could not load oracle predictions: %v", err)
		log.Println("Using analytical fallback (cos²(θ/2) formula)")
	}

	// Initialize window
	rl.InitWindow(screenWidth, screenHeight, title)
	defer rl.CloseWindow()
	rl.SetTargetFPS(60)

	// Camera setup — orbit around the apparatus
	camera := rl.Camera3D{
		Position: rl.NewVector3(0, 8, 15),
		Target:   rl.NewVector3(0, 0, 0),
		Up:       rl.NewVector3(0, 1, 0),
		Fovy:     45,
	}

	// Create scene components
	apparatus := scene.DefaultApparatus()
	particles := scene.NewParticleSystem(oracle, 2000)
	controls := ui.NewControls()

	fmt.Println("QBP Verified Simulation Engine")
	fmt.Println("Press H for help, ESC to quit")

	for !rl.WindowShouldClose() {
		dt := rl.GetFrameTime()

		// Update controls and sync theta
		controls.Update()
		particles.SetTheta(controls.ThetaRad())

		// Handle reset
		if rl.IsKeyPressed(rl.KeyR) {
			particles.Reset()
		}

		// Update camera (orbit mode)
		rl.UpdateCamera(&camera, rl.CameraFree)

		// Update particle simulation
		if !controls.Paused {
			particles.Update(dt)
		}

		// Get oracle predictions for current angle
		theta := controls.ThetaRad()
		oracleProbUp := oracle.ProbUp(theta)
		oracleProbDown := oracle.ProbDown(theta)

		// Get simulation statistics
		simUp, simDown, simTotal := particles.Stats()

		// Draw
		rl.BeginDrawing()
		rl.ClearBackground(rl.NewColor(15, 15, 25, 255))

		// 3D scene
		rl.BeginMode3D(camera)
		rl.DrawGrid(20, 1)
		apparatus.Draw()
		particles.Draw()
		rl.EndMode3D()

		// 2D overlay
		apparatus.DrawLabels(camera)
		controls.DrawSlider()
		controls.DrawVVStatus(screenWidth, oracleProbUp, oracleProbDown,
			simUp, simDown, simTotal)
		controls.DrawPauseIndicator(screenWidth)
		controls.DrawHelp(screenWidth, screenHeight)

		// FPS counter
		rl.DrawFPS(screenWidth-90, screenHeight-25)

		rl.EndDrawing()
	}
}
