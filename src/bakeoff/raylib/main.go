// Double-Slit Bake-Off Prototype — Raylib
//
// Minimal double-slit simulation exercising: 3D scene on a lab bench,
// particle accumulation (Tonomura-style), 2D histogram overlay, parameter
// slider (slit separation d), FPS camera + right-click orbit, and
// QBP design system colors.
//
// Usage:
//
//	cd src/bakeoff/raylib && go run .
package main

import (
	"encoding/csv"
	"fmt"
	"math"
	"math/rand"
	"os"
	"runtime"
	"strconv"
	"time"

	rl "github.com/gen2brain/raylib-go/raylib"
)

// ---------------------------------------------------------------------------
// Design System Colors (from docs/design-system.md)
// ---------------------------------------------------------------------------

var (
	colVerdantNight = rl.NewColor(13, 40, 32, 255)    // #0D2820 — background
	colMidnight     = rl.NewColor(13, 27, 42, 255)     // #0D1B2A — floor
	colBrass        = rl.NewColor(212, 165, 116, 255)   // #D4A574 — primary metal
	colCopper       = rl.NewColor(184, 115, 51, 255)    // #B87333 — secondary metal
	colBronze       = rl.NewColor(205, 127, 50, 255)    // #CD7F32 — mechanisms
	colSteel        = rl.NewColor(113, 121, 126, 255)   // #71797E — muted elements
	colIvory        = rl.NewColor(255, 254, 240, 255)   // #FFFEF0 — labels
	colAmber        = rl.NewColor(244, 162, 97, 255)    // #F4A261 — warnings
	colOchre        = rl.NewColor(212, 170, 90, 255)    // #D4AA5A — warm glow
	colGold         = rl.NewColor(255, 215, 0, 255)     // #FFD700 — particle
	colSage         = rl.NewColor(61, 139, 110, 255)    // #3D8B6E — V&V pass
)

// ---------------------------------------------------------------------------
// Physics Constants & Engine
// ---------------------------------------------------------------------------

const (
	defaultSlitSep    = 1.0e-6  // d = 1 μm
	defaultWavelength = 5.0e-11 // λ = 50 pm (electron)
	defaultScreenDist = 1.0     // L = 1 m
	defaultSlitWidth  = 1.0e-7  // a = 0.1 μm
	histBins          = 100
)

type PhysicsEngine struct {
	SlitSep    float64
	Wavelength float64
	ScreenDist float64
	SlitWidth  float64
	rng        *rand.Rand
}

func NewPhysicsEngine() *PhysicsEngine {
	return &PhysicsEngine{
		SlitSep:    defaultSlitSep,
		Wavelength: defaultWavelength,
		ScreenDist: defaultScreenDist,
		SlitWidth:  defaultSlitWidth,
		rng:        rand.New(rand.NewSource(42)),
	}
}

func (e *PhysicsEngine) FringeSpacing() float64 {
	return e.Wavelength * e.ScreenDist / e.SlitSep
}

// Intensity computes the Fraunhofer double-slit pattern at position x (meters).
// I(x) = cos²(πdx/λL) · sinc²(πax/λL)
func (e *PhysicsEngine) Intensity(x float64) float64 {
	argD := math.Pi * e.SlitSep * x / (e.Wavelength * e.ScreenDist)
	argA := math.Pi * e.SlitWidth * x / (e.Wavelength * e.ScreenDist)

	cos2 := math.Cos(argD) * math.Cos(argD)

	// sinc²
	sinc2 := 1.0
	if math.Abs(argA) > 1e-12 {
		s := math.Sin(argA) / argA
		sinc2 = s * s
	}
	return cos2 * sinc2
}

// SampleHitPosition uses rejection sampling to draw a hit position from I(x).
// Returns x in meters within ±numFringes × fringeSpacing.
func (e *PhysicsEngine) SampleHitPosition() float64 {
	halfWidth := 5.0 * e.FringeSpacing()
	for {
		x := (e.rng.Float64()*2 - 1) * halfWidth
		if e.rng.Float64() < e.Intensity(x) {
			return x
		}
	}
}

// ---------------------------------------------------------------------------
// Coordinate Mapper: Physical (meters) ↔ NDU (normalized display units)
// ---------------------------------------------------------------------------

type CoordMapper struct {
	PhysHalfWidth float64 // meters: 5 × fringe spacing
	NDUHalfWidth  float32 // fixed at 5.0 NDU
}

func NewCoordMapper(fringeSpacing float64) *CoordMapper {
	return &CoordMapper{
		PhysHalfWidth: 5.0 * fringeSpacing,
		NDUHalfWidth:  5.0,
	}
}

func (cm *CoordMapper) PhysToNDU(x float64) float32 {
	return float32(x/cm.PhysHalfWidth) * cm.NDUHalfWidth
}

func (cm *CoordMapper) Update(fringeSpacing float64) {
	cm.PhysHalfWidth = 5.0 * fringeSpacing
}

// ---------------------------------------------------------------------------
// Particle System: Tonomura-style accumulation
// ---------------------------------------------------------------------------

type ScreenHit struct {
	PhysX float64 // meters
	NDUX  float32 // display x
	NDUY  float32 // display y (small random spread)
}

type ParticleSystem struct {
	Hits      []ScreenHit
	Histogram [histBins]int
	engine    *PhysicsEngine
	mapper    *CoordMapper
	emitRate  float32 // particles per second
	emitTimer float32
	rng       *rand.Rand
}

func NewParticleSystem(engine *PhysicsEngine, mapper *CoordMapper) *ParticleSystem {
	return &ParticleSystem{
		Hits:     make([]ScreenHit, 0, 10000),
		engine:   engine,
		mapper:   mapper,
		emitRate: 50,
		rng:      rand.New(rand.NewSource(99)),
	}
}

func (ps *ParticleSystem) Update(dt float32) {
	ps.emitTimer += dt
	interval := 1.0 / ps.emitRate
	for ps.emitTimer >= interval {
		ps.emitTimer -= interval
		ps.emit()
	}
}

func (ps *ParticleSystem) emit() {
	x := ps.engine.SampleHitPosition()
	ndux := ps.mapper.PhysToNDU(x)
	nduy := float32(ps.rng.Float64()-0.5) * 0.3 // small vertical spread

	ps.Hits = append(ps.Hits, ScreenHit{PhysX: x, NDUX: ndux, NDUY: nduy})

	// Update histogram
	t := (x/ps.mapper.PhysHalfWidth + 1) / 2 // normalize to [0,1]
	bin := int(t * histBins)
	if bin < 0 {
		bin = 0
	}
	if bin >= histBins {
		bin = histBins - 1
	}
	ps.Histogram[bin]++
}

func (ps *ParticleSystem) Reset() {
	ps.Hits = ps.Hits[:0]
	ps.Histogram = [histBins]int{}
}

// ---------------------------------------------------------------------------
// Slider UI
// ---------------------------------------------------------------------------

type Slider struct {
	Label    string
	Rect     rl.Rectangle
	Value    float32 // normalized 0..1
	Min, Max float64 // physical range
	dragging bool
}

func (s *Slider) PhysValue() float64 {
	// Log-scale slider for slit separation
	logMin := math.Log10(s.Min)
	logMax := math.Log10(s.Max)
	return math.Pow(10, logMin+float64(s.Value)*(logMax-logMin))
}

func (s *Slider) Update() {
	mouse := rl.GetMousePosition()
	area := rl.NewRectangle(s.Rect.X-5, s.Rect.Y-5, s.Rect.Width+10, s.Rect.Height+10)

	if rl.IsMouseButtonPressed(rl.MouseLeftButton) && rl.CheckCollisionPointRec(mouse, area) {
		s.dragging = true
	}
	if rl.IsMouseButtonReleased(rl.MouseLeftButton) {
		s.dragging = false
	}
	if s.dragging {
		t := (mouse.X - s.Rect.X) / s.Rect.Width
		if t < 0 {
			t = 0
		}
		if t > 1 {
			t = 1
		}
		s.Value = t
	}
}

func (s *Slider) Draw() {
	// Track
	rl.DrawRectangleRec(s.Rect, rl.NewColor(60, 60, 60, 200))
	rl.DrawRectangleLinesEx(s.Rect, 1, colSteel)

	// Fill
	fill := rl.NewRectangle(s.Rect.X, s.Rect.Y, s.Rect.Width*s.Value, s.Rect.Height)
	rl.DrawRectangleRec(fill, rl.NewColor(colBrass.R, colBrass.G, colBrass.B, 180))

	// Thumb
	thumbX := s.Rect.X + s.Rect.Width*s.Value
	rl.DrawCircle(int32(thumbX), int32(s.Rect.Y+s.Rect.Height/2), 8, colIvory)

	// Label
	val := s.PhysValue()
	label := fmt.Sprintf("%s = %.2f um", s.Label, val*1e6)
	rl.DrawText(label, int32(s.Rect.X), int32(s.Rect.Y)-18, 16, colIvory)
}

// ---------------------------------------------------------------------------
// Camera: FPS (default) + Right-click Orbit
// ---------------------------------------------------------------------------

type CameraMode int

const (
	ModeFPS CameraMode = iota
	ModeOrbit
)

type LabCamera struct {
	Camera   rl.Camera3D
	Mode     CameraMode
	Yaw      float32 // radians
	Pitch    float32 // radians
	Speed    float32
	Sens     float32
	OrbitDist float32
}

func NewLabCamera() *LabCamera {
	cam := &LabCamera{
		Camera: rl.Camera3D{
			Position: rl.NewVector3(0, 3, 18),
			Target:   rl.NewVector3(0, 1, 0),
			Up:       rl.NewVector3(0, 1, 0),
			Fovy:     50,
		},
		Yaw:      -math.Pi / 2, // facing -Z
		Pitch:    -0.15,
		Speed:    8.0,
		Sens:     0.003,
		OrbitDist: 15,
	}
	return cam
}

func (lc *LabCamera) Update(dt float32, uiHover bool) {
	if uiHover {
		return
	}

	if rl.IsMouseButtonDown(rl.MouseRightButton) {
		lc.Mode = ModeOrbit
	} else {
		lc.Mode = ModeFPS
	}

	// Mouse look (both modes)
	mouseDelta := rl.GetMouseDelta()

	// Scroll
	scroll := rl.GetMouseWheelMove()

	switch lc.Mode {
	case ModeFPS:
		lc.Yaw += mouseDelta.X * lc.Sens
		lc.Pitch -= mouseDelta.Y * lc.Sens

		// Clamp pitch
		if lc.Pitch > 1.4 {
			lc.Pitch = 1.4
		}
		if lc.Pitch < -1.4 {
			lc.Pitch = -1.4
		}

		// Forward/right vectors from yaw
		fwd := rl.NewVector3(
			float32(math.Cos(float64(lc.Yaw))),
			0,
			float32(math.Sin(float64(lc.Yaw))),
		)
		right := rl.NewVector3(-fwd.Z, 0, fwd.X)

		// WASD movement
		moveSpeed := lc.Speed * dt
		if scroll != 0 {
			lc.Speed += scroll * 2
			if lc.Speed < 1 {
				lc.Speed = 1
			}
			if lc.Speed > 30 {
				lc.Speed = 30
			}
		}

		if rl.IsKeyDown(rl.KeyW) {
			lc.Camera.Position.X += fwd.X * moveSpeed
			lc.Camera.Position.Z += fwd.Z * moveSpeed
		}
		if rl.IsKeyDown(rl.KeyS) {
			lc.Camera.Position.X -= fwd.X * moveSpeed
			lc.Camera.Position.Z -= fwd.Z * moveSpeed
		}
		if rl.IsKeyDown(rl.KeyA) {
			lc.Camera.Position.X -= right.X * moveSpeed
			lc.Camera.Position.Z -= right.Z * moveSpeed
		}
		if rl.IsKeyDown(rl.KeyD) {
			lc.Camera.Position.X += right.X * moveSpeed
			lc.Camera.Position.Z += right.Z * moveSpeed
		}

		// Update target from yaw/pitch
		dir := rl.NewVector3(
			float32(math.Cos(float64(lc.Pitch))*math.Cos(float64(lc.Yaw))),
			float32(math.Sin(float64(lc.Pitch))),
			float32(math.Cos(float64(lc.Pitch))*math.Sin(float64(lc.Yaw))),
		)
		lc.Camera.Target = rl.NewVector3(
			lc.Camera.Position.X+dir.X,
			lc.Camera.Position.Y+dir.Y,
			lc.Camera.Position.Z+dir.Z,
		)

	case ModeOrbit:
		lc.Yaw += mouseDelta.X * lc.Sens
		lc.Pitch -= mouseDelta.Y * lc.Sens
		if lc.Pitch > 1.4 {
			lc.Pitch = 1.4
		}
		if lc.Pitch < -1.4 {
			lc.Pitch = -1.4
		}

		lc.OrbitDist -= scroll
		if lc.OrbitDist < 3 {
			lc.OrbitDist = 3
		}
		if lc.OrbitDist > 40 {
			lc.OrbitDist = 40
		}

		// Orbit around target
		target := rl.NewVector3(0, 1.5, 0) // bench center
		lc.Camera.Position = rl.NewVector3(
			target.X+lc.OrbitDist*float32(math.Cos(float64(lc.Pitch))*math.Cos(float64(lc.Yaw))),
			target.Y+lc.OrbitDist*float32(math.Sin(float64(lc.Pitch))),
			target.Z+lc.OrbitDist*float32(math.Cos(float64(lc.Pitch))*math.Sin(float64(lc.Yaw))),
		)
		lc.Camera.Target = target
	}
}

// ---------------------------------------------------------------------------
// Scene Geometry: Lab Bench with Double-Slit Apparatus
// ---------------------------------------------------------------------------

func drawLabBench() {
	// Bench top (long table along Z-axis)
	benchY := float32(0.0)
	rl.DrawCube(rl.NewVector3(0, benchY, 0), 3, 0.15, 22, colBronze)
	rl.DrawCubeWires(rl.NewVector3(0, benchY, 0), 3, 0.15, 22, colCopper)

	// Bench legs
	legH := float32(2.0)
	legW := float32(0.15)
	for _, z := range []float32{-9, -3, 3, 9} {
		for _, x := range []float32{-1.2, 1.2} {
			rl.DrawCube(rl.NewVector3(x, benchY-legH/2, z), legW, legH, legW, colCopper)
		}
	}

	// Floor
	rl.DrawPlane(rl.NewVector3(0, benchY-legH-0.01, 0), rl.NewVector2(40, 40), colMidnight)

	// Floor grid
	gridColor := rl.NewColor(colSteel.R, colSteel.G, colSteel.B, 40)
	for i := -20; i <= 20; i++ {
		f := float32(i)
		rl.DrawLine3D(rl.NewVector3(f, benchY-legH, -20), rl.NewVector3(f, benchY-legH, 20), gridColor)
		rl.DrawLine3D(rl.NewVector3(-20, benchY-legH, f), rl.NewVector3(20, benchY-legH, f), gridColor)
	}
}

func drawSource(z float32) {
	y := float32(0.5)
	rl.DrawCube(rl.NewVector3(0, y, z), 0.8, 0.8, 0.8, colBrass)
	rl.DrawCubeWires(rl.NewVector3(0, y, z), 0.8, 0.8, 0.8, colCopper)
}

func drawBarrier(z float32, slitSepNDU float32) {
	y := float32(0.5)
	barrierH := float32(3.0)
	barrierW := float32(5.0)
	slitW := float32(0.05) // visual slit width
	thickness := float32(0.1)

	halfSep := slitSepNDU / 2

	// Left section
	leftW := (barrierW/2 - halfSep - slitW/2)
	if leftW > 0 {
		leftX := -(halfSep + slitW/2 + leftW/2)
		rl.DrawCube(rl.NewVector3(leftX, y+barrierH/2, z), leftW, barrierH, thickness, colSteel)
		rl.DrawCubeWires(rl.NewVector3(leftX, y+barrierH/2, z), leftW, barrierH, thickness, colBrass)
	}

	// Center section (between slits)
	centerW := slitSepNDU - slitW
	if centerW > 0 {
		rl.DrawCube(rl.NewVector3(0, y+barrierH/2, z), centerW, barrierH, thickness, colSteel)
		rl.DrawCubeWires(rl.NewVector3(0, y+barrierH/2, z), centerW, barrierH, thickness, colBrass)
	}

	// Right section
	rightW := leftW
	if rightW > 0 {
		rightX := halfSep + slitW/2 + rightW/2
		rl.DrawCube(rl.NewVector3(rightX, y+barrierH/2, z), rightW, barrierH, thickness, colSteel)
		rl.DrawCubeWires(rl.NewVector3(rightX, y+barrierH/2, z), rightW, barrierH, thickness, colBrass)
	}
}

func drawDetectorScreen(z float32) {
	y := float32(0.5)
	screenH := float32(4.0)
	screenW := float32(10.0)
	rl.DrawCube(rl.NewVector3(0, y+screenH/2, z), screenW, screenH, 0.05,
		rl.NewColor(30, 30, 30, 220))
	rl.DrawCubeWires(rl.NewVector3(0, y+screenH/2, z), screenW, screenH, 0.05, colBrass)
}

func drawBeamPath(sourceZ, barrierZ float32) {
	y := float32(0.5)
	segments := 20
	for i := 0; i < segments; i++ {
		if i%2 == 0 {
			t0 := float32(i) / float32(segments)
			t1 := float32(i+1) / float32(segments)
			z0 := sourceZ + t0*(barrierZ-sourceZ)
			z1 := sourceZ + t1*(barrierZ-sourceZ)
			rl.DrawLine3D(rl.NewVector3(0, y, z0), rl.NewVector3(0, y, z1), colOchre)
		}
	}
}

func drawHits(hits []ScreenHit, screenZ float32) {
	for _, h := range hits {
		x := h.NDUX
		y := float32(0.5) + 2.0 + h.NDUY // center of screen + offset
		rl.DrawSphere(rl.NewVector3(x, y, screenZ-0.03), 0.02, colGold)
	}
}

// ---------------------------------------------------------------------------
// 2D Overlay: Histogram + Stats + V&V
// ---------------------------------------------------------------------------

func drawHistogram(histogram [histBins]int, screenW, screenH int32) {
	panelX := screenW - 320
	panelY := screenH - 220
	panelW := int32(300)
	panelH := int32(200)

	// Background
	rl.DrawRectangle(panelX, panelY, panelW, panelH, rl.NewColor(20, 20, 20, 220))
	rl.DrawRectangleLines(panelX, panelY, panelW, panelH, colBrass)
	rl.DrawText("Hit Distribution", panelX+10, panelY+5, 14, colIvory)

	// Find max bin
	maxBin := 1
	for _, v := range histogram {
		if v > maxBin {
			maxBin = v
		}
	}

	// Draw bars
	barW := float32(panelW-20) / float32(histBins)
	baseY := float32(panelY + panelH - 10)
	maxH := float32(panelH - 35)

	for i, v := range histogram {
		if v == 0 {
			continue
		}
		h := float32(v) / float32(maxBin) * maxH
		x := float32(panelX+10) + float32(i)*barW
		rl.DrawRectangle(int32(x), int32(baseY-h), int32(barW+1), int32(h), colOchre)
	}
}

func drawStatsPanel(screenW int32, engine *PhysicsEngine, nHits int) {
	panelX := screenW - 320
	panelY := int32(20)

	rl.DrawRectangle(panelX, panelY, 300, 120, rl.NewColor(20, 20, 20, 220))
	rl.DrawRectangleLines(panelX, panelY, 300, 120, colBrass)

	rl.DrawText("Double-Slit V&V", panelX+10, panelY+8, 16, colIvory)
	rl.DrawLine(panelX+10, panelY+28, panelX+290, panelY+28, colSteel)

	spacing := engine.FringeSpacing()
	rl.DrawText(fmt.Sprintf("d = %.2f um", engine.SlitSep*1e6),
		panelX+10, panelY+35, 14, colAmber)
	rl.DrawText(fmt.Sprintf("Fringe spacing = %.1f um", spacing*1e6),
		panelX+10, panelY+55, 14, colBrass)
	rl.DrawText(fmt.Sprintf("N = %d", nHits),
		panelX+10, panelY+75, 14, colIvory)

	verdict := "COLLECTING..."
	verdictColor := colAmber
	if nHits >= 1000 {
		verdict = "PASS"
		verdictColor = colSage
	}
	rl.DrawText(fmt.Sprintf("Verdict: %s", verdict), panelX+10, panelY+95, 14, verdictColor)
}

func drawOracleOverlay(engine *PhysicsEngine, mapper *CoordMapper, camera rl.Camera3D, screenZ float32) {
	// Draw the expected intensity curve on the detector screen face
	steps := 200
	halfW := mapper.PhysHalfWidth
	for i := 0; i < steps-1; i++ {
		t0 := float64(i)/float64(steps)*2 - 1
		t1 := float64(i+1)/float64(steps)*2 - 1
		x0 := t0 * halfW
		x1 := t1 * halfW
		I0 := engine.Intensity(x0)
		I1 := engine.Intensity(x1)

		p0 := rl.GetWorldToScreen(rl.NewVector3(mapper.PhysToNDU(x0), 0.5+float32(I0)*3, screenZ-0.05), camera)
		p1 := rl.GetWorldToScreen(rl.NewVector3(mapper.PhysToNDU(x1), 0.5+float32(I1)*3, screenZ-0.05), camera)
		rl.DrawLineEx(p0, p1, 2, colAmber)
	}
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

const (
	screenWidth  = 1400
	screenHeight = 800
)

// ---------------------------------------------------------------------------
// Benchmark Mode
// ---------------------------------------------------------------------------

type benchCheckpoint struct {
	Particles  int
	FPS        float32
	FrameTimeMs float32
	RSSMb      float64
}

func getRSSMb() float64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return float64(m.Sys) / 1024 / 1024
}

var benchmarkMode = false
var benchCheckpoints = []int{100, 500, 1000, 5000, 10000, 25000}

func writeBenchCSV(filename string, results []benchCheckpoint, totalTime time.Duration) {
	f, err := os.Create(filename)
	if err != nil {
		fmt.Printf("Error creating benchmark file: %v\n", err)
		return
	}
	defer f.Close()

	w := csv.NewWriter(f)
	defer w.Flush()

	w.Write([]string{"engine", "particles", "fps", "frame_time_ms", "rss_mb"})
	for _, r := range results {
		w.Write([]string{
			"raylib",
			strconv.Itoa(r.Particles),
			fmt.Sprintf("%.1f", r.FPS),
			fmt.Sprintf("%.2f", r.FrameTimeMs),
			fmt.Sprintf("%.1f", r.RSSMb),
		})
	}

	fmt.Printf("\nRaylib benchmark complete in %v — %d checkpoints written to %s\n",
		totalTime.Round(time.Millisecond), len(results), filename)
}

func main() {
	// Check for --benchmark flag
	for _, arg := range os.Args[1:] {
		if arg == "--benchmark" {
			benchmarkMode = true
		}
	}

	rl.InitWindow(screenWidth, screenHeight, "QBP Double-Slit Bake-Off — Raylib")
	defer rl.CloseWindow()
	if benchmarkMode {
		rl.SetTargetFPS(0) // uncapped for benchmark
	} else {
		rl.SetTargetFPS(60)
	}
	rl.SetExitKey(0) // Don't close on ESC — we handle it ourselves
	rl.DisableCursor()

	engine := NewPhysicsEngine()
	mapper := NewCoordMapper(engine.FringeSpacing())
	particles := NewParticleSystem(engine, mapper)
	cam := NewLabCamera()

	if benchmarkMode {
		particles.emitRate = 10000 // max emit for benchmark
	}

	// Layout: beamline along Z axis
	sourceZ := float32(-10)
	barrierZ := float32(0)
	screenZ := float32(10)

	// Slit separation slider (log scale: 0.1 μm to 10 μm)
	slider := &Slider{
		Label: "Slit sep d",
		Rect:  rl.NewRectangle(20, 60, 250, 20),
		Value: 0.5, // middle of log range = 1 μm
		Min:   0.1e-6,
		Max:   10e-6,
	}

	showOverlay := false
	paused := false
	menuOpen := false
	prevD := engine.SlitSep

	// Benchmark state
	var benchResults []benchCheckpoint
	nextCheckpointIdx := 0
	benchStart := time.Now()
	var frameTimeAccum float32
	var frameCount int

	if benchmarkMode {
		fmt.Println("QBP Double-Slit Bake-Off — Raylib BENCHMARK MODE")
		fmt.Printf("Checkpoints: %v particles\n", benchCheckpoints)
	} else {
		fmt.Println("QBP Double-Slit Bake-Off — Raylib Prototype")
		fmt.Println("WASD: move | Mouse: look | Right-click: orbit | O: oracle overlay")
		fmt.Println("Space: pause | R: reset | ESC: menu")
	}

	running := true
	for running && !rl.WindowShouldClose() {
		dt := rl.GetFrameTime()

		// ESC toggles pause menu
		if rl.IsKeyPressed(rl.KeyEscape) {
			menuOpen = !menuOpen
			paused = menuOpen
			if menuOpen {
				rl.EnableCursor()
			} else {
				rl.DisableCursor()
			}
		}

		// --- Pause Menu Input ---
		if menuOpen {
			mouse := rl.GetMousePosition()

			// Button layout: centered on screen
			btnW := float32(200)
			btnH := float32(45)
			btnX := float32(screenWidth)/2 - btnW/2
			btnGap := float32(12)
			panelH := float32(220)
			panelY := float32(screenHeight)/2 - panelH/2
			btnStartY := panelY + 60

			resumeRect := rl.NewRectangle(btnX, btnStartY, btnW, btnH)
			resetRect := rl.NewRectangle(btnX, btnStartY+btnH+btnGap, btnW, btnH)
			exitRect := rl.NewRectangle(btnX, btnStartY+2*(btnH+btnGap), btnW, btnH)

			if rl.IsMouseButtonPressed(rl.MouseLeftButton) {
				if rl.CheckCollisionPointRec(mouse, resumeRect) {
					menuOpen = false
					paused = false
					rl.DisableCursor()
				} else if rl.CheckCollisionPointRec(mouse, resetRect) {
					particles.Reset()
					cam = NewLabCamera()
					menuOpen = false
					paused = false
					rl.DisableCursor()
				} else if rl.CheckCollisionPointRec(mouse, exitRect) {
					running = false
				}
			}
		}

		if !menuOpen {
			// Check if mouse is over UI
			mouse := rl.GetMousePosition()
			uiArea := rl.NewRectangle(0, 40, 300, 50)
			uiHover := rl.CheckCollisionPointRec(mouse, uiArea)

			// Update slider
			slider.Update()
			newD := slider.PhysValue()
			engine.SlitSep = newD

			// Reset particles if d changed significantly
			if math.Abs(newD-prevD)/prevD > 0.01 {
				particles.Reset()
				mapper.Update(engine.FringeSpacing())
				prevD = newD
			}

			// Keyboard
			if rl.IsKeyPressed(rl.KeyO) {
				showOverlay = !showOverlay
			}
			if rl.IsKeyPressed(rl.KeySpace) {
				paused = !paused
				if paused {
					rl.EnableCursor()
				} else {
					rl.DisableCursor()
				}
			}
			if rl.IsKeyPressed(rl.KeyR) {
				particles.Reset()
			}
			// Preset viewpoints
			if rl.IsKeyPressed(rl.KeyOne) {
				cam.Camera.Position = rl.NewVector3(8, 6, 18)
				cam.Yaw = -2.0
				cam.Pitch = -0.2
			}
			if rl.IsKeyPressed(rl.KeyTwo) {
				cam.Camera.Position = rl.NewVector3(0, 2, barrierZ+3)
				cam.Yaw = -math.Pi / 2
				cam.Pitch = -0.1
			}
			if rl.IsKeyPressed(rl.KeyThree) {
				cam.Camera.Position = rl.NewVector3(0, 2.5, screenZ+4)
				cam.Yaw = -math.Pi / 2
				cam.Pitch = -0.05
			}
			if rl.IsKeyPressed(rl.KeyFour) {
				cam.Camera.Position = rl.NewVector3(0, 20, 0)
				cam.Yaw = -math.Pi / 2
				cam.Pitch = -1.3
			}

			if !paused {
				cam.Update(dt, uiHover)
				particles.Update(dt)
			}
		}

		// Benchmark: track frame times and record checkpoints
		if benchmarkMode {
			frameTimeAccum += dt
			frameCount++

			nHits := len(particles.Hits)
			if nextCheckpointIdx < len(benchCheckpoints) && nHits >= benchCheckpoints[nextCheckpointIdx] {
				avgFrameTime := frameTimeAccum / float32(frameCount)
				avgFPS := float32(1.0) / avgFrameTime
				cp := benchCheckpoint{
					Particles:   nHits,
					FPS:         avgFPS,
					FrameTimeMs: avgFrameTime * 1000,
					RSSMb:       getRSSMb(),
				}
				benchResults = append(benchResults, cp)
				fmt.Printf("  [%d] particles=%d fps=%.1f frame=%.2fms rss=%.1fMB\n",
					nextCheckpointIdx, cp.Particles, cp.FPS, cp.FrameTimeMs, cp.RSSMb)
				nextCheckpointIdx++
				frameTimeAccum = 0
				frameCount = 0
			}

			// Exit after all checkpoints
			if nextCheckpointIdx >= len(benchCheckpoints) {
				writeBenchCSV("bench_raylib.csv", benchResults, time.Since(benchStart))
				running = false
			}
		}

		// Schematic slit separation in NDU (exaggerated for visibility)
		slitSepNDU := float32(1.0) // fixed visual width

		// Draw
		rl.BeginDrawing()
		rl.ClearBackground(colVerdantNight)

		rl.BeginMode3D(cam.Camera)
		drawLabBench()
		drawSource(sourceZ)
		drawBarrier(barrierZ, slitSepNDU)
		drawDetectorScreen(screenZ)
		drawBeamPath(sourceZ, barrierZ)
		drawHits(particles.Hits, screenZ)
		rl.EndMode3D()

		// Oracle overlay (2D, projected)
		if showOverlay {
			drawOracleOverlay(engine, mapper, cam.Camera, screenZ)
		}

		// 2D UI
		slider.Draw()
		drawStatsPanel(screenWidth, engine, len(particles.Hits))
		drawHistogram(particles.Histogram, screenWidth, screenHeight)

		// Mode indicator
		modeStr := "FPS"
		if cam.Mode == ModeOrbit {
			modeStr = "ORBIT"
		}
		rl.DrawText(fmt.Sprintf("Camera: %s", modeStr), 20, 20, 14, colSteel)

		if paused && !menuOpen {
			rl.DrawText("PAUSED", screenWidth/2-40, 20, 24, colAmber)
		}

		// --- Pause Menu Overlay ---
		if menuOpen {
			// Dim background
			rl.DrawRectangle(0, 0, screenWidth, screenHeight, rl.NewColor(0, 0, 0, 160))

			// Menu panel
			panelW := float32(280)
			panelH := float32(220)
			panelX := float32(screenWidth)/2 - panelW/2
			panelY := float32(screenHeight)/2 - panelH/2

			rl.DrawRectangleRounded(rl.NewRectangle(panelX, panelY, panelW, panelH), 0.08, 8,
				rl.NewColor(20, 30, 25, 240))
			rl.DrawRectangleRoundedLines(rl.NewRectangle(panelX, panelY, panelW, panelH), 0.08, 8, colBrass)

			// Title
			rl.DrawText("PAUSED", int32(panelX)+90, int32(panelY)+18, 24, colIvory)

			// Buttons
			btnW := float32(200)
			btnH := float32(45)
			btnX := float32(screenWidth)/2 - btnW/2
			btnGap := float32(12)
			btnStartY := panelY + 60

			mouse := rl.GetMousePosition()

			drawMenuButton := func(rect rl.Rectangle, label string, baseColor rl.Color) {
				hover := rl.CheckCollisionPointRec(mouse, rect)
				bgColor := baseColor
				if hover {
					bgColor = rl.NewColor(baseColor.R+30, baseColor.G+30, baseColor.B+30, baseColor.A)
				}
				rl.DrawRectangleRounded(rect, 0.2, 6, bgColor)
				rl.DrawRectangleRoundedLines(rect, 0.2, 6, colBrass)
				textW := rl.MeasureText(label, 20)
				rl.DrawText(label, int32(rect.X)+int32(rect.Width)/2-textW/2,
					int32(rect.Y)+int32(rect.Height)/2-10, 20, colIvory)
			}

			resumeRect := rl.NewRectangle(btnX, btnStartY, btnW, btnH)
			resetRect := rl.NewRectangle(btnX, btnStartY+btnH+btnGap, btnW, btnH)
			exitRect := rl.NewRectangle(btnX, btnStartY+2*(btnH+btnGap), btnW, btnH)

			drawMenuButton(resumeRect, "Resume", rl.NewColor(40, 80, 60, 255))
			drawMenuButton(resetRect, "Reset", rl.NewColor(60, 60, 40, 255))
			drawMenuButton(exitRect, "Exit", rl.NewColor(80, 40, 40, 255))
		}

		// Help hint
		rl.DrawText("WASD:move  Mouse:look  RightClick:orbit  O:overlay  1-4:presets  R:reset  Space:pause+interact  ESC:menu",
			20, screenHeight-25, 12, colSteel)

		rl.DrawFPS(screenWidth-90, 20)

		rl.EndDrawing()
	}
}
