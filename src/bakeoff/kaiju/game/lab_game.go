//go:build !editor

// QBP Phase 4e — Double-Slit Lab
//
// Interactive 3D lab room for Experiment 03 verification & validation.
// Run with: QBP_LAB=1 ./doubleslit
// (Default still runs the bake-off prototype.)

package main

import (
	"fmt"
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/matrix"
	"kaiju/platform/hid"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
	"math"
	"math/rand"
	"os"
	"os/signal"
	"reflect"
	"syscall"
	"time"
)

var labMode = os.Getenv("QBP_LAB") == "1"

// ---------------------------------------------------------------------------
// Design System Colors (from docs/design-system.md)
// ---------------------------------------------------------------------------

func labColVerdantNight() matrix.Color { return matrix.NewColor(13.0/255, 40.0/255, 32.0/255, 1) }
func labColMidnight() matrix.Color     { return matrix.NewColor(13.0/255, 27.0/255, 42.0/255, 1) }
func labColBrass() matrix.Color        { return matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1) }
func labColCopper() matrix.Color       { return matrix.NewColor(184.0/255, 115.0/255, 51.0/255, 1) }
func labColBronze() matrix.Color       { return matrix.NewColor(205.0/255, 127.0/255, 50.0/255, 1) }
func labColSteel() matrix.Color        { return matrix.NewColor(113.0/255, 121.0/255, 126.0/255, 1) }
func labColOchre() matrix.Color        { return matrix.NewColor(212.0/255, 170.0/255, 90.0/255, 1) }
func labColAmber() matrix.Color        { return matrix.NewColor(244.0/255, 162.0/255, 97.0/255, 1) }
func labColGold() matrix.Color         { return matrix.NewColor(1, 215.0/255, 0, 1) }
func labColIvory() matrix.Color        { return matrix.NewColor(1, 254.0/255, 240.0/255, 1) }
func labColFloor() matrix.Color        { return matrix.NewColor(10.0/255, 20.0/255, 30.0/255, 1) }

// Suppress unused
var _ = labColAmber
var _ = labColGold
var _ = labColIvory

// ---------------------------------------------------------------------------
// Room Dimensions (1 NDU = 1 meter)
// ---------------------------------------------------------------------------

const (
	// Room envelope
	roomWidth  = 12.0 // X: -6 to +6
	roomDepth  = 16.0 // Z: -8 to +8
	roomHeight = 4.5  // Y: 0 to 4.5

	// Optical bench (experiment) — runs in X, parallel to desk
	benchLen   = 6.0  // Total length (X: -3 to +3)
	benchDepth = 0.8  // Z extent (narrow table)
	benchY     = 0.9  // Surface height
	benchThick = 0.08 // Top thickness
	benchZ     = 1.0  // Center Z of bench (in front of platform)

	// Raised platform (back of room, overlooking bench)
	platZ0    = -7.5  // Back wall side (more room behind desk)
	platZ1    = -3.5  // Edge facing bench
	platWidth = 8.0   // X: -4 to +4
	platY     = 0.6   // Platform height (3 steps × 0.2m)
	stepDepth = 0.5   // Each step 0.5m deep
	stepH     = 0.2   // Each step 0.2m rise

	// Desk on platform
	deskZ     = -5.5  // Center of desk
	deskWidth = 4.0   // X extent
	deskDepth = 1.0   // Z extent
	deskH     = 0.75  // Height above platform
	deskY     = platY + deskH

	// Chair (behind desk, facing +Z toward bench)
	chairZ     = -6.5  // Behind desk, scientist looks +Z over desk toward bench
	chairSeatH = 0.45  // Seat height above platform
	chairBackH = 0.8   // Back height above seat

	// Camera (seated in chair, looking toward bench)
	camStartX = 0.0
	camStartY = platY + chairSeatH + 1.2 // platform + seat + seated eye
	camStartZ = chairZ                     // At the chair
)

// ---------------------------------------------------------------------------
// Lab Game
// ---------------------------------------------------------------------------

type LabGame struct {
	host *engine.Host
	rng  *rand.Rand

	// Camera
	yaw      matrix.Float
	pitch    matrix.Float
	mouseSen matrix.Float
	lastMPos matrix.Vec2
	hasLastM bool
	seated   bool

	heartbeat      chan struct{}
	frameCount     int
	frameTimeAccum float64
	fpsLog         *os.File

	// Active experiment room
	room ExperimentRoom
}

func (g *LabGame) PluginRegistry() []reflect.Type {
	return []reflect.Type{}
}

func (g *LabGame) ContentDatabase() (assets.Database, error) {
	return assets.NewFileDatabase("content")
}

func (g *LabGame) Launch(host *engine.Host) {
	g.host = host
	g.rng = rand.New(rand.NewSource(42))
	g.yaw = -math.Pi / 2 // Face down +Z (toward the bench)
	g.pitch = -0.15       // Slight downward tilt
	g.mouseSen = 0.002

	// Camera
	cam := host.PrimaryCamera()
	cam.SetPosition(matrix.NewVec3(camStartX, camStartY, camStartZ))

	// Build room
	g.buildFloor(host)
	g.buildWalls(host)
	g.buildPlatform(host)
	g.buildBench(host)
	g.buildApparatus(host)

	// Watchdog: SIGUSR1 force-kills if GPU hangs and ESC can't fire.
	// From another terminal: kill -USR1 $(pgrep kaiju-ds)
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGUSR1)
	go func() {
		<-sigCh
		fmt.Println("SIGUSR1 received — force quit (watchdog)")
		os.Exit(1)
	}()

	// Heartbeat watchdog: if the update loop stops ticking for 5 seconds
	// (GPU hang), force-kill the process.
	g.heartbeat = make(chan struct{}, 1)
	go func() {
		for {
			select {
			case <-g.heartbeat:
			case <-time.After(5 * time.Second):
				fmt.Println("WATCHDOG: update loop stalled for 5s — force quit")
				os.Exit(1)
			}
		}
	}()

	// FPS log file
	g.fpsLog, _ = os.Create("fps_log.txt")
	if g.fpsLog != nil {
		g.fpsLog.WriteString("timestamp,fps,frame_ms,particles\n")
	}

	// Hide cursor for FPS look (no LockCursor — it floods X11 with warp events)
	host.Window.HideCursor()

	// Update loop
	host.Updater.AddUpdate(func(dt float64) {
		select {
		case g.heartbeat <- struct{}{}:
		default:
		}
		g.update(dt)
	})

	// Initialize experiment room
	g.room = NewDSRoom()
	g.room.Setup(host)

	fmt.Println("╔══════════════════════════════════════════════════════════╗")
	fmt.Println("║  QBP Experiment 03: Double-Slit Lab                      ║")
	fmt.Println("║  WASD: move  |  Mouse: look  |  Shift: sprint            ║")
	fmt.Println("║  Q: sit/stand  |  1-4: views                             ║")
	fmt.Println("║  5:Bach  6:Zeilinger  7:Tonomura  (standard QM)          ║")
	fmt.Println("║  8:QBP-weak  9:QBP-strong  (quaternionic coupling)       ║")
	fmt.Println("║  Enter: emitter  Space: freeze  +/-: rate  O: oracle     ║")
	fmt.Println("║  R: reset  |  ESC: quit                                  ║")
	fmt.Println("╚══════════════════════════════════════════════════════════╝")
}

// ---------------------------------------------------------------------------
// Geometry helpers
// ---------------------------------------------------------------------------

func (g *LabGame) cube(host *engine.Host, pos, scale matrix.Vec3, color matrix.Color) {
	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(pos)
	entity.Transform.SetScale(scale)

	mat, err := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	if err != nil {
		fmt.Printf("Warning: material error: %v\n", err)
		return
	}

	drawing := rendering.Drawing{
		Material:  mat,
		Mesh:      mesh,
		Transform: &entity.Transform,
		ShaderData: &shader_data_registry.ShaderDataUnlit{
			ShaderDataBase: rendering.NewShaderDataBase(),
			Color:          color,
			UVs:            matrix.NewVec4(0, 0, 1, 1),
		},
		ViewCuller: &host.Cameras.Primary,
	}
	host.Drawings.AddDrawing(drawing)
}

// ---------------------------------------------------------------------------
// Room Construction
// ---------------------------------------------------------------------------

func (g *LabGame) buildFloor(host *engine.Host) {
	// Main floor
	g.cube(host,
		matrix.NewVec3(0, -0.05, 0),
		matrix.NewVec3(roomWidth, 0.1, roomDepth),
		labColFloor())

	// Grid lines on floor (Steel color, thin strips along Z)
	for x := matrix.Float(-roomWidth / 2); x <= roomWidth/2; x += 2 {
		g.cube(host,
			matrix.NewVec3(x, 0.001, 0),
			matrix.NewVec3(0.02, 0.002, roomDepth),
			labColSteel())
	}
	// Grid lines along X
	for z := matrix.Float(-roomDepth / 2); z <= roomDepth/2; z += 2 {
		g.cube(host,
			matrix.NewVec3(0, 0.001, z),
			matrix.NewVec3(roomWidth, 0.002, 0.02),
			labColSteel())
	}
}

func (g *LabGame) buildWalls(host *engine.Host) {
	wallThick := matrix.Float(0.15)

	// Back wall (behind platform)
	g.cube(host,
		matrix.NewVec3(0, roomHeight/2, -roomDepth/2),
		matrix.NewVec3(roomWidth, roomHeight, wallThick),
		labColVerdantNight())

	// Front wall (behind detector)
	g.cube(host,
		matrix.NewVec3(0, roomHeight/2, roomDepth/2),
		matrix.NewVec3(roomWidth, roomHeight, wallThick),
		labColVerdantNight())

	// Left wall
	g.cube(host,
		matrix.NewVec3(-roomWidth/2, roomHeight/2, 0),
		matrix.NewVec3(wallThick, roomHeight, roomDepth),
		labColVerdantNight())

	// Right wall
	g.cube(host,
		matrix.NewVec3(roomWidth/2, roomHeight/2, 0),
		matrix.NewVec3(wallThick, roomHeight, roomDepth),
		labColVerdantNight())

	// Ceiling
	g.cube(host,
		matrix.NewVec3(0, roomHeight, 0),
		matrix.NewVec3(roomWidth, wallThick, roomDepth),
		labColMidnight())
}

func (g *LabGame) buildPlatform(host *engine.Host) {
	// 3 steps leading UP to the platform (lowest step furthest from platform)
	for i := 0; i < 3; i++ {
		stepNum := 3 - i // 3=tallest (at platform), 1=shortest (away from platform)
		stepY := stepH * matrix.Float(stepNum)
		stepZ := platZ1 + matrix.Float(i)*stepDepth
		g.cube(host,
			matrix.NewVec3(0, stepY/2, stepZ+stepDepth/2),
			matrix.NewVec3(platWidth, stepY, stepDepth),
			labColSteel())
	}

	// Platform top
	platDepth := matrix.Float(platZ1 - platZ0)
	g.cube(host,
		matrix.NewVec3(0, platY/2, (platZ0+platZ1)/2),
		matrix.NewVec3(platWidth, platY, platDepth),
		labColSteel())

	// Desk — Bronze colored slab on the platform
	g.cube(host,
		matrix.NewVec3(0, platY+deskH/2, deskZ),
		matrix.NewVec3(deskWidth, deskH, deskDepth),
		labColBronze())

	// Desk edge trim (Brass strip along front edge)
	g.cube(host,
		matrix.NewVec3(0, platY+deskH, deskZ+deskDepth/2),
		matrix.NewVec3(deskWidth+0.1, 0.03, 0.05),
		labColBrass())

	// Chair — between desk and platform edge
	seatY := matrix.Float(platY + chairSeatH)
	chairWidth := matrix.Float(0.5)
	chairDepth := matrix.Float(0.5)

	// Seat cushion
	g.cube(host,
		matrix.NewVec3(0, seatY, chairZ),
		matrix.NewVec3(chairWidth, 0.08, chairDepth),
		labColCopper())

	legH := matrix.Float(chairSeatH - 0.04)

	// Chair back (on -Z side, behind the scientist who faces +Z)
	g.cube(host,
		matrix.NewVec3(0, seatY+chairBackH/2, chairZ-chairDepth/2+0.03),
		matrix.NewVec3(chairWidth, chairBackH, 0.05),
		labColCopper())

	// Chair base/pedestal (single center column)
	g.cube(host,
		matrix.NewVec3(0, platY+legH/2, chairZ),
		matrix.NewVec3(0.08, legH, 0.08),
		labColSteel())
	// Chair base star (5-point, simplified as cross)
	g.cube(host,
		matrix.NewVec3(0, platY+0.04, chairZ),
		matrix.NewVec3(0.5, 0.03, 0.08),
		labColSteel())
	g.cube(host,
		matrix.NewVec3(0, platY+0.04, chairZ),
		matrix.NewVec3(0.08, 0.03, 0.5),
		labColSteel())

	// Chair armrests
	armY := seatY + 0.25
	for _, x := range []matrix.Float{-chairWidth/2 + 0.02, chairWidth/2 - 0.02} {
		g.cube(host,
			matrix.NewVec3(x, armY, chairZ),
			matrix.NewVec3(0.04, 0.04, chairDepth-0.1),
			labColBrass())
	}

	// Flat monitor layout — 2×2 screens (double-stacked), facing -Z toward scientist
	//
	// Scientist eyes: (0, 2.25, -6.5), looking +Z
	// All screens face -Z — simple flat panels, no L-shape.
	// Wider screens (0.50 each) for readable text.

	screenH := matrix.Float(0.35)
	screenW := matrix.Float(0.50)  // Wider flat screens
	gap := matrix.Float(0.03)      // Gap between stacked screens

	bottomEdgeY := matrix.Float(camStartY - 0.05 - screenH - screenH/2)
	botCenterY := bottomEdgeY + screenH/2
	topCenterY := bottomEdgeY + screenH + gap + screenH/2

	// Z position: on the desk, slightly forward
	monitorZ := matrix.Float(deskZ + 0.4)

	// Left and right centers (with gap between wings)
	lCenterX := matrix.Float(-0.65) // Left wing center
	rCenterX := matrix.Float(0.65)  // Right wing center

	// === Left wing — 2 flat screens stacked ===
	for _, cy := range []matrix.Float{botCenterY, topCenterY} {
		// Screen face (faces -Z)
		g.cube(host,
			matrix.NewVec3(lCenterX, cy, monitorZ),
			matrix.NewVec3(screenW, screenH, 0.025),
			labColMidnight())
		// Bezel
		g.cube(host,
			matrix.NewVec3(lCenterX, cy, monitorZ+0.015),
			matrix.NewVec3(screenW+0.03, screenH+0.03, 0.005),
			labColBrass())
	}

	// Left monitor arm (steel post, desk to bottom screen)
	armBaseY := matrix.Float(deskY + 0.01)
	armTopY := bottomEdgeY
	armH := armTopY - armBaseY
	g.cube(host,
		matrix.NewVec3(lCenterX, armBaseY+armH/2, monitorZ),
		matrix.NewVec3(0.04, armH, 0.04),
		labColSteel())

	// === Right wing — 2 flat screens stacked ===
	for _, cy := range []matrix.Float{botCenterY, topCenterY} {
		// Screen face (faces -Z)
		g.cube(host,
			matrix.NewVec3(rCenterX, cy, monitorZ),
			matrix.NewVec3(screenW, screenH, 0.025),
			labColMidnight())
		// Bezel
		g.cube(host,
			matrix.NewVec3(rCenterX, cy, monitorZ+0.015),
			matrix.NewVec3(screenW+0.03, screenH+0.03, 0.005),
			labColBrass())
	}

	// Right monitor arm
	g.cube(host,
		matrix.NewVec3(rCenterX, armBaseY+armH/2, monitorZ),
		matrix.NewVec3(0.04, armH, 0.04),
		labColSteel())

	// === Center — clear view to bench ===
	g.cube(host,
		matrix.NewVec3(0, deskY+0.015, deskZ+0.3),
		matrix.NewVec3(0.40, 0.015, 0.13),
		labColMidnight())
	g.cube(host,
		matrix.NewVec3(0.35, deskY+0.01, deskZ+0.3),
		matrix.NewVec3(0.12, 0.01, 0.15),
		labColSteel())
}

func (g *LabGame) buildBench(host *engine.Host) {
	// Bench top (optical table surface) — runs in X, parallel to desk
	g.cube(host,
		matrix.NewVec3(0, benchY, benchZ),
		matrix.NewVec3(benchLen, benchThick, benchDepth),
		labColBronze())

	// Bench legs (4 corners)
	legH := matrix.Float(benchY - benchThick/2)
	legW := matrix.Float(0.08)
	halfLen := matrix.Float(benchLen/2 - 0.15)
	halfDep := matrix.Float(benchDepth/2 - 0.1)
	for _, x := range []matrix.Float{-halfLen, halfLen} {
		for _, z := range []matrix.Float{benchZ - halfDep, benchZ + halfDep} {
			g.cube(host,
				matrix.NewVec3(x, legH/2, z),
				matrix.NewVec3(legW, legH, legW),
				labColSteel())
		}
	}

	// Bench edge trim (Brass strip around perimeter)
	trimH := matrix.Float(0.02)
	trimY := matrix.Float(benchY + benchThick/2)
	// Long edges (along X)
	g.cube(host,
		matrix.NewVec3(0, trimY, benchZ-benchDepth/2),
		matrix.NewVec3(benchLen, trimH, 0.02),
		labColBrass())
	g.cube(host,
		matrix.NewVec3(0, trimY, benchZ+benchDepth/2),
		matrix.NewVec3(benchLen, trimH, 0.02),
		labColBrass())
	// Short edges (along Z)
	g.cube(host,
		matrix.NewVec3(-benchLen/2, trimY, benchZ),
		matrix.NewVec3(0.02, trimH, benchDepth),
		labColBrass())
	g.cube(host,
		matrix.NewVec3(benchLen/2, trimY, benchZ),
		matrix.NewVec3(0.02, trimH, benchDepth),
		labColBrass())
}

func (g *LabGame) buildApparatus(host *engine.Host) {
	appY := matrix.Float(benchY + benchThick/2) // Top of bench surface

	// Apparatus runs along X axis (left-to-right on bench)
	// Source at -X, barrier at center, detector at +X
	srcX := matrix.Float(-benchLen/2 + 0.5)
	barrierX := matrix.Float(0)
	screenX := matrix.Float(benchLen/2 - 0.5)

	// Source — small emitter box
	g.cube(host,
		matrix.NewVec3(srcX, appY+0.15, benchZ),
		matrix.NewVec3(0.3, 0.3, 0.3),
		labColCopper())
	// Emitter aperture (dark hole on face toward detector)
	g.cube(host,
		matrix.NewVec3(srcX+0.16, appY+0.15, benchZ),
		matrix.NewVec3(0.02, 0.06, 0.06),
		labColMidnight())

	// Barrier — vertical plate with two slit gaps (now in YZ plane)
	barrierH := matrix.Float(0.5)
	barrierW := matrix.Float(0.8)  // Z extent (height of barrier plate in Z)
	slitGap := matrix.Float(0.15)  // Separation between slits (in Z)
	slitW := matrix.Float(0.03)    // Each slit width (in Z)

	// Bottom solid section
	botW := (barrierW - slitGap) / 2 - slitW/2
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH/2, benchZ-(slitGap/2+slitW/2+botW/2)),
		matrix.NewVec3(0.03, barrierH, botW),
		labColBrass())

	// Center solid section (between slits)
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH/2, benchZ),
		matrix.NewVec3(0.03, barrierH, slitGap-slitW),
		labColBrass())

	// Top solid section
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH/2, benchZ+(slitGap/2+slitW/2+botW/2)),
		matrix.NewVec3(0.03, barrierH, botW),
		labColBrass())

	// Barrier frame (Copper surround)
	frameW := matrix.Float(0.04)
	// Top bar
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH+frameW/2, benchZ),
		matrix.NewVec3(0.05, frameW, barrierW+frameW*2),
		labColCopper())
	// Bottom bar
	g.cube(host,
		matrix.NewVec3(barrierX, appY-frameW/2, benchZ),
		matrix.NewVec3(0.05, frameW, barrierW+frameW*2),
		labColCopper())
	// Near bar (toward camera)
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH/2, benchZ-(barrierW/2+frameW/2)),
		matrix.NewVec3(0.05, barrierH+frameW*2, frameW),
		labColCopper())
	// Far bar
	g.cube(host,
		matrix.NewVec3(barrierX, appY+barrierH/2, benchZ+(barrierW/2+frameW/2)),
		matrix.NewVec3(0.05, barrierH+frameW*2, frameW),
		labColCopper())

	// Detector screen — tall flat panel (in YZ plane)
	screenH := matrix.Float(0.6)
	screenD := matrix.Float(1.0) // Z extent
	// Screen surface (where hits land)
	g.cube(host,
		matrix.NewVec3(screenX, appY+screenH/2, benchZ),
		matrix.NewVec3(0.02, screenH, screenD),
		labColIvory())
	// Screen frame
	g.cube(host,
		matrix.NewVec3(screenX+0.02, appY+screenH/2, benchZ),
		matrix.NewVec3(0.02, screenH+0.06, screenD+0.06),
		labColCopper())

	// Beam path indicator — faint dashed line along bench (X axis)
	dashLen := matrix.Float(0.2)
	dashGap := matrix.Float(0.2)
	for x := srcX + 0.4; x < screenX-0.3; x += dashLen + dashGap {
		g.cube(host,
			matrix.NewVec3(x+dashLen/2, appY+0.005, benchZ),
			matrix.NewVec3(dashLen, 0.005, 0.01),
			labColSteel())
	}
}

// ---------------------------------------------------------------------------
// Update Loop — FPS Camera
// ---------------------------------------------------------------------------

func (g *LabGame) update(dt float64) {
	kb := g.host.Window.Keyboard
	mouse := &g.host.Window.Mouse

	// FPS + particle count logging (to file and stderr)
	g.frameCount++
	g.frameTimeAccum += dt
	if g.frameTimeAccum >= 1.0 {
		fps := float64(g.frameCount) / g.frameTimeAccum
		frameMs := (g.frameTimeAccum / float64(g.frameCount)) * 1000
		particles := 0
		if dsRoom, ok := g.room.(*DSRoom); ok {
			particles = dsRoom.detector.TotalHits
		}
		if g.fpsLog != nil {
			fmt.Fprintf(g.fpsLog, "%.0f,%.1f,%.2f,%d\n", float64(time.Now().UnixMilli()), fps, frameMs, particles)
			g.fpsLog.Sync()
		}
		fmt.Fprintf(os.Stderr, "FPS: %.1f  (frame: %.2fms)  particles: %d\n", fps, frameMs, particles)
		g.frameCount = 0
		g.frameTimeAccum = 0
	}

	// Quit: ESC or Ctrl+Alt+Esc
	if kb.KeyDown(hid.KeyboardKeyEscape) {
		fmt.Println("ESC — quit")
		os.Exit(0)
	}

	// Mouse look — raw delta between frames, no LockCursor.
	// Warp to center only when cursor nears the window edge.
	mp := mouse.Position()
	if g.hasLastM {
		dx := matrix.Float(mp.X()-g.lastMPos.X()) * g.mouseSen
		dy := matrix.Float(mp.Y()-g.lastMPos.Y()) * g.mouseSen
		g.yaw += dx
		g.pitch += dy
		if g.pitch > math.Pi/2-0.1 {
			g.pitch = math.Pi/2 - 0.1
		}
		if g.pitch < -math.Pi/2+0.1 {
			g.pitch = -math.Pi/2 + 0.1
		}
	}
	g.lastMPos = mp
	g.hasLastM = true

	// Warp cursor to center if it drifts near the window edge
	w, h := g.host.Window.Width(), g.host.Window.Height()
	margin := 50
	sx, sy := int(mouse.SX), int(mouse.SY)
	if sx < margin || sx > w-margin || sy < margin || sy > h-margin {
		g.host.Window.SetCursorPosition(w/2, h/2)
		g.hasLastM = false // skip next delta to avoid jump from warp
	}

	// Movement (disabled when seated)
	cam := g.host.PrimaryCamera()
	pos := cam.Position()

	if !g.seated {
		speed := matrix.Float(8.0 * dt)
		if kb.KeyHeld(hid.KeyboardKeyLeftShift) {
			speed *= 2.5
		}

		forward := matrix.NewVec3(
			matrix.Float(math.Cos(float64(g.yaw))),
			0,
			matrix.Float(math.Sin(float64(g.yaw))))
		right := matrix.NewVec3(
			matrix.Float(-math.Sin(float64(g.yaw))),
			0,
			matrix.Float(math.Cos(float64(g.yaw))))

		if kb.KeyHeld(hid.KeyboardKeyW) {
			pos = pos.Add(forward.Scale(speed))
		}
		if kb.KeyHeld(hid.KeyboardKeyS) {
			pos = pos.Subtract(forward.Scale(speed))
		}
		if kb.KeyHeld(hid.KeyboardKeyA) {
			pos = pos.Subtract(right.Scale(speed))
		}
		if kb.KeyHeld(hid.KeyboardKeyD) {
			pos = pos.Add(right.Scale(speed))
		}
	}

	// Preset views (KeyDown = first frame only)
	if kb.KeyDown(hid.KeyboardKey1) {
		// Overview — behind desk, looking toward bench
		pos = matrix.NewVec3(0, camStartY, camStartZ)
		g.yaw = math.Pi / 2
		g.pitch = -0.15
		g.hasLastM = false
	}
	if kb.KeyDown(hid.KeyboardKey2) {
		// Slit close-up — in front of barrier, facing it
		pos = matrix.NewVec3(-0.8, benchY+0.4, benchZ-1.0)
		g.yaw = math.Pi / 2
		g.pitch = -0.1
		g.hasLastM = false
	}
	if kb.KeyDown(hid.KeyboardKey3) {
		// Detector screen — looking at it from the source side
		pos = matrix.NewVec3(benchLen/2+0.3, benchY+0.4, benchZ-0.8)
		g.yaw = math.Pi
		g.pitch = -0.05
		g.hasLastM = false
	}
	if kb.KeyDown(hid.KeyboardKey4) {
		// Top-down — bird's eye
		pos = matrix.NewVec3(0, 4.0, benchZ)
		g.yaw = math.Pi / 2
		g.pitch = -math.Pi/2 + 0.1
		g.hasLastM = false
	}

	// Sit/Stand toggle (Q key) — must be within 1m of chair
	if kb.KeyDown(hid.KeyboardKeyQ) {
		chairPos := matrix.NewVec3(0, 0, chairZ)
		playerXZ := matrix.NewVec3(pos.X(), 0, pos.Z())
		dist := chairPos.Subtract(playerXZ).Length()
		if !g.seated && dist < 1.0 {
			// Sit down — snap to chair, face desk/bench
			// Pitch = -0.25 for "dashboard view": both desk controls AND monitors visible
			g.seated = true
			pos = matrix.NewVec3(0, camStartY, chairZ)
			g.yaw = math.Pi / 2  // Face +Z toward bench
			g.pitch = -0.25
			g.hasLastM = false
		} else if g.seated {
			// Stand up — rise to standing height, step back from chair
			g.seated = false
			standY := matrix.Float(platY + 1.7) // Standing eye height on platform
			pos = matrix.NewVec3(0, standY, chairZ-0.5)
			g.hasLastM = false
		}
	}

	// When seated: disable WASD movement, allow mouse look only
	if g.seated {
		pos = matrix.NewVec3(0, camStartY, chairZ)
	}

	// Wall collision — clamp position inside room bounds
	wallMargin := matrix.Float(0.3)
	minX := matrix.Float(-roomWidth/2) + wallMargin
	maxX := matrix.Float(roomWidth/2) - wallMargin
	minZ := matrix.Float(-roomDepth/2) + wallMargin
	maxZ := matrix.Float(roomDepth/2) - wallMargin
	minY := matrix.Float(0.5) // Don't go below eye height
	maxY := matrix.Float(roomHeight) - wallMargin

	px, py, pz := pos.X(), pos.Y(), pos.Z()
	if px < minX { px = minX }
	if px > maxX { px = maxX }
	if py < minY { py = minY }
	if py > maxY { py = maxY }
	if pz < minZ { pz = minZ }
	if pz > maxZ { pz = maxZ }
	pos = matrix.NewVec3(px, py, pz)

	cam.SetPosition(pos)
	target := pos.Add(matrix.NewVec3(
		matrix.Float(math.Cos(float64(g.pitch))*math.Cos(float64(g.yaw))),
		matrix.Float(math.Sin(float64(g.pitch))),
		matrix.Float(math.Cos(float64(g.pitch))*math.Sin(float64(g.yaw)))))
	cam.SetLookAt(target)

	// Update experiment room
	if g.room != nil {
		if dsRoom, ok := g.room.(*DSRoom); ok {
			dsRoom.HandleInput(g.host)
		}
		g.room.Update(dt)
	}
}
