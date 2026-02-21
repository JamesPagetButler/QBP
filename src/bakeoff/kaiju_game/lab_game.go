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
	roomWidth  = 16.0 // X: -8 to +8
	roomDepth  = 30.0 // Z: -16 to +14
	roomHeight = 4.5  // Y: 0 to 4.5

	// Optical bench (experiment)
	benchZ0    = -10.0 // Source end
	benchZ1    = 10.0  // Detector end
	benchWidth = 1.2   // X extent
	benchY     = 0.9   // Surface height
	benchThick = 0.08  // Top thickness

	// Raised platform (behind bench, overlooking it)
	platZ0    = -15.5 // Back wall side
	platZ1    = -11.0 // Edge facing bench
	platWidth = 10.0  // X: -5 to +5
	platY     = 0.6   // Platform height (3 steps × 0.2m)
	stepDepth = 0.5   // Each step 0.5m deep
	stepH     = 0.2   // Each step 0.2m rise

	// Desk on platform
	deskZ     = -13.0 // Center of desk
	deskWidth = 4.0   // X extent
	deskDepth = 1.0   // Z extent
	deskH     = 0.75  // Height above platform
	deskY     = platY + deskH

	// Camera (seated at desk)
	camStartX = 0.0
	camStartY = platY + 0.45 + 1.2 // platform + chair + seated eye = 2.25
	camStartZ = deskZ + 1.5         // Behind the desk, looking forward
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
	hasLastM bool
	lastMX   matrix.Float
	lastMY   matrix.Float
	mouseSen matrix.Float
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

	// Watchdog: SIGUSR1 force-kills if GPU hangs and Ctrl+Alt+Esc can't fire.
	// From another terminal: kill -USR1 $(pgrep doubleslit)
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGUSR1)
	go func() {
		<-sigCh
		fmt.Println("SIGUSR1 received — force quit (watchdog)")
		os.Exit(1)
	}()

	// Cursor free for FPS look
	w, h := host.Window.Width(), host.Window.Height()
	host.Window.LockCursor(w/2, h/2)
	host.Window.HideCursor()

	// Update loop
	host.Updater.AddUpdate(func(dt float64) {
		g.update(dt)
	})

	fmt.Println("╔═══════════════════════════════════════════════════╗")
	fmt.Println("║  QBP Experiment 03: Double-Slit Lab               ║")
	fmt.Println("║  WASD: move  |  Mouse: look  |  ESC: quit        ║")
	fmt.Println("║  1-4: preset views  |  Space: pause + free cursor ║")
	fmt.Println("╚═══════════════════════════════════════════════════╝")
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
	for x := matrix.Float(-8); x <= 8; x += 2 {
		g.cube(host,
			matrix.NewVec3(x, 0.001, 0),
			matrix.NewVec3(0.02, 0.002, roomDepth),
			labColSteel())
	}
	// Grid lines along X
	for z := matrix.Float(-14); z <= 12; z += 2 {
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
	// 3 steps leading up to the platform
	for i := 0; i < 3; i++ {
		stepY := stepH * matrix.Float(i+1)
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

	// Screen mounts on desk (3 angled screen frames — geometry placeholder)
	// Main screen (center, wider)
	screenBaseY := matrix.Float(deskY + 0.02)
	screenH := matrix.Float(0.5)
	screenTilt := matrix.Float(0.05) // Slight lean back

	// Center screen frame
	g.cube(host,
		matrix.NewVec3(0, screenBaseY+screenH/2, deskZ-0.1-screenTilt),
		matrix.NewVec3(2.0, screenH, 0.04),
		labColMidnight())
	// Center screen bezel
	g.cube(host,
		matrix.NewVec3(0, screenBaseY+screenH/2, deskZ-0.1-screenTilt-0.01),
		matrix.NewVec3(2.1, screenH+0.06, 0.02),
		labColBrass())

	// Left screen
	g.cube(host,
		matrix.NewVec3(-1.8, screenBaseY+screenH/2, deskZ-0.05-screenTilt),
		matrix.NewVec3(1.2, screenH, 0.04),
		labColMidnight())
	g.cube(host,
		matrix.NewVec3(-1.8, screenBaseY+screenH/2, deskZ-0.05-screenTilt-0.01),
		matrix.NewVec3(1.3, screenH+0.06, 0.02),
		labColBrass())

	// Right screen
	g.cube(host,
		matrix.NewVec3(1.8, screenBaseY+screenH/2, deskZ-0.05-screenTilt),
		matrix.NewVec3(1.2, screenH, 0.04),
		labColMidnight())
	g.cube(host,
		matrix.NewVec3(1.8, screenBaseY+screenH/2, deskZ-0.05-screenTilt-0.01),
		matrix.NewVec3(1.3, screenH+0.06, 0.02),
		labColBrass())
}

func (g *LabGame) buildBench(host *engine.Host) {
	benchLen := matrix.Float(benchZ1 - benchZ0)
	centerZ := matrix.Float((benchZ0 + benchZ1) / 2)

	// Bench top (optical table surface)
	g.cube(host,
		matrix.NewVec3(0, benchY, centerZ),
		matrix.NewVec3(benchWidth, benchThick, benchLen),
		labColBronze())

	// Bench legs (4 pairs)
	legH := matrix.Float(benchY - benchThick/2)
	legW := matrix.Float(0.08)
	for _, z := range []matrix.Float{benchZ0 + 1, benchZ0 + 7, benchZ1 - 7, benchZ1 - 1} {
		for _, x := range []matrix.Float{-benchWidth/2 + 0.1, benchWidth/2 - 0.1} {
			g.cube(host,
				matrix.NewVec3(x, legH/2, z),
				matrix.NewVec3(legW, legH, legW),
				labColSteel())
		}
	}

	// Bench edge trim (Brass strip around perimeter)
	trimH := matrix.Float(0.02)
	trimY := matrix.Float(benchY + benchThick/2)
	// Long edges
	g.cube(host,
		matrix.NewVec3(-benchWidth/2, trimY, centerZ),
		matrix.NewVec3(0.02, trimH, benchLen),
		labColBrass())
	g.cube(host,
		matrix.NewVec3(benchWidth/2, trimY, centerZ),
		matrix.NewVec3(0.02, trimH, benchLen),
		labColBrass())
	// Short edges
	g.cube(host,
		matrix.NewVec3(0, trimY, benchZ0),
		matrix.NewVec3(benchWidth, trimH, 0.02),
		labColBrass())
	g.cube(host,
		matrix.NewVec3(0, trimY, benchZ1),
		matrix.NewVec3(benchWidth, trimH, 0.02),
		labColBrass())
}

func (g *LabGame) buildApparatus(host *engine.Host) {
	appY := matrix.Float(benchY + benchThick/2) // Top of bench surface

	// Source — small emitter box
	srcZ := matrix.Float(benchZ0 + 1)
	g.cube(host,
		matrix.NewVec3(0, appY+0.15, srcZ),
		matrix.NewVec3(0.3, 0.3, 0.3),
		labColCopper())
	// Emitter aperture (dark hole on front face)
	g.cube(host,
		matrix.NewVec3(0, appY+0.15, srcZ+0.16),
		matrix.NewVec3(0.06, 0.06, 0.02),
		labColMidnight())

	// Barrier — vertical plate with two slit gaps
	barrierZ := matrix.Float(0)
	barrierH := matrix.Float(0.5)
	barrierW := matrix.Float(0.8)
	slitGap := matrix.Float(0.15) // Schematic exaggeration of slit separation
	slitW := matrix.Float(0.03)   // Each slit width

	// Left solid section
	leftW := (barrierW - slitGap) / 2 - slitW/2
	g.cube(host,
		matrix.NewVec3(-(slitGap/2+slitW/2+leftW/2), appY+barrierH/2, barrierZ),
		matrix.NewVec3(leftW, barrierH, 0.03),
		labColBrass())

	// Center solid section (between slits)
	g.cube(host,
		matrix.NewVec3(0, appY+barrierH/2, barrierZ),
		matrix.NewVec3(slitGap-slitW, barrierH, 0.03),
		labColBrass())

	// Right solid section
	g.cube(host,
		matrix.NewVec3(slitGap/2+slitW/2+leftW/2, appY+barrierH/2, barrierZ),
		matrix.NewVec3(leftW, barrierH, 0.03),
		labColBrass())

	// Barrier frame (Copper surround)
	frameW := matrix.Float(0.04)
	// Top bar
	g.cube(host,
		matrix.NewVec3(0, appY+barrierH+frameW/2, barrierZ),
		matrix.NewVec3(barrierW+frameW*2, frameW, 0.05),
		labColCopper())
	// Bottom bar
	g.cube(host,
		matrix.NewVec3(0, appY-frameW/2, barrierZ),
		matrix.NewVec3(barrierW+frameW*2, frameW, 0.05),
		labColCopper())
	// Left bar
	g.cube(host,
		matrix.NewVec3(-(barrierW/2+frameW/2), appY+barrierH/2, barrierZ),
		matrix.NewVec3(frameW, barrierH+frameW*2, 0.05),
		labColCopper())
	// Right bar
	g.cube(host,
		matrix.NewVec3(barrierW/2+frameW/2, appY+barrierH/2, barrierZ),
		matrix.NewVec3(frameW, barrierH+frameW*2, 0.05),
		labColCopper())

	// Detector screen — tall flat panel
	screenZ := matrix.Float(benchZ1 - 1)
	screenH := matrix.Float(0.6)
	screenW := matrix.Float(1.0)
	// Screen surface (where hits land — white/ivory)
	g.cube(host,
		matrix.NewVec3(0, appY+screenH/2, screenZ),
		matrix.NewVec3(screenW, screenH, 0.02),
		labColIvory())
	// Screen frame
	g.cube(host,
		matrix.NewVec3(0, appY+screenH/2, screenZ-0.02),
		matrix.NewVec3(screenW+0.06, screenH+0.06, 0.02),
		labColCopper())

	// Beam path indicator — faint dashed line along bench
	dashLen := matrix.Float(0.3)
	dashGap := matrix.Float(0.3)
	for z := srcZ + 0.5; z < screenZ-0.5; z += dashLen + dashGap {
		g.cube(host,
			matrix.NewVec3(0, appY+0.005, z+dashLen/2),
			matrix.NewVec3(0.01, 0.005, dashLen),
			labColSteel())
	}
}

// ---------------------------------------------------------------------------
// Update Loop — FPS Camera
// ---------------------------------------------------------------------------

func (g *LabGame) update(dt float64) {
	kb := g.host.Window.Keyboard
	mouse := &g.host.Window.Mouse

	// Force-quit: Ctrl+Alt+Esc
	if kb.KeyHeld(hid.KeyboardKeyLeftCtrl) && kb.KeyHeld(hid.KeyboardKeyLeftAlt) && kb.KeyDown(hid.KeyboardKeyEscape) {
		fmt.Println("Ctrl+Alt+Esc — force quit")
		os.Exit(0)
	}

	// Mouse look
	mpos := mouse.ScreenPosition()
	if g.hasLastM {
		dx := (mpos.X() - g.lastMX) * g.mouseSen
		dy := (mpos.Y() - g.lastMY) * g.mouseSen
		g.yaw += dx
		g.pitch -= dy
		// Clamp pitch
		if g.pitch > math.Pi/2-0.1 {
			g.pitch = math.Pi/2 - 0.1
		}
		if g.pitch < -math.Pi/2+0.1 {
			g.pitch = -math.Pi/2 + 0.1
		}
	}
	g.lastMX = mpos.X()
	g.lastMY = mpos.Y()
	g.hasLastM = true

	// Movement
	speed := matrix.Float(4.0 * dt) // 4 m/s walk speed
	if kb.KeyHeld(hid.KeyboardKeyLeftShift) {
		speed *= 2.5 // Sprint
	}

	forward := matrix.NewVec3(
		matrix.Float(math.Cos(float64(g.yaw))),
		0,
		matrix.Float(math.Sin(float64(g.yaw))))
	right := matrix.NewVec3(
		matrix.Float(-math.Sin(float64(g.yaw))),
		0,
		matrix.Float(math.Cos(float64(g.yaw))))

	cam := g.host.PrimaryCamera()
	pos := cam.Position()

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

	// Preset views (KeyDown = first frame only)
	if kb.KeyDown(hid.KeyboardKey1) {
		// Overview — behind desk, looking down the bench
		pos = matrix.NewVec3(0, camStartY, camStartZ)
		g.yaw = math.Pi / 2
		g.pitch = -0.15
	}
	if kb.KeyDown(hid.KeyboardKey2) {
		// Slit close-up — beside barrier, facing it
		pos = matrix.NewVec3(1.5, benchY+0.5, -0.5)
		g.yaw = -math.Pi
		g.pitch = -0.1
	}
	if kb.KeyDown(hid.KeyboardKey3) {
		// Detector screen — face on
		pos = matrix.NewVec3(0, benchY+0.4, benchZ1+0.5)
		g.yaw = -math.Pi / 2
		g.pitch = -0.05
	}
	if kb.KeyDown(hid.KeyboardKey4) {
		// Top-down — bird's eye
		pos = matrix.NewVec3(0, 4.0, 0)
		g.yaw = math.Pi / 2
		g.pitch = -math.Pi/2 + 0.1
	}

	cam.SetPosition(pos)
	target := pos.Add(matrix.NewVec3(
		matrix.Float(math.Cos(float64(g.pitch))*math.Cos(float64(g.yaw))),
		matrix.Float(math.Sin(float64(g.pitch))),
		matrix.Float(math.Cos(float64(g.pitch))*math.Sin(float64(g.yaw)))))
	cam.SetLookAt(target)
}
