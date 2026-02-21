//go:build !editor

// Double-Slit Bake-Off Prototype — Kaiju Engine
//
// Minimal double-slit simulation exercising: 3D scene on a lab bench,
// particle accumulation (Tonomura-style), 2D text overlay,
// FPS camera, and QBP design system colors.

package main

import (
	"encoding/csv"
	"fmt"
	"kaiju/bootstrap"
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
	"runtime"
	"syscall"
	"strconv"
	"time"
)

// ---------------------------------------------------------------------------
// Design System Colors (from docs/design-system.md)
// ---------------------------------------------------------------------------

func colMidnight() matrix.Color     { return matrix.NewColor(13.0/255, 27.0/255, 42.0/255, 1) }
func colBrass() matrix.Color        { return matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1) }
func colCopper() matrix.Color       { return matrix.NewColor(184.0/255, 115.0/255, 51.0/255, 1) }
func colBronze() matrix.Color       { return matrix.NewColor(205.0/255, 127.0/255, 50.0/255, 1) }
func colSteel() matrix.Color        { return matrix.NewColor(113.0/255, 121.0/255, 126.0/255, 1) }
func colGold() matrix.Color         { return matrix.NewColor(1, 215.0/255, 0, 1) }

// Suppress unused warnings
var _ = colGold

// ---------------------------------------------------------------------------
// Benchmark Mode
// ---------------------------------------------------------------------------

var dsBenchmarkMode = false
var dsBenchCheckpoints = []int{100, 500, 1000, 5000, 10000, 25000}

type dsBenchCheckpoint struct {
	Particles   int
	FPS         float32
	FrameTimeMs float32
	RSSMb       float64
}

func dsGetRSSMb() float64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return float64(m.Sys) / 1024 / 1024
}

func dsWriteBenchCSV(filename string, results []dsBenchCheckpoint, totalTime time.Duration) {
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
			"kaiju",
			strconv.Itoa(r.Particles),
			fmt.Sprintf("%.1f", r.FPS),
			fmt.Sprintf("%.2f", r.FrameTimeMs),
			fmt.Sprintf("%.1f", r.RSSMb),
		})
	}

	fmt.Printf("\nKaiju benchmark complete in %v — %d checkpoints written to %s\n",
		totalTime.Round(time.Millisecond), len(results), filename)
}

func init() {
	// Kaiju's bootstrap uses flag package, so we use an env var instead
	if os.Getenv("QBP_BENCHMARK") == "1" {
		dsBenchmarkMode = true
	}
}

// ---------------------------------------------------------------------------
// Physics Engine
// ---------------------------------------------------------------------------

const (
	dsDefaultSlitSep    = 1.0e-6
	dsDefaultWavelength = 5.0e-11
	dsDefaultScreenDist = 1.0
	dsDefaultSlitWidth  = 1.0e-7
	dsHistBins          = 100
)

type dsPhysicsEngine struct {
	SlitSep    float64
	Wavelength float64
	ScreenDist float64
	SlitWidth  float64
	rng        *rand.Rand
}

func newDSPhysicsEngine() *dsPhysicsEngine {
	return &dsPhysicsEngine{
		SlitSep:    dsDefaultSlitSep,
		Wavelength: dsDefaultWavelength,
		ScreenDist: dsDefaultScreenDist,
		SlitWidth:  dsDefaultSlitWidth,
		rng:        rand.New(rand.NewSource(42)),
	}
}

func (e *dsPhysicsEngine) FringeSpacing() float64 {
	return e.Wavelength * e.ScreenDist / e.SlitSep
}

func (e *dsPhysicsEngine) Intensity(x float64) float64 {
	argD := math.Pi * e.SlitSep * x / (e.Wavelength * e.ScreenDist)
	argA := math.Pi * e.SlitWidth * x / (e.Wavelength * e.ScreenDist)
	cos2 := math.Cos(argD) * math.Cos(argD)
	sinc2 := 1.0
	if math.Abs(argA) > 1e-12 {
		s := math.Sin(argA) / argA
		sinc2 = s * s
	}
	return cos2 * sinc2
}

func (e *dsPhysicsEngine) SampleHitPosition() float64 {
	halfWidth := 5.0 * e.FringeSpacing()
	for {
		x := (e.rng.Float64()*2 - 1) * halfWidth
		if e.rng.Float64() < e.Intensity(x) {
			return x
		}
	}
}

// ---------------------------------------------------------------------------
// Coordinate Mapper
// ---------------------------------------------------------------------------

type dsCoordMapper struct {
	PhysHalfWidth float64
	NDUHalfWidth  matrix.Float
}

func newDSCoordMapper(fringeSpacing float64) *dsCoordMapper {
	return &dsCoordMapper{PhysHalfWidth: 5.0 * fringeSpacing, NDUHalfWidth: 5.0}
}

func (cm *dsCoordMapper) PhysToNDU(x float64) matrix.Float {
	return matrix.Float(x/cm.PhysHalfWidth) * cm.NDUHalfWidth
}

func (cm *dsCoordMapper) Update(fringeSpacing float64) {
	cm.PhysHalfWidth = 5.0 * fringeSpacing
}

// ---------------------------------------------------------------------------
// Particle System
// ---------------------------------------------------------------------------

type dsScreenHit struct {
	NDUX matrix.Float
	NDUY matrix.Float
}

type dsParticleSystem struct {
	Hits      []dsScreenHit
	Histogram [dsHistBins]int
	engine    *dsPhysicsEngine
	mapper    *dsCoordMapper
	emitRate  float32
	emitTimer float32
	rng       *rand.Rand
}

func newDSParticleSystem(eng *dsPhysicsEngine, mapper *dsCoordMapper) *dsParticleSystem {
	return &dsParticleSystem{
		Hits:     make([]dsScreenHit, 0, 10000),
		engine:   eng,
		mapper:   mapper,
		emitRate: 50,
		rng:      rand.New(rand.NewSource(99)),
	}
}

func (ps *dsParticleSystem) Update(dt float32) {
	ps.emitTimer += dt
	interval := 1.0 / ps.emitRate
	for ps.emitTimer >= interval {
		ps.emitTimer -= interval
		x := ps.engine.SampleHitPosition()
		ndux := ps.mapper.PhysToNDU(x)
		nduy := matrix.Float(ps.rng.Float64()-0.5) * 0.3
		ps.Hits = append(ps.Hits, dsScreenHit{NDUX: ndux, NDUY: nduy})

		t := (x/ps.mapper.PhysHalfWidth + 1) / 2
		bin := int(t * dsHistBins)
		if bin < 0 {
			bin = 0
		}
		if bin >= dsHistBins {
			bin = dsHistBins - 1
		}
		ps.Histogram[bin]++
	}
}

func (ps *dsParticleSystem) Reset() {
	ps.Hits = ps.Hits[:0]
	ps.Histogram = [dsHistBins]int{}
}

// ---------------------------------------------------------------------------
// Game Implementation
// ---------------------------------------------------------------------------

type DoubleslitGame struct {
	host      *engine.Host
	physEng   *dsPhysicsEngine
	mapper    *dsCoordMapper
	particles *dsParticleSystem

	// Camera state
	yaw      matrix.Float
	pitch    matrix.Float
	speed    matrix.Float
	lastMX   float32
	lastMY   float32
	hasLastM bool

	// Slider
	sliderVal float32

	paused bool

	// Hit entities for rendering
	hitEntities []*engine.Entity

	// Benchmark state
	benchResults       []dsBenchCheckpoint
	nextCheckpointIdx  int
	benchStart         time.Time
	frameTimeAccum     float32
	frameCount         int
}

func (g *DoubleslitGame) PluginRegistry() []reflect.Type {
	return []reflect.Type{}
}

func (g *DoubleslitGame) ContentDatabase() (assets.Database, error) {
	return assets.NewFileDatabase("content")
}

func (g *DoubleslitGame) Launch(host *engine.Host) {
	g.host = host
	g.physEng = newDSPhysicsEngine()
	g.mapper = newDSCoordMapper(g.physEng.FringeSpacing())
	g.particles = newDSParticleSystem(g.physEng, g.mapper)
	g.yaw = -math.Pi / 2
	g.pitch = -0.15
	g.speed = 8.0
	g.sliderVal = 0.5

	// Set up camera
	cam := host.PrimaryCamera()
	cam.SetPosition(matrix.NewVec3(0, 3, 18))

	// Create 3D scene objects
	g.createLabBench(host)
	g.createApparatus(host)

	if dsBenchmarkMode {
		g.particles.emitRate = 10000
		g.benchStart = time.Now()
	}

	// Watchdog: SIGUSR1 force-kills if GPU hangs and Ctrl+Alt+Esc can't fire.
	// From another terminal: kill -USR1 $(pgrep doubleslit)
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGUSR1)
	go func() {
		<-sigCh
		fmt.Println("SIGUSR1 received — force quit (watchdog)")
		os.Exit(1)
	}()

	// Register update loop
	host.Updater.AddUpdate(func(deltaTime float64) {
		g.update(matrix.Float(deltaTime))
	})

	if dsBenchmarkMode {
		fmt.Println("QBP Double-Slit Bake-Off — Kaiju BENCHMARK MODE")
		fmt.Printf("Checkpoints: %v particles\n", dsBenchCheckpoints)
	} else {
		fmt.Println("QBP Double-Slit Bake-Off — Kaiju Engine Prototype")
		fmt.Println("WASD: move | Mouse: look | Space: pause | R: reset | ESC: quit")
	}
}

func (g *DoubleslitGame) createCube(host *engine.Host, pos, scale matrix.Vec3, color matrix.Color) {
	mesh := rendering.NewMeshCube(host.MeshCache())
	entity := engine.NewEntity(host.WorkGroup())
	entity.Transform.SetPosition(pos)
	entity.Transform.SetScale(scale)

	mat, err := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	if err != nil {
		fmt.Printf("Warning: could not load material: %v\n", err)
		return
	}

	drawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &entity.Transform,
		ViewCuller: &host.Cameras.Primary,
		ShaderData: &shader_data_registry.ShaderDataUnlit{
			ShaderDataBase: rendering.NewShaderDataBase(),
			Color:          color,
			UVs:            matrix.NewVec4(0, 0, 1, 1),
		},
	}
	host.Drawings.AddDrawing(drawing)
}

func (g *DoubleslitGame) createLabBench(host *engine.Host) {
	// Bench top
	g.createCube(host,
		matrix.NewVec3(0, 0, 0),
		matrix.NewVec3(3, 0.15, 22),
		colBronze())

	// Bench legs
	for _, z := range []matrix.Float{-9, -3, 3, 9} {
		for _, x := range []matrix.Float{-1.2, 1.2} {
			g.createCube(host,
				matrix.NewVec3(x, -1.0, z),
				matrix.NewVec3(0.15, 2.0, 0.15),
				colCopper())
		}
	}

	// Floor
	g.createCube(host,
		matrix.NewVec3(0, -2.01, 0),
		matrix.NewVec3(40, 0.02, 40),
		colMidnight())
}

func (g *DoubleslitGame) createApparatus(host *engine.Host) {
	// Source
	g.createCube(host,
		matrix.NewVec3(0, 0.5, -10),
		matrix.NewVec3(0.8, 0.8, 0.8),
		colBrass())

	// Barrier sections (schematic slit separation)
	var slitSepNDU matrix.Float = 1.0
	halfSep := slitSepNDU / 2
	var slitW matrix.Float = 0.05
	var barrierH matrix.Float = 3.0

	leftW := 2.5 - halfSep - slitW/2
	g.createCube(host,
		matrix.NewVec3(-(halfSep+slitW/2+leftW/2), 0.5+barrierH/2, 0),
		matrix.NewVec3(leftW, barrierH, 0.1),
		colSteel())

	centerW := slitSepNDU - slitW
	g.createCube(host,
		matrix.NewVec3(0, 0.5+barrierH/2, 0),
		matrix.NewVec3(centerW, barrierH, 0.1),
		colSteel())

	g.createCube(host,
		matrix.NewVec3(halfSep+slitW/2+leftW/2, 0.5+barrierH/2, 0),
		matrix.NewVec3(leftW, barrierH, 0.1),
		colSteel())

	// Detector screen
	g.createCube(host,
		matrix.NewVec3(0, 0.5+2, 10),
		matrix.NewVec3(10, 4, 0.05),
		matrix.NewColor(0.12, 0.12, 0.12, 0.86))
}

func (g *DoubleslitGame) update(dt matrix.Float) {
	kb := g.host.Window.Keyboard
	mouse := g.host.Window.Mouse

	// Force-quit: Ctrl+Alt+Esc
	if kb.KeyHeld(hid.KeyboardKeyLeftCtrl) && kb.KeyHeld(hid.KeyboardKeyLeftAlt) && kb.KeyDown(hid.KeyboardKeyEscape) {
		fmt.Println("Ctrl+Alt+Esc — force quit")
		os.Exit(0)
	}

	// Pause toggle
	if kb.KeyDown(hid.KeyboardKeySpace) {
		g.paused = !g.paused
	}

	// Reset
	if kb.KeyDown(hid.KeyboardKeyR) {
		g.particles.Reset()
		// Remove old hit entities
		for _, e := range g.hitEntities {
			e.SetActive(false)
		}
		g.hitEntities = g.hitEntities[:0]
	}

	// FPS Camera — compute delta from previous frame position
	mpos := mouse.ScreenPosition()
	if g.hasLastM {
		dx := mpos.X() - g.lastMX
		dy := mpos.Y() - g.lastMY
		g.yaw += matrix.Float(dx) * 0.003
		g.pitch += matrix.Float(dy) * 0.003
		if g.pitch > 1.4 {
			g.pitch = 1.4
		}
		if g.pitch < -1.4 {
			g.pitch = -1.4
		}
	}
	g.lastMX = mpos.X()
	g.lastMY = mpos.Y()
	g.hasLastM = true

	cam := g.host.PrimaryCamera()
	pos := cam.Position()

	fwd := matrix.NewVec3(
		matrix.Float(math.Cos(float64(g.yaw))),
		0,
		matrix.Float(math.Sin(float64(g.yaw))),
	)
	right := matrix.NewVec3(-fwd.Z(), 0, fwd.X())
	moveSpeed := g.speed * dt

	if kb.KeyHeld(hid.KeyboardKeyW) {
		pos = pos.Add(fwd.Scale(moveSpeed))
	}
	if kb.KeyHeld(hid.KeyboardKeyS) {
		pos = pos.Subtract(fwd.Scale(moveSpeed))
	}
	if kb.KeyHeld(hid.KeyboardKeyA) {
		pos = pos.Subtract(right.Scale(moveSpeed))
	}
	if kb.KeyHeld(hid.KeyboardKeyD) {
		pos = pos.Add(right.Scale(moveSpeed))
	}

	cam.SetPosition(pos)
	target := pos.Add(matrix.NewVec3(
		matrix.Float(math.Cos(float64(g.pitch))*math.Cos(float64(g.yaw))),
		matrix.Float(math.Sin(float64(g.pitch))),
		matrix.Float(math.Cos(float64(g.pitch))*math.Sin(float64(g.yaw))),
	))
	cam.SetLookAt(target)

	// Particle update
	if !g.paused || dsBenchmarkMode {
		prevCount := len(g.particles.Hits)
		g.particles.Update(float32(dt))

		// Spawn hit-dot entities for new particles
		for i := prevCount; i < len(g.particles.Hits); i++ {
			h := g.particles.Hits[i]
			g.spawnHitDot(h)
		}
	}

	// Benchmark: track frame times and record checkpoints
	if dsBenchmarkMode {
		g.frameTimeAccum += float32(dt)
		g.frameCount++

		nHits := len(g.particles.Hits)
		if g.nextCheckpointIdx < len(dsBenchCheckpoints) && nHits >= dsBenchCheckpoints[g.nextCheckpointIdx] {
			avgFrameTime := g.frameTimeAccum / float32(g.frameCount)
			avgFPS := float32(1.0) / avgFrameTime
			cp := dsBenchCheckpoint{
				Particles:   nHits,
				FPS:         avgFPS,
				FrameTimeMs: avgFrameTime * 1000,
				RSSMb:       dsGetRSSMb(),
			}
			g.benchResults = append(g.benchResults, cp)
			fmt.Printf("  [%d] particles=%d fps=%.1f frame=%.2fms rss=%.1fMB\n",
				g.nextCheckpointIdx, cp.Particles, cp.FPS, cp.FrameTimeMs, cp.RSSMb)
			g.nextCheckpointIdx++
			g.frameTimeAccum = 0
			g.frameCount = 0
		}

		// Exit after all checkpoints
		if g.nextCheckpointIdx >= len(dsBenchCheckpoints) {
			dsWriteBenchCSV("bench_kaiju.csv", g.benchResults, time.Since(g.benchStart))
			g.host.Close()
		}
	}
}

func (g *DoubleslitGame) spawnHitDot(h dsScreenHit) {
	mesh := rendering.NewMeshSphere(g.host.MeshCache(), 0.02, 4, 8)
	entity := engine.NewEntity(g.host.WorkGroup())
	entity.Transform.SetPosition(matrix.NewVec3(h.NDUX, 0.5+2.0+h.NDUY, 10-0.03))
	entity.Transform.SetScale(matrix.NewVec3(1, 1, 1))

	mat, err := g.host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	if err != nil {
		return
	}

	drawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &entity.Transform,
		ViewCuller: &g.host.Cameras.Primary,
		ShaderData: &shader_data_registry.ShaderDataUnlit{
			ShaderDataBase: rendering.NewShaderDataBase(),
			Color:          colGold(),
			UVs:            matrix.NewVec4(0, 0, 1, 1),
		},
	}
	g.host.Drawings.AddDrawing(drawing)
	g.hitEntities = append(g.hitEntities, entity)
}

func getGame() bootstrap.GameInterface {
	if labMode {
		return &LabGame{}
	}
	if uiSmokeTestMode {
		return &UISmokeTestGame{}
	}
	return &DoubleslitGame{}
}
