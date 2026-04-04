//go:build !editor

// Kaiju UI Smoke Test — verifies slider, label, panel, and histogram rendering.
//
// Run with: QBP_UI_TEST=1 ./doubleslit
// (Without QBP_UI_TEST=1, the normal double-slit game runs instead.)

package main

import (
	"fmt"
	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/ui"
	"kaiju/matrix"
	"kaiju/rendering"
	"math"
	"math/rand"
	"os"
	"reflect"
)

var uiSmokeTestMode = os.Getenv("QBP_UI_TEST") == "1"

// ---------------------------------------------------------------------------
// UI Smoke Test Game
// ---------------------------------------------------------------------------

type UISmokeTestGame struct {
	host      *engine.Host
	uiManager ui.Manager

	// Widgets under test
	slider     *ui.Slider
	valueLabel *ui.Label
	statsLabel *ui.Label
	histBars   []*ui.Panel

	// Simulated data
	slitSepUm float64 // slit separation in micrometers
	histogram [50]int
	totalHits int
	rng       *rand.Rand
}

func (g *UISmokeTestGame) PluginRegistry() []reflect.Type {
	return []reflect.Type{}
}

func (g *UISmokeTestGame) ContentDatabase() (assets.Database, error) {
	return assets.NewFileDatabase("content")
}

func (g *UISmokeTestGame) Launch(host *engine.Host) {
	g.host = host
	g.rng = rand.New(rand.NewSource(42))
	g.slitSepUm = 1.0 // 1 um default

	// Initialize UI manager
	g.uiManager.Init(host)

	// Get the square texture for panel backgrounds
	tex, err := host.TextureCache().Texture(
		assets.TextureSquare, rendering.TextureFilterLinear)
	if err != nil {
		fmt.Printf("Warning: could not load square texture: %v\n", err)
	}

	// ── Title Panel ─────────────────────────────────────────────
	titlePanel := g.uiManager.Add().ToPanel()
	titlePanel.Init(tex, ui.ElementTypePanel)
	titlePanel.DontFitContent()
	titlePanel.SetColor(matrix.NewColor(13.0/255, 27.0/255, 42.0/255, 0.95))
	titlePanel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	titlePanel.Base().Layout().Scale(400, 40)
	titlePanel.Base().Layout().SetOffset(20, 10)
	titlePanel.Base().Layout().SetPadding(10, 8, 10, 8)

	titleLabel := g.uiManager.Add().ToLabel()
	titleLabel.Init("Kaiju UI Smoke Test")
	titleLabel.SetColor(matrix.NewColor(1, 215.0/255, 0, 1)) // Gold
	titleLabel.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	titleLabel.SetFontSize(24)
	titlePanel.AddChild(titleLabel.Base())

	// ── BIG slider — root level, no parent panel ──────────────
	g.slider = g.uiManager.Add().ToSlider()
	g.slider.Init()
	g.slider.Base().ToPanel().DontFitContent() // Prevent shrink-wrapping to bg/fg panels
	g.slider.SetBGColor(matrix.NewColor(0.4, 0.4, 0.4, 1))
	g.slider.SetFGColor(matrix.NewColor(1.0, 0.2, 0.2, 1)) // Bright red handle
	g.slider.Base().Layout().Scale(600, 50)
	g.slider.SetValueWithoutEvent(0.5)

	// Value readout — must be inside a panel (labels need a parent panel)
	valueLabelPanel := g.uiManager.Add().ToPanel()
	valueLabelPanel.Init(tex, ui.ElementTypePanel)
	valueLabelPanel.DontFitContent()
	valueLabelPanel.AllowClickThrough()
	valueLabelPanel.SetColor(matrix.NewColor(0, 0, 0, 0)) // Transparent
	valueLabelPanel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	valueLabelPanel.Base().Layout().Scale(650, 40)
	valueLabelPanel.Base().Layout().SetOffset(20, 120)

	g.valueLabel = g.uiManager.Add().ToLabel()
	g.valueLabel.Init("d = 1.00 um  --  CLICK AND DRAG THE RED BAR ABOVE")
	g.valueLabel.SetColor(matrix.NewColor(1, 1, 0, 1)) // Bright yellow
	g.valueLabel.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	g.valueLabel.SetFontSize(22)
	valueLabelPanel.AddChild(g.valueLabel.Base())

	// Wire up slider change event
	g.slider.Base().AddEvent(ui.EventTypeChange, func() {
		val := g.slider.Value()
		fmt.Printf("[SLIDER] value=%.3f\n", val)
		// Log scale: 0.1 to 10 um
		logMin := math.Log10(0.1)
		logMax := math.Log10(10.0)
		g.slitSepUm = math.Pow(10, logMin+float64(val)*(logMax-logMin))
		g.valueLabel.SetText(fmt.Sprintf("d = %.2f um", g.slitSepUm))
		// Reset histogram on change
		g.histogram = [50]int{}
		g.totalHits = 0
	})

	// Debug: log click events on the slider
	g.slider.Base().AddEvent(ui.EventTypeDown, func() {
		fmt.Println("[SLIDER] DOWN event received")
	})
	g.slider.Base().AddEvent(ui.EventTypeUp, func() {
		fmt.Println("[SLIDER] UP event received")
	})

	// ── Stats Panel ─────────────────────────────────────────────
	statsPanel := g.uiManager.Add().ToPanel()
	statsPanel.Init(tex, ui.ElementTypePanel)
	statsPanel.DontFitContent()
	statsPanel.SetColor(matrix.NewColor(0.1, 0.12, 0.1, 0.9))
	statsPanel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	statsPanel.Base().Layout().Scale(400, 60)
	statsPanel.Base().Layout().SetOffset(20, 190)
	statsPanel.Base().Layout().SetPadding(15, 10, 15, 10)

	g.statsLabel = g.uiManager.Add().ToLabel()
	g.statsLabel.Init("N = 0 | Fringe: 50.0 um | COLLECTING...")
	g.statsLabel.SetColor(matrix.NewColor(244.0/255, 162.0/255, 97.0/255, 1)) // Amber
	g.statsLabel.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	g.statsLabel.SetFontSize(18)
	statsPanel.AddChild(g.statsLabel.Base())

	// ── Histogram Panel ─────────────────────────────────────────
	histPanel := g.uiManager.Add().ToPanel()
	histPanel.Init(tex, ui.ElementTypePanel)
	histPanel.DontFitContent()
	histPanel.SetColor(matrix.NewColor(0.08, 0.08, 0.08, 0.9))
	histPanel.Base().Layout().SetPositioning(ui.PositioningAbsolute)
	histPanel.Base().Layout().Scale(400, 220)
	histPanel.Base().Layout().SetOffset(20, 260)
	histPanel.Base().Layout().SetPadding(10, 25, 10, 10)

	histTitle := g.uiManager.Add().ToLabel()
	histTitle.Init("Hit Distribution")
	histTitle.SetColor(matrix.NewColor(1, 1, 0.94, 1)) // Ivory
	histTitle.SetBGColor(matrix.NewColor(0, 0, 0, 0))
	histTitle.SetFontSize(14)
	histPanel.AddChild(histTitle.Base())

	// Create histogram bars (50 bars)
	g.histBars = make([]*ui.Panel, 50)
	for i := 0; i < 50; i++ {
		bar := g.uiManager.Add().ToPanel()
		bar.Init(tex, ui.ElementTypePanel)
		bar.DontFitContent()
		bar.SetColor(matrix.NewColor(212.0/255, 170.0/255, 90.0/255, 1)) // Ochre
		bar.Base().Layout().SetPositioning(ui.PositioningAbsolute)
		bar.Base().Layout().Scale(5, 1) // 5px wide, 1px tall initially
		bar.Base().Layout().SetOffset(float32(i)*6.4+10, 165)
		histPanel.AddChild(bar.Base())
		g.histBars[i] = bar
	}

	// ── Border demo on the stats panel ──────────────────────────
	statsPanel.SetBorderSize(1, 1, 1, 1)
	statsPanel.SetBorderColor(
		matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1),
		matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1),
		matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1),
		matrix.NewColor(212.0/255, 165.0/255, 116.0/255, 1),
	)

	// Ensure cursor is visible and not locked
	host.Window.ShowCursor()
	host.Window.UnlockCursor()

	// ── Update Loop ─────────────────────────────────────────────
	host.Updater.AddUpdate(func(deltaTime float64) {
		g.update(deltaTime)
	})

	fmt.Println("╔═══════════════════════════════════════════════╗")
	fmt.Println("║  Kaiju UI Smoke Test                         ║")
	fmt.Println("║  Drag slider to change slit separation       ║")
	fmt.Println("║  Histogram updates in real-time              ║")
	fmt.Println("║  ESC to quit                                 ║")
	fmt.Println("╚═══════════════════════════════════════════════╝")
}

func (g *UISmokeTestGame) update(dt float64) {
	// Emit ~100 particles per second
	emitCount := int(100.0 * dt)
	if emitCount < 1 {
		emitCount = 1
	}

	d := g.slitSepUm * 1e-6 // convert to meters
	wavelength := 5.0e-11
	screenDist := 1.0
	slitWidth := 1.0e-7
	fringeSpacing := wavelength * screenDist / d
	halfWidth := 5.0 * fringeSpacing

	for i := 0; i < emitCount; i++ {
		// Rejection sampling from Fraunhofer pattern
		for {
			x := (g.rng.Float64()*2 - 1) * halfWidth
			argD := math.Pi * d * x / (wavelength * screenDist)
			argA := math.Pi * slitWidth * x / (wavelength * screenDist)
			cos2 := math.Cos(argD) * math.Cos(argD)
			sinc2 := 1.0
			if math.Abs(argA) > 1e-12 {
				s := math.Sin(argA) / argA
				sinc2 = s * s
			}
			if g.rng.Float64() < cos2*sinc2 {
				// Bin it
				t := (x/halfWidth + 1) / 2
				bin := int(t * 50)
				if bin < 0 {
					bin = 0
				}
				if bin >= 50 {
					bin = 49
				}
				g.histogram[bin]++
				g.totalHits++
				break
			}
		}
	}

	// Update histogram bars
	maxBin := 1
	for _, v := range g.histogram {
		if v > maxBin {
			maxBin = v
		}
	}
	for i, bar := range g.histBars {
		h := float32(g.histogram[i]) / float32(maxBin) * 150
		if h < 1 {
			h = 1
		}
		bar.Base().Layout().Scale(5, h)
		bar.Base().Layout().SetOffsetY(165 - h)
	}

	// Update stats
	verdict := "COLLECTING..."
	if g.totalHits >= 1000 {
		verdict = "PASS"
	}
	g.statsLabel.SetText(fmt.Sprintf("N = %d | Fringe: %.1f um | %s",
		g.totalHits, fringeSpacing*1e6, verdict))
}
