//go:build !editor

// monitor_text.go — CPU-rasterized text on 3D monitor surfaces.
//
// Each of the 4 desk monitors displays text content by rasterizing it
// into an RGBA image buffer, uploading as a GPU texture, and mapping
// onto a flat quad mesh positioned at the monitor surface.
// Dirty-flag updates: text only re-rasterizes when content changes.

package main

import (
	"image"
	"image/color"
	"image/draw"
	"math"
	"strings"

	"golang.org/x/image/font"
	"golang.org/x/image/font/basicfont"
	"golang.org/x/image/math/fixed"

	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/matrix"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
)

const (
	monTexW = 512
	monTexH = 256
)

// ---------------------------------------------------------------------------
// MonitorTextBlock — one monitor's text-on-texture display
// ---------------------------------------------------------------------------

// MonitorTextBlock manages a textured quad on a monitor surface.
// Text is CPU-rasterized into an RGBA buffer and uploaded to the GPU.
type MonitorTextBlock struct {
	host     *engine.Host
	entity   *engine.Entity
	texture  *rendering.Texture
	lastText string
	dirty    bool
	position matrix.Vec3
	quadW    float32    // World-space width of the text quad
	quadH    float32    // World-space height
	fgColor  color.RGBA // Text color for rasterization
}

func newMonitorTextBlock(host *engine.Host, pos matrix.Vec3,
	quadW, quadH float32, fg color.RGBA) *MonitorTextBlock {

	mt := &MonitorTextBlock{
		host:     host,
		position: pos,
		quadW:    quadW,
		quadH:    quadH,
		fgColor:  fg,
	}
	mt.initQuad()
	return mt
}

func (mt *MonitorTextBlock) initQuad() {
	host := mt.host

	// Rasterize blank initial texture (dark monitor "off" state)
	blankImg := rasterizeMonitorText("", monTexW, monTexH, mt.fgColor)

	// Create GPU texture from pixel data
	var err error
	mt.texture, err = rendering.NewTextureFromMemory(
		rendering.GenerateUniqueTextureKey,
		blankImg.Pix,
		monTexW, monTexH,
		rendering.TextureFilterLinear,
	)
	if err != nil {
		return
	}
	mt.texture.DelayedCreate(host.Window.Renderer)

	// Create quad mesh positioned at monitor surface
	mesh := rendering.NewMeshQuad(host.MeshCache())
	mt.entity = engine.NewEntity(host.WorkGroup())
	mt.entity.Transform.SetPosition(mt.position)
	mt.entity.Transform.SetScale(matrix.NewVec3(
		matrix.Float(mt.quadW), matrix.Float(mt.quadH), 1))
	// Rotate 180° around Y so quad faces -Z (toward scientist)
	mt.entity.Transform.SetRotation(matrix.NewVec3(
		0, matrix.Float(math.Pi), 0))

	// Create textured material instance
	baseMat, _ := host.MaterialCache().Material(assets.MaterialDefinitionUnlit)
	mat := baseMat.CreateInstance([]*rendering.Texture{mt.texture})

	sd := &shader_data_registry.ShaderDataUnlit{
		ShaderDataBase: rendering.NewShaderDataBase(),
		Color:          matrix.NewColor(1, 1, 1, 1), // No tint — texture colors only
		UVs:            matrix.NewVec4(0, 0, 1, 1),
	}

	drawing := rendering.Drawing{
		Material:   mat,
		Mesh:       mesh,
		Transform:  &mt.entity.Transform,
		ShaderData: sd,
		ViewCuller: &host.Cameras.Primary,
	}
	host.Drawings.AddDrawing(drawing)
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

// Flush re-rasterizes and uploads the texture if the text has changed.
func (mt *MonitorTextBlock) Flush() {
	if !mt.dirty || mt.texture == nil {
		return
	}
	mt.dirty = false

	img := rasterizeMonitorText(mt.lastText, monTexW, monTexH, mt.fgColor)

	// Mirror horizontally to compensate for the pi Y-rotation
	mirrorImageH(img)

	mt.texture.WritePixels(mt.host.Window.Renderer, []rendering.GPUImageWriteRequest{
		{
			Region: matrix.Vec4i{0, 0, monTexW, monTexH},
			Pixels: img.Pix,
		},
	})
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

// NewMonitorTextSystem creates the four textured quads positioned at
// the monitor surfaces defined in buildPlatform (lab_game.go).
func NewMonitorTextSystem(host *engine.Host) *MonitorTextSystem {
	// Match flat monitor geometry from buildPlatform (lab_game.go).
	// Flat screens at monitorZ = deskZ + 0.4, facing -Z.
	monitorZ := float32(deskZ + 0.4)
	textZ := monitorZ - 0.015 // Slightly in front of screen surface

	screenH := float32(0.35)
	screenW := float32(0.50)
	gap := float32(0.03)

	bottomEdgeY := float32(camStartY - 0.05 - screenH - screenH/2)
	botCenterY := bottomEdgeY + screenH/2
	topCenterY := bottomEdgeY + screenH + gap + screenH/2

	lCenterX := float32(-0.65)
	rCenterX := float32(0.65)

	// Quad slightly smaller than screen for bezel margin
	quadW := screenW * 0.92
	quadH := screenH * 0.92

	ivory := color.RGBA{255, 250, 240, 255}
	amber := color.RGBA{244, 162, 97, 255}

	mts := &MonitorTextSystem{host: host}

	mts.leftTop = newMonitorTextBlock(host,
		matrix.NewVec3(matrix.Float(lCenterX), matrix.Float(topCenterY), matrix.Float(textZ)),
		quadW, quadH, ivory)

	mts.leftBottom = newMonitorTextBlock(host,
		matrix.NewVec3(matrix.Float(lCenterX), matrix.Float(botCenterY), matrix.Float(textZ)),
		quadW, quadH, amber)

	mts.rightTop = newMonitorTextBlock(host,
		matrix.NewVec3(matrix.Float(rCenterX), matrix.Float(topCenterY), matrix.Float(textZ)),
		quadW, quadH, ivory)

	mts.rightBottom = newMonitorTextBlock(host,
		matrix.NewVec3(matrix.Float(rCenterX), matrix.Float(botCenterY), matrix.Float(textZ)),
		quadW, quadH, ivory)

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
// the last Flush will re-rasterize and upload their textures.
func (mts *MonitorTextSystem) Flush() {
	mts.leftTop.Flush()
	mts.leftBottom.Flush()
	mts.rightTop.Flush()
	mts.rightBottom.Flush()
}

// ---------------------------------------------------------------------------
// Text rasterization helpers
// ---------------------------------------------------------------------------

// rasterizeMonitorText renders multi-line text onto a dark RGBA buffer
// using the built-in basicfont (7x13 monospace — terminal aesthetic).
func rasterizeMonitorText(text string, width, height int, fg color.RGBA) *image.RGBA {
	img := image.NewRGBA(image.Rect(0, 0, width, height))

	// Dark monitor background (near-black with slight blue tint)
	bg := color.RGBA{10, 16, 26, 255}
	draw.Draw(img, img.Bounds(), image.NewUniform(bg), image.Point{}, draw.Src)

	if text == "" {
		return img
	}

	face := basicfont.Face7x13

	d := &font.Drawer{
		Dst:  img,
		Src:  image.NewUniform(fg),
		Face: face,
	}

	marginX := 16
	marginY := 22 // First baseline Y position
	lineH := 22   // Pixels between baselines

	lines := strings.Split(text, "\n")
	for i, line := range lines {
		y := marginY + i*lineH
		if y > height-8 {
			break // Don't draw past bottom
		}
		d.Dot = fixed.Point26_6{
			X: fixed.Int26_6(marginX * 64),
			Y: fixed.Int26_6(y * 64),
		}
		d.DrawString(line)
	}

	return img
}

// mirrorImageH flips an RGBA image horizontally in-place.
// Needed because the quad is rotated pi around Y, which mirrors the texture.
func mirrorImageH(img *image.RGBA) {
	w := img.Bounds().Dx()
	h := img.Bounds().Dy()
	stride := img.Stride
	for y := 0; y < h; y++ {
		row := img.Pix[y*stride : y*stride+w*4]
		for x := 0; x < w/2; x++ {
			l := x * 4
			r := (w - 1 - x) * 4
			row[l], row[r] = row[r], row[l]
			row[l+1], row[r+1] = row[r+1], row[l+1]
			row[l+2], row[r+2] = row[r+2], row[l+2]
			row[l+3], row[r+3] = row[r+3], row[l+3]
		}
	}
}
