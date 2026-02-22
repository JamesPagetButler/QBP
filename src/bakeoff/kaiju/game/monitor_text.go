//go:build !editor

// monitor_text.go — CPU-rasterized text on 3D monitor surfaces.
//
// Each of the 4 desk monitors displays text content by rasterizing it
// into an RGBA image buffer, uploading as a GPU texture, and mapping
// onto a flat quad mesh positioned at the monitor surface.
// Dirty-flag updates: text only re-rasterizes when content changes.
//
// KEY INSIGHT: The standard Kaiju quad faces +Z with CCW winding.
// Our camera sits at Z=-6.5 looking +Z — it sees the BACK of a +Z quad.
// With CullMode="Back" in the basic shader pipeline, that back face is culled.
// Rotating Pi around Y to face -Z reverses the winding order, so it's STILL
// culled. Fix: create a custom quad with reversed index winding that faces -Z
// with correct CCW winding from the camera's viewpoint.

package main

import (
	"image"
	"image/color"
	"image/draw"
	"strings"

	"golang.org/x/image/font"
	"golang.org/x/image/font/basicfont"
	"golang.org/x/image/math/fixed"

	"kaiju/engine"
	"kaiju/engine/assets"
	"kaiju/engine/collision"
	"kaiju/matrix"
	"kaiju/registry/shader_data_registry"
	"kaiju/rendering"
)

const (
	monTexW = 512
	monTexH = 256
)

// alwaysVisibleCuller is a ViewCuller that never culls — everything is in view.
// Used for flat quads whose zero-depth AABBs fail the camera frustum test.
type alwaysVisibleCuller struct{}

func (alwaysVisibleCuller) IsInView(_ collision.AABB) bool { return true }
func (alwaysVisibleCuller) ViewChanged() bool              { return false }

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

// newMeshQuadNegZ creates a quad mesh facing -Z with correct CCW winding.
// The standard Kaiju quad faces +Z; this one is visible from -Z (camera side).
func newMeshQuadNegZ(cache *rendering.MeshCache) *rendering.Mesh {
	const key = "quad_neg_z"
	if mesh, ok := cache.FindMesh(key); ok {
		return mesh
	}
	// Same vertex positions as the standard center quad.
	// Normal = (0,0,-1) so it faces -Z.
	// UVs are horizontally mirrored so text reads left-to-right from -Z.
	verts := []rendering.Vertex{
		{Position: matrix.Vec3{-0.5, -0.5, 0}, Normal: matrix.Vec3{0, 0, -1}, UV0: matrix.Vec2{1, 1}, Color: matrix.ColorWhite()},
		{Position: matrix.Vec3{-0.5, 0.5, 0}, Normal: matrix.Vec3{0, 0, -1}, UV0: matrix.Vec2{1, 0}, Color: matrix.ColorWhite()},
		{Position: matrix.Vec3{0.5, 0.5, 0}, Normal: matrix.Vec3{0, 0, -1}, UV0: matrix.Vec2{0, 0}, Color: matrix.ColorWhite()},
		{Position: matrix.Vec3{0.5, -0.5, 0}, Normal: matrix.Vec3{0, 0, -1}, UV0: matrix.Vec2{0, 1}, Color: matrix.ColorWhite()},
	}
	// Reversed winding: {0,1,2, 0,2,3} instead of standard {0,2,1, 0,3,2}.
	// This makes the -Z facing side the CCW front face.
	indices := []uint32{0, 1, 2, 0, 2, 3}
	return cache.Mesh(key, verts, indices)
}

func (mt *MonitorTextBlock) initQuad() {
	host := mt.host

	// Initial blank texture (dark monitor "off" state)
	blankImg := rasterizeMonitorText("", monTexW, monTexH, mt.fgColor)

	// Create GPU texture from raw RGBA pixel data
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

	// Custom quad mesh facing -Z (toward scientist at Z=-6.5)
	mesh := newMeshQuadNegZ(host.MeshCache())
	mt.entity = engine.NewEntity(host.WorkGroup())
	mt.entity.Transform.SetPosition(mt.position)
	mt.entity.Transform.SetScale(matrix.NewVec3(
		matrix.Float(mt.quadW), matrix.Float(mt.quadH), 1))
	// No rotation needed — the mesh already faces -Z

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
		ViewCuller: alwaysVisibleCuller{}, // Flat quads have zero-depth AABBs
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
	// No mirrorImageH needed — the -Z quad's UVs handle the orientation.

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
	textZ := monitorZ - 0.04 // In front of screen surface (enough gap to avoid Z-fighting)

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
