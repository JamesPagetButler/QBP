// Package scene provides 3D rendering of the Stern-Gerlach experiment apparatus.
package scene

import (
	rl "github.com/gen2brain/raylib-go/raylib"
)

// Apparatus holds the geometry for the Stern-Gerlach experimental setup.
type Apparatus struct {
	MagnetPos    rl.Vector3
	MagnetSize   rl.Vector3
	SourcePos    rl.Vector3
	DetectorPos  rl.Vector3
	DetectorSize rl.Vector3
	BeamLength   float32
}

// DefaultApparatus returns a standard Stern-Gerlach apparatus layout.
func DefaultApparatus() *Apparatus {
	return &Apparatus{
		MagnetPos:    rl.NewVector3(0, 0, 0),
		MagnetSize:   rl.NewVector3(2, 4, 2),
		SourcePos:    rl.NewVector3(-8, 0, 0),
		DetectorPos:  rl.NewVector3(8, 0, 0),
		DetectorSize: rl.NewVector3(0.5, 6, 3),
		BeamLength:   16,
	}
}

// Draw renders the apparatus in 3D space.
func (a *Apparatus) Draw() {
	// Source (particle emitter)
	rl.DrawCube(a.SourcePos, 1.5, 1.5, 1.5, rl.DarkGray)
	rl.DrawCubeWires(a.SourcePos, 1.5, 1.5, 1.5, rl.Black)

	// Magnet — north pole (red, top)
	northPos := rl.NewVector3(a.MagnetPos.X, a.MagnetPos.Y+1.5, a.MagnetPos.Z)
	rl.DrawCube(northPos, a.MagnetSize.X, 1, a.MagnetSize.Z, rl.Red)
	rl.DrawCubeWires(northPos, a.MagnetSize.X, 1, a.MagnetSize.Z, rl.Maroon)

	// Magnet — south pole (blue, bottom)
	southPos := rl.NewVector3(a.MagnetPos.X, a.MagnetPos.Y-1.5, a.MagnetPos.Z)
	rl.DrawCube(southPos, a.MagnetSize.X, 1, a.MagnetSize.Z, rl.Blue)
	rl.DrawCubeWires(southPos, a.MagnetSize.X, 1, a.MagnetSize.Z, rl.DarkBlue)

	// Gap between poles (shows field gradient)
	rl.DrawCube(a.MagnetPos, a.MagnetSize.X, 2, a.MagnetSize.Z,
		rl.NewColor(200, 200, 200, 60))

	// Detector screen
	rl.DrawCube(a.DetectorPos, a.DetectorSize.X, a.DetectorSize.Y, a.DetectorSize.Z,
		rl.NewColor(50, 50, 50, 200))
	rl.DrawCubeWires(a.DetectorPos, a.DetectorSize.X, a.DetectorSize.Y, a.DetectorSize.Z,
		rl.White)

	// Beam path (dotted line effect via segments)
	segments := 20
	for i := 0; i < segments; i++ {
		if i%2 == 0 {
			t0 := float32(i) / float32(segments)
			t1 := float32(i+1) / float32(segments)
			start := rl.NewVector3(
				a.SourcePos.X+t0*a.BeamLength, 0, 0)
			end := rl.NewVector3(
				a.SourcePos.X+t1*a.BeamLength, 0, 0)
			rl.DrawLine3D(start, end, rl.Yellow)
		}
	}

	// Labels (drawn as 3D text positions — actual text rendered in 2D overlay)
}

// DrawLabels renders 2D text labels for apparatus components.
func (a *Apparatus) DrawLabels(camera rl.Camera3D) {
	// Source label
	srcScreen := rl.GetWorldToScreen(a.SourcePos, camera)
	rl.DrawText("Source", int32(srcScreen.X)-20, int32(srcScreen.Y)+20, 14, rl.White)

	// Magnet label
	magScreen := rl.GetWorldToScreen(
		rl.NewVector3(a.MagnetPos.X, a.MagnetPos.Y+3, a.MagnetPos.Z), camera)
	rl.DrawText("N", int32(magScreen.X)-5, int32(magScreen.Y), 16, rl.Red)

	magScreenS := rl.GetWorldToScreen(
		rl.NewVector3(a.MagnetPos.X, a.MagnetPos.Y-3, a.MagnetPos.Z), camera)
	rl.DrawText("S", int32(magScreenS.X)-5, int32(magScreenS.Y), 16, rl.Blue)

	// Detector label
	detScreen := rl.GetWorldToScreen(a.DetectorPos, camera)
	rl.DrawText("Detector", int32(detScreen.X)-25, int32(detScreen.Y)+20, 14, rl.White)
}
