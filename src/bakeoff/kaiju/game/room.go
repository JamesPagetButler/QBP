//go:build !editor

// Experiment Room Framework for QBP Virtual Lab
//
// Each experiment lives in a Room that owns its devices, physics, monitors,
// and UI. Rooms are designed to be slotted into a hallway (future #393)
// but for now are launched directly from the lab game.

package main

import "kaiju/engine"

// ExperimentRoom is the interface that each experiment room implements.
// The lab game delegates to the active room for setup, update, and teardown.
type ExperimentRoom interface {
	ID() string
	DisplayName() string
	Devices() []Device
	Setup(host *engine.Host)
	Update(dt float64)
	Teardown()
}
