//go:build !editor

// Instrument Abstraction Layer for QBP Virtual Lab
//
// Inspired by Bluesky/ophyd (Device, Readable, Movable) and TANGO Controls
// (commands, attributes, properties). Adapted for a Go game loop where
// Update() is called every frame.
//
// Three core interfaces:
//   - Device:      base — has a name, status, per-frame update
//   - Movable:     writable parameters (sliders, knobs)
//   - Triggerable: start/stop with event stream output (detectors, oracles)

package main

// DeviceStatus represents the operational state of a lab device.
type DeviceStatus int

const (
	StatusIdle    DeviceStatus = iota // Device is idle
	StatusRunning                     // Device is actively producing/measuring
	StatusError                       // Device encountered an error
)

func (s DeviceStatus) String() string {
	switch s {
	case StatusIdle:
		return "IDLE"
	case StatusRunning:
		return "RUNNING"
	case StatusError:
		return "ERROR"
	default:
		return "UNKNOWN"
	}
}

// DataEvent is an event emitted by a Triggerable device.
// Payload is intentionally untyped — consumers assert to the expected type.
type DataEvent struct {
	Timestamp float64 // Simulation time (seconds since room start)
	Source    string  // Device name that emitted this event
	Payload  any     // float64, []float64, HitRecord, etc.
}

// HitRecord is the payload for a single particle detection event.
type HitRecord struct {
	PhysX float64 // Physical position in meters
	NDUX  float64 // Normalized display unit X
	NDUY  float64 // Normalized display unit Y (small spread)
	Bin   int     // Histogram bin index
}

// ParamDescriptor describes a single adjustable parameter on a Movable device.
type ParamDescriptor struct {
	Name     string
	Min, Max float64
	Default  float64
	LogScale bool
	Unit     string
}

// Device is the base interface for all lab instruments.
type Device interface {
	Name() string
	Status() DeviceStatus
	Update(dt float64) // Called every frame by the room's update loop
}

// Movable is a device with adjustable parameters (e.g., slit width, emitter rate).
type Movable interface {
	Device
	Set(param string, value float64) error
	Get(param string) (float64, error)
	Params() []ParamDescriptor
}

// Triggerable is a device that can be started/stopped and produces a stream
// of DataEvents (e.g., a detector accumulating hits, an oracle emitting predictions).
type Triggerable interface {
	Device
	Start() error
	Stop() error
	Subscribe() <-chan DataEvent
}
