//go:build !editor

// Double-Slit concrete devices implementing the instrument interfaces.
//
// Devices:
//   - DSEmitter:       Movable — controls particle emission rate
//   - DSSlit:          Movable — adjusts slit separation and width
//   - DSDetector:      Triggerable — accumulates hits, emits DataEvents
//   - DSOracle:        Triggerable — loads oracle predictions for V&V

package main

import (
	"encoding/json"
	"fmt"
	"math"
	"math/rand"
	"os"
)

const dsHistogramBins = 100

// ---------------------------------------------------------------------------
// DSEmitter — Movable: controls particle emission
// ---------------------------------------------------------------------------

type DSEmitter struct {
	name   string
	status DeviceStatus
	rate   float64 // particles per second
}

func NewDSEmitter() *DSEmitter {
	return &DSEmitter{
		name:   "emitter",
		status: StatusIdle,
		rate:   500,
	}
}

func (e *DSEmitter) Name() string         { return e.name }
func (e *DSEmitter) Status() DeviceStatus { return e.status }
func (e *DSEmitter) Update(dt float64)    {} // Emitter has no per-frame work

func (e *DSEmitter) Params() []ParamDescriptor {
	return []ParamDescriptor{
		{Name: "rate", Min: 10, Max: 5000, Default: 500, Unit: "Hz"},
	}
}

func (e *DSEmitter) Set(param string, value float64) error {
	switch param {
	case "rate":
		if value < 10 || value > 5000 {
			return fmt.Errorf("rate out of range [10, 5000]: %f", value)
		}
		e.rate = value
		return nil
	default:
		return fmt.Errorf("unknown param: %s", param)
	}
}

func (e *DSEmitter) Get(param string) (float64, error) {
	switch param {
	case "rate":
		return e.rate, nil
	default:
		return 0, fmt.Errorf("unknown param: %s", param)
	}
}

// ---------------------------------------------------------------------------
// DSSlit — Movable: adjusts slit geometry
// ---------------------------------------------------------------------------

type DSSlit struct {
	name       string
	status     DeviceStatus
	separation float64 // d in meters
	width      float64 // a in meters
}

func NewDSSlit() *DSSlit {
	p := presets[2] // Tonomura defaults
	return &DSSlit{
		name:       "slit",
		status:     StatusIdle,
		separation: p.SlitSep,
		width:      p.SlitWidth,
	}
}

func (s *DSSlit) Name() string         { return s.name }
func (s *DSSlit) Status() DeviceStatus { return s.status }
func (s *DSSlit) Update(dt float64)    {}

func (s *DSSlit) Params() []ParamDescriptor {
	return []ParamDescriptor{
		{Name: "separation", Min: 0.1e-6, Max: 10e-6, Default: 1e-6, LogScale: true, Unit: "m"},
		{Name: "width", Min: 0.01e-6, Max: 1e-6, Default: 0.1e-6, LogScale: true, Unit: "m"},
	}
}

func (s *DSSlit) Set(param string, value float64) error {
	switch param {
	case "separation":
		s.separation = value
		return nil
	case "width":
		s.width = value
		return nil
	default:
		return fmt.Errorf("unknown param: %s", param)
	}
}

func (s *DSSlit) Get(param string) (float64, error) {
	switch param {
	case "separation":
		return s.separation, nil
	case "width":
		return s.width, nil
	default:
		return 0, fmt.Errorf("unknown param: %s", param)
	}
}

// ---------------------------------------------------------------------------
// DSDetector — Triggerable: accumulates particle hits
// ---------------------------------------------------------------------------

type DSDetector struct {
	name      string
	status    DeviceStatus
	physics   *LabPhysicsEngine
	mapper    *LabCoordMapper
	eventCh   chan DataEvent
	rng       *rand.Rand
	emitTimer float64

	Hits      []HitRecord
	Histogram [dsHistogramBins]int
	TotalHits int
}

func NewDSDetector(physics *LabPhysicsEngine, mapper *LabCoordMapper) *DSDetector {
	return &DSDetector{
		name:    "detector",
		status:  StatusIdle,
		physics: physics,
		mapper:  mapper,
		eventCh: make(chan DataEvent, 256),
		rng:     rand.New(rand.NewSource(99)),
		Hits:    make([]HitRecord, 0, 10000),
	}
}

func (d *DSDetector) Name() string         { return d.name }
func (d *DSDetector) Status() DeviceStatus { return d.status }

func (d *DSDetector) Start() error {
	d.status = StatusRunning
	return nil
}

func (d *DSDetector) Stop() error {
	d.status = StatusIdle
	return nil
}

func (d *DSDetector) Subscribe() <-chan DataEvent { return d.eventCh }

// Update accumulates hits when the detector is running.
// emitRate is passed from the emitter device.
func (d *DSDetector) Update(dt float64) {
	// Detector accumulation is driven by UpdateWithRate from the room.
}

// UpdateWithRate is the room-level driver that feeds the emitter rate.
func (d *DSDetector) UpdateWithRate(dt float64, emitRate float64) {
	if d.status != StatusRunning {
		return
	}

	d.emitTimer += dt
	interval := 1.0 / emitRate
	for d.emitTimer >= interval {
		d.emitTimer -= interval

		x := d.physics.SampleHitPosition()
		ndux := d.mapper.PhysToNDU(x)
		nduy := (d.rng.Float64() - 0.5) * 0.3

		t := (x/d.mapper.PhysHalfWidth + 1) / 2
		bin := int(t * dsHistogramBins)
		if bin < 0 {
			bin = 0
		}
		if bin >= dsHistogramBins {
			bin = dsHistogramBins - 1
		}

		hit := HitRecord{PhysX: x, NDUX: ndux, NDUY: nduy, Bin: bin}
		d.Hits = append(d.Hits, hit)
		d.Histogram[bin]++
		d.TotalHits++

		// Non-blocking send to event channel
		select {
		case d.eventCh <- DataEvent{Source: d.name, Payload: hit}:
		default:
		}
	}
}

func (d *DSDetector) Reset() {
	d.Hits = d.Hits[:0]
	d.Histogram = [dsHistogramBins]int{}
	d.TotalHits = 0
	d.emitTimer = 0
}

// MeasuredVisibility estimates V = (Imax - Imin) / (Imax + Imin) from the histogram.
// Mirrors: floatVisibility in FloatCompute.lean
// Returns -1 if insufficient data.
func (d *DSDetector) MeasuredVisibility() float64 {
	if d.TotalHits < 1000 {
		return -1
	}

	// Find max and min bin values (excluding edge bins which may have boundary effects)
	maxBin := 0
	minBin := d.TotalHits
	for i := 5; i < dsHistogramBins-5; i++ {
		if d.Histogram[i] > maxBin {
			maxBin = d.Histogram[i]
		}
		if d.Histogram[i] < minBin {
			minBin = d.Histogram[i]
		}
	}

	if maxBin+minBin == 0 {
		return -1
	}
	return QBPVisibility(float64(maxBin), float64(minBin))
}

// FringeSpacingEstimate computes weighted center-of-mass fringe spacing.
func (d *DSDetector) FringeSpacingEstimate() float64 {
	if d.TotalHits < 100 {
		return 0
	}

	// Find peaks via simple derivative sign change
	smoothed := make([]float64, dsHistogramBins)
	for i := 1; i < dsHistogramBins-1; i++ {
		smoothed[i] = float64(d.Histogram[i-1]+2*d.Histogram[i]+d.Histogram[i+1]) / 4.0
	}

	var peaks []int
	for i := 2; i < dsHistogramBins-2; i++ {
		if smoothed[i] > smoothed[i-1] && smoothed[i] > smoothed[i+1] && smoothed[i] > 3 {
			peaks = append(peaks, i)
		}
	}

	if len(peaks) < 2 {
		return 0
	}

	// Average spacing between adjacent peaks in NDU
	totalSpacing := 0.0
	for i := 1; i < len(peaks); i++ {
		binSpacing := float64(peaks[i] - peaks[i-1])
		totalSpacing += binSpacing
	}
	avgBinSpacing := totalSpacing / float64(len(peaks)-1)

	// Convert bin spacing to physical spacing
	physRange := 2.0 * d.mapper.PhysHalfWidth
	physSpacing := avgBinSpacing * physRange / float64(dsHistogramBins)
	return physSpacing
}

// ---------------------------------------------------------------------------
// DSOracle — Triggerable: provides expected predictions for V&V
// ---------------------------------------------------------------------------

type OraclePrediction struct {
	Experiment string                 `json:"experiment"`
	Property   string                 `json:"property"`
	Value      json.RawMessage        `json:"value"`
	Params     map[string]interface{} `json:"params"`
}

type DSOracle struct {
	name        string
	status      DeviceStatus
	eventCh     chan DataEvent
	Predictions []OraclePrediction
}

func NewDSOracle() *DSOracle {
	oracle := &DSOracle{
		name:    "oracle",
		status:  StatusIdle,
		eventCh: make(chan DataEvent, 16),
	}
	oracle.loadPredictions()
	return oracle
}

func (o *DSOracle) loadPredictions() {
	// Try multiple paths — binary runs from src/bakeoff/kaiju/ but project root varies
	paths := []string{
		"../../../tests/oracle_predictions.json",   // from src/bakeoff/kaiju/
		"../../tests/oracle_predictions.json",       // from src/bakeoff/kaiju/engine/
		"tests/oracle_predictions.json",             // from project root
		"src/bakeoff/kaiju/../../../tests/oracle_predictions.json",
	}
	var data []byte
	var err error
	for _, p := range paths {
		data, err = os.ReadFile(p)
		if err == nil {
			break
		}
	}
	if err != nil {
		fmt.Printf("Warning: could not load oracle predictions: %v\n", err)
		return
	}

	var all []OraclePrediction
	if err := json.Unmarshal(data, &all); err != nil {
		fmt.Printf("Warning: could not parse oracle predictions: %v\n", err)
		return
	}

	// Filter to experiment 03 only
	for _, p := range all {
		if p.Experiment == "03" {
			o.Predictions = append(o.Predictions, p)
		}
	}
	fmt.Printf("Oracle loaded %d predictions for experiment 03\n", len(o.Predictions))
}

func (o *DSOracle) Name() string         { return o.name }
func (o *DSOracle) Status() DeviceStatus { return o.status }
func (o *DSOracle) Update(dt float64)    {}

func (o *DSOracle) Start() error {
	o.status = StatusRunning
	return nil
}

func (o *DSOracle) Stop() error {
	o.status = StatusIdle
	return nil
}

func (o *DSOracle) Subscribe() <-chan DataEvent { return o.eventCh }

// ExpectedFringeSpacing returns the analytical fringe spacing λL/d.
func (o *DSOracle) ExpectedFringeSpacing(wavelength, screenDist, slitSep float64) float64 {
	return wavelength * screenDist / slitSep
}

// ---------------------------------------------------------------------------
// V&V Verdict Logic
// ---------------------------------------------------------------------------

type VVVerdict int

const (
	VerdictCollecting VVVerdict = iota
	VerdictPass
	VerdictFail
	VerdictUnvalidated
)

func (v VVVerdict) String() string {
	switch v {
	case VerdictCollecting:
		return "COLLECTING..."
	case VerdictPass:
		return "PASS"
	case VerdictFail:
		return "FAIL"
	case VerdictUnvalidated:
		return "UNVALIDATED"
	default:
		return "UNKNOWN"
	}
}

// ComputeVerdict checks accumulated data against oracle predictions.
// For standard QM presets: validates fringe spacing within 5%.
// For QBP presets: also validates that visibility matches V = 1-η prediction.
func ComputeVerdict(detector *DSDetector, oracle *DSOracle, physics *LabPhysicsEngine, presetID string) VVVerdict {
	if presetID == "" || presetID == "custom" {
		return VerdictUnvalidated
	}

	if detector.TotalHits < 1000 {
		return VerdictCollecting
	}

	expected := oracle.ExpectedFringeSpacing(physics.Wavelength, physics.ScreenDist, physics.SlitSep)
	measured := detector.FringeSpacingEstimate()

	if measured == 0 || expected == 0 {
		return VerdictCollecting
	}

	// Check 1: Fringe spacing within 5%
	relError := math.Abs(measured-expected) / expected
	if relError >= 0.05 {
		return VerdictFail
	}

	// Check 2 (QBP presets): Verify visibility matches V = 1-η
	if physics.U1 > 0 && detector.TotalHits >= 3000 {
		expectedVis := physics.Visibility()
		measuredVis := detector.MeasuredVisibility()
		if measuredVis >= 0 {
			visError := math.Abs(measuredVis - expectedVis)
			if visError > 0.15 { // Wider tolerance for visibility (statistical)
				return VerdictFail
			}
		}
	}

	return VerdictPass
}
