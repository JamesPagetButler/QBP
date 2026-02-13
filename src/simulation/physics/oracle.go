// Package physics provides the verified physics oracle for the QBP simulation.
//
// It uses the Lean-proven oracle as the source of truth for all physics calculations.
// The primary integration is via subprocess (calling `lake exe oracle`), which is
// reliable and uses the same verified code as the FFI approach.
//
// Future: If Lean→C shared library export matures, switch to cgo FFI for lower latency.
package physics

import (
	"encoding/json"
	"fmt"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
)

// Prediction holds a single oracle prediction for a given angle.
type Prediction struct {
	Experiment  string  `json:"experiment"`
	Label       string  `json:"label"`
	ThetaRad    float64 `json:"theta_rad"`
	ProbUp      float64 `json:"prob_up"`
	ProbDown    float64 `json:"prob_down"`
	Expectation float64 `json:"expectation"`
}

// Oracle provides physics calculations backed by the Lean-proven oracle.
type Oracle struct {
	predictions map[float64]Prediction // cache keyed by theta
	mu          sync.RWMutex
	proofsDir   string
}

// NewOracle creates a new Oracle instance.
// proofsDir should point to the proofs/ directory containing the Lean project.
func NewOracle(proofsDir string) *Oracle {
	return &Oracle{
		predictions: make(map[float64]Prediction),
		proofsDir:   proofsDir,
	}
}

// LoadPredictions loads oracle predictions from the committed JSON file.
// This is the preferred method — no Lean build required.
func (o *Oracle) LoadPredictions(jsonPath string) error {
	data, err := os.ReadFile(jsonPath)
	if err != nil {
		return fmt.Errorf("reading oracle predictions: %w", err)
	}

	var preds []Prediction
	if err := json.Unmarshal(data, &preds); err != nil {
		return fmt.Errorf("parsing oracle predictions: %w", err)
	}

	o.mu.Lock()
	defer o.mu.Unlock()
	for _, p := range preds {
		o.predictions[p.ThetaRad] = p
	}
	return nil
}

// GeneratePredictions calls the Lean oracle executable to generate fresh predictions.
// Requires Lean 4 and lake to be installed. Falls back to cached predictions.
func (o *Oracle) GeneratePredictions() error {
	cmd := exec.Command("lake", "exe", "oracle")
	cmd.Dir = o.proofsDir

	output, err := cmd.Output()
	if err != nil {
		return fmt.Errorf("running lean oracle: %w", err)
	}

	var preds []Prediction
	if err := json.Unmarshal(output, &preds); err != nil {
		return fmt.Errorf("parsing oracle output: %w", err)
	}

	o.mu.Lock()
	defer o.mu.Unlock()
	for _, p := range preds {
		o.predictions[p.ThetaRad] = p
	}
	return nil
}

// ProbUp returns the probability of spin-up for a state at angle theta.
// Uses cached predictions if available, otherwise computes analytically
// using the proven formula P(+) = cos²(θ/2).
func (o *Oracle) ProbUp(theta float64) float64 {
	o.mu.RLock()
	if p, ok := o.findNearest(theta); ok {
		o.mu.RUnlock()
		return p.ProbUp
	}
	o.mu.RUnlock()
	// Analytical fallback: cos²(θ/2) — matches the proven formula
	half := theta / 2.0
	return math.Cos(half) * math.Cos(half)
}

// ProbDown returns the probability of spin-down for a state at angle theta.
func (o *Oracle) ProbDown(theta float64) float64 {
	o.mu.RLock()
	if p, ok := o.findNearest(theta); ok {
		o.mu.RUnlock()
		return p.ProbDown
	}
	o.mu.RUnlock()
	half := theta / 2.0
	return math.Sin(half) * math.Sin(half)
}

// Expectation returns the expectation value for a state at angle theta.
func (o *Oracle) Expectation(theta float64) float64 {
	o.mu.RLock()
	if p, ok := o.findNearest(theta); ok {
		o.mu.RUnlock()
		return p.Expectation
	}
	o.mu.RUnlock()
	return math.Cos(theta)
}

// findNearest finds a cached prediction within tolerance of the given theta.
// Must be called with at least a read lock held.
func (o *Oracle) findNearest(theta float64) (Prediction, bool) {
	const tolerance = 1e-6
	for t, p := range o.predictions {
		if math.Abs(t-theta) < tolerance {
			return p, true
		}
	}
	return Prediction{}, false
}

// FindProjectRoot walks up from the current directory to find the QBP project root.
func FindProjectRoot() (string, error) {
	dir, err := os.Getwd()
	if err != nil {
		return "", err
	}

	for {
		if _, err := os.Stat(filepath.Join(dir, "proofs", "lakefile.lean")); err == nil {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "", fmt.Errorf("could not find QBP project root")
		}
		dir = parent
	}
}
