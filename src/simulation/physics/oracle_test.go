package physics

import (
	"math"
	"os"
	"path/filepath"
	"testing"
)

func TestOracleLoadPredictions(t *testing.T) {
	// Find the oracle predictions JSON relative to the project root
	root, err := FindProjectRoot()
	if err != nil {
		t.Skip("Cannot find project root, skipping oracle test")
	}

	jsonPath := filepath.Join(root, "tests", "oracle_predictions.json")
	if _, err := os.Stat(jsonPath); err != nil {
		t.Skipf("Oracle predictions not found at %s", jsonPath)
	}

	oracle := NewOracle(filepath.Join(root, "proofs"))
	if err := oracle.LoadPredictions(jsonPath); err != nil {
		t.Fatalf("Failed to load predictions: %v", err)
	}

	// Verify known values
	tests := []struct {
		name     string
		theta    float64
		wantUp   float64
		wantDown float64
		wantExp  float64
	}{
		{"theta=0", 0.0, 1.0, 0.0, 1.0},
		{"theta=pi", math.Pi, 0.0, 1.0, -1.0},
	}

	const tolerance = 1e-4 // Lean Float has ~6 decimal digits of precision

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotUp := oracle.ProbUp(tt.theta)
			if math.Abs(gotUp-tt.wantUp) > tolerance {
				t.Errorf("ProbUp(%f) = %f, want %f", tt.theta, gotUp, tt.wantUp)
			}

			gotDown := oracle.ProbDown(tt.theta)
			if math.Abs(gotDown-tt.wantDown) > tolerance {
				t.Errorf("ProbDown(%f) = %f, want %f", tt.theta, gotDown, tt.wantDown)
			}

			gotExp := oracle.Expectation(tt.theta)
			if math.Abs(gotExp-tt.wantExp) > tolerance {
				t.Errorf("Expectation(%f) = %f, want %f", tt.theta, gotExp, tt.wantExp)
			}
		})
	}
}

func TestOracleAnalyticalFallback(t *testing.T) {
	// Test without loading predictions — should use analytical fallback
	oracle := NewOracle("")

	const tolerance = 1e-10

	tests := []struct {
		name     string
		theta    float64
		wantUp   float64
		wantDown float64
		wantExp  float64
	}{
		{"theta=0", 0.0, 1.0, 0.0, 1.0},
		{"theta=pi/2", math.Pi / 2, 0.5, 0.5, 0.0},
		{"theta=pi", math.Pi, 0.0, 1.0, -1.0},
		{"theta=pi/4", math.Pi / 4, math.Cos(math.Pi/8) * math.Cos(math.Pi/8),
			math.Sin(math.Pi/8) * math.Sin(math.Pi/8), math.Cos(math.Pi / 4)},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if math.Abs(oracle.ProbUp(tt.theta)-tt.wantUp) > tolerance {
				t.Errorf("ProbUp(%f) = %f, want %f", tt.theta, oracle.ProbUp(tt.theta), tt.wantUp)
			}
			if math.Abs(oracle.ProbDown(tt.theta)-tt.wantDown) > tolerance {
				t.Errorf("ProbDown(%f) = %f, want %f", tt.theta, oracle.ProbDown(tt.theta), tt.wantDown)
			}
			if math.Abs(oracle.Expectation(tt.theta)-tt.wantExp) > tolerance {
				t.Errorf("Expectation(%f) = %f, want %f", tt.theta, oracle.Expectation(tt.theta), tt.wantExp)
			}
		})
	}
}
