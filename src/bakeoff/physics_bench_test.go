// Physics engine benchmarks — shared between Raylib and Kaiju.
// Both engines use identical physics code, so this tests it once.
//
// Run: cd src/bakeoff && go test -bench . -benchtime 3s -v
package bakeoff

import (
	"math"
	"math/rand"
	"testing"
)

// ---------------------------------------------------------------------------
// Physics Engine (copied from prototypes — identical in both)
// ---------------------------------------------------------------------------

const (
	benchSlitSep    = 1.0e-6
	benchWavelength = 5.0e-11
	benchScreenDist = 1.0
	benchSlitWidth  = 1.0e-7
	benchHistBins   = 100
)

type benchPhysicsEngine struct {
	SlitSep    float64
	Wavelength float64
	ScreenDist float64
	SlitWidth  float64
	rng        *rand.Rand
}

func newBenchPhysicsEngine() *benchPhysicsEngine {
	return &benchPhysicsEngine{
		SlitSep:    benchSlitSep,
		Wavelength: benchWavelength,
		ScreenDist: benchScreenDist,
		SlitWidth:  benchSlitWidth,
		rng:        rand.New(rand.NewSource(42)),
	}
}

func (e *benchPhysicsEngine) FringeSpacing() float64 {
	return e.Wavelength * e.ScreenDist / e.SlitSep
}

func (e *benchPhysicsEngine) Intensity(x float64) float64 {
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

func (e *benchPhysicsEngine) SampleHitPosition() float64 {
	halfWidth := 5.0 * e.FringeSpacing()
	for {
		x := (e.rng.Float64()*2 - 1) * halfWidth
		if e.rng.Float64() < e.Intensity(x) {
			return x
		}
	}
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

// BenchmarkIntensity measures raw intensity calculation throughput.
func BenchmarkIntensity(b *testing.B) {
	eng := newBenchPhysicsEngine()
	spacing := eng.FringeSpacing()
	halfW := 5.0 * spacing
	step := 2.0 * halfW / float64(b.N)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		x := -halfW + float64(i)*step
		_ = eng.Intensity(x)
	}
}

// BenchmarkSampleHitPosition measures rejection sampler throughput.
func BenchmarkSampleHitPosition(b *testing.B) {
	eng := newBenchPhysicsEngine()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = eng.SampleHitPosition()
	}
}

// BenchmarkFringeSpacing measures fringe spacing calculation.
func BenchmarkFringeSpacing(b *testing.B) {
	eng := newBenchPhysicsEngine()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = eng.FringeSpacing()
	}
}

// ---------------------------------------------------------------------------
// Accuracy Tests
// ---------------------------------------------------------------------------

// TestIntensityPeaks verifies I(x) peaks at expected positions.
func TestIntensityPeaks(t *testing.T) {
	eng := newBenchPhysicsEngine()
	spacing := eng.FringeSpacing()

	// Central peak at x=0 should be 1.0
	I0 := eng.Intensity(0)
	if math.Abs(I0-1.0) > 1e-10 {
		t.Errorf("Central peak: got %f, want 1.0", I0)
	}

	// Minima at x = (n+0.5) × λL/d (between fringes)
	for _, n := range []float64{0, 1, 2, 3} {
		xMin := (n + 0.5) * spacing
		IMin := eng.Intensity(xMin)
		if IMin > 0.01 {
			t.Errorf("Minimum at n=%v: got %f, want ~0", n, IMin)
		}
	}

	// Secondary peaks at x = n × λL/d (should be near 1.0 for small n)
	for _, n := range []float64{1, 2} {
		xPeak := n * spacing
		IPeak := eng.Intensity(xPeak)
		// Envelope sinc² reduces these, but cos² should be ~1
		if IPeak < 0.1 {
			t.Errorf("Peak at n=%v: got %f, want > 0.1", n, IPeak)
		}
	}
}

// TestFringeSpacing verifies the analytical formula.
func TestFringeSpacing(t *testing.T) {
	eng := newBenchPhysicsEngine()
	expected := benchWavelength * benchScreenDist / benchSlitSep
	got := eng.FringeSpacing()
	if math.Abs(got-expected)/expected > 1e-12 {
		t.Errorf("FringeSpacing: got %e, want %e", got, expected)
	}
}

// TestHistogramConvergence checks that N samples produce a recognizable
// fringe pattern (peak at center, minima between fringes).
func TestHistogramConvergence(t *testing.T) {
	eng := newBenchPhysicsEngine()
	halfWidth := 5.0 * eng.FringeSpacing()

	counts := [benchHistBins]int{}
	N := 50000
	for i := 0; i < N; i++ {
		x := eng.SampleHitPosition()
		norm := (x/halfWidth + 1) / 2
		bin := int(norm * benchHistBins)
		if bin < 0 {
			bin = 0
		}
		if bin >= benchHistBins {
			bin = benchHistBins - 1
		}
		counts[bin]++
	}

	// Central bin (around bin 50) should be the highest region
	centerBin := benchHistBins / 2
	centerCount := counts[centerBin] + counts[centerBin-1] + counts[centerBin+1]

	// Edge bins (0-5, 95-99) should have much fewer
	edgeCount := 0
	for i := 0; i < 5; i++ {
		edgeCount += counts[i] + counts[benchHistBins-1-i]
	}

	if centerCount < edgeCount {
		t.Errorf("Center (%d) should exceed edges (%d) — fringe pattern not forming", centerCount, edgeCount)
	}

	t.Logf("Histogram convergence: center 3-bin=%d, edge 10-bin=%d, N=%d", centerCount, edgeCount, N)
}

// TestSamplerDistribution verifies the sampled distribution matches
// the analytical intensity pattern using mean-square comparison.
func TestSamplerDistribution(t *testing.T) {
	eng := newBenchPhysicsEngine()
	halfWidth := 5.0 * eng.FringeSpacing()

	// Use a finer histogram for better resolution
	const fineBins = 500
	counts := [fineBins]float64{}
	N := 200000
	for i := 0; i < N; i++ {
		x := eng.SampleHitPosition()
		norm := (x/halfWidth + 1) / 2
		bin := int(norm * fineBins)
		if bin < 0 {
			bin = 0
		}
		if bin >= fineBins {
			bin = fineBins - 1
		}
		counts[bin]++
	}

	// Normalize counts to [0,1] range
	maxCount := 0.0
	for _, c := range counts {
		if c > maxCount {
			maxCount = c
		}
	}

	// Compare normalized histogram to analytical I(x)
	// Compute R² (coefficient of determination)
	var ssRes, ssTot, mean float64
	for i := 0; i < fineBins; i++ {
		mean += counts[i] / maxCount
	}
	mean /= fineBins

	for i := 0; i < fineBins; i++ {
		x := (float64(i)/fineBins*2 - 1) * halfWidth
		expected := eng.Intensity(x)
		observed := counts[i] / maxCount
		ssRes += (observed - expected) * (observed - expected)
		ssTot += (observed - mean) * (observed - mean)
	}

	r2 := 1.0 - ssRes/ssTot
	t.Logf("Distribution fit: R²=%.4f (N=%d, bins=%d)", r2, N, fineBins)

	if r2 < 0.85 {
		t.Errorf("Distribution R²=%.4f < 0.85 — sampler not matching Fraunhofer pattern", r2)
	}
}
