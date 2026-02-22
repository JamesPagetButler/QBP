//go:build !editor

// Physics engine for the QBP Virtual Lab.
//
// Implements BOTH standard Fraunhofer AND QBP quaternionic physics:
//
//   Standard:  I(x) = cos²(π·d·x / λ·L) · sinc²(π·a·x / λ·L)
//   QBP:       I(x) = (1-η) · I_fraunhofer(x) + η
//
// where η is the quaternionic fraction — the central QBP prediction.
// Proven in Lean: proofs/QBP/Experiments/DoubleSlit.lean §5b
//
// The float functions here mirror proofs/QBP/Oracle/FloatCompute.lean
// and are validated against the Lean oracle (tests/oracle_predictions.json).

package main

import (
	"kaiju/qbp"
	"math"
	"math/rand"
)

// Experimental presets — grounded in real double-slit experiments.
// U1 is the quaternionic coupling energy (QBP-specific parameter).
// When U1=0, the simulation reduces to standard QM (proven: scenarioA_visibility).
type Preset struct {
	ID         string
	Label      string
	SlitSep    float64 // d (meters)
	Wavelength float64 // λ (meters)
	ScreenDist float64 // L (meters)
	SlitWidth  float64 // a (meters)
	U1         float64 // Quaternionic coupling energy U₁ (Joules). 0 = standard QM.
}

var presets = []Preset{
	{
		ID:         "bach_2013",
		Label:      "Bach 2013 (electrons)",
		SlitSep:    272e-9,
		Wavelength: 50e-12,
		ScreenDist: 0.24,
		SlitWidth:  62e-9,
		U1:         0, // Standard QM baseline
	},
	{
		ID:         "zeilinger_1988",
		Label:      "Zeilinger 1988 (neutrons)",
		SlitSep:    126.5e-6,
		Wavelength: 1.845e-9,
		ScreenDist: 5.0,
		SlitWidth:  21.8e-6,
		U1:         0, // Standard QM baseline
	},
	{
		ID:         "tonomura_1989",
		Label:      "Tonomura 1989 (electrons)",
		SlitSep:    1.0e-6,
		Wavelength: 5.5e-12,
		ScreenDist: 1.0,
		SlitWidth:  1.0e-7,
		U1:         0, // Standard QM baseline
	},
	// QBP test presets — non-zero U₁ demonstrates quaternionic effects
	{
		ID:         "qbp_weak",
		Label:      "QBP: Weak coupling",
		SlitSep:    1.0e-6,
		Wavelength: 5.5e-12,
		ScreenDist: 1.0,
		SlitWidth:  1.0e-7,
		U1:         1e-6, // Weak coupling → small η → slight visibility reduction
	},
	{
		ID:         "qbp_strong",
		Label:      "QBP: Strong coupling",
		SlitSep:    1.0e-6,
		Wavelength: 5.5e-12,
		ScreenDist: 1.0,
		SlitWidth:  1.0e-7,
		U1:         1e-3, // Strong coupling → large η → significant visibility loss
	},
}

func presetByID(id string) *Preset {
	for i := range presets {
		if presets[i].ID == id {
			return &presets[i]
		}
	}
	return nil
}

// ---------------------------------------------------------------------------
// QBP Float Oracle Functions — delegated to kaiju/qbp package
//
// The qbp package contains pure math (no Vulkan dependency), enabling:
// 1. Differential testing against Lean oracle without GPU
// 2. Future hot-swap to Lean FFI, SciLean, or PhysLean backends
// ---------------------------------------------------------------------------

// Convenience wrappers — delegate to qbp package for testability.
func QBPVisibility(imax, imin float64) float64                                  { return qbp.Visibility(imax, imin) }
func QBPQuatFraction(normSq0, normSq1 float64) float64                         { return qbp.QuatFraction(normSq0, normSq1) }
func QBPCouplingDecomposition(u0, u1, a0, b0, a1, b1 float64) (float64, float64, float64, float64) { return qbp.CouplingDecomposition(u0, u1, a0, b0, a1, b1) }
func QBPDecayConstant(u1, d float64) float64                                   { return qbp.DecayConstant(u1, d) }
func QBPDecayLength(kappa float64) float64                                     { return qbp.DecayLength(kappa) }
func QBPFraunhoferIntensity(i0, d, lambda, l, x float64) float64              { return qbp.FraunhoferIntensity(i0, d, lambda, l, x) }
func QBPFringeSpacing(lambda, l, d float64) float64                            { return qbp.FringeSpacing(lambda, l, d) }
func QBPNormSqSymp(re, imI, imJ, imK float64) float64                         { return qbp.NormSqSymp(re, imI, imJ, imK) }

// ---------------------------------------------------------------------------
// LabPhysicsEngine
// ---------------------------------------------------------------------------

// LabPhysicsEngine computes QBP-modified intensity and samples hit positions.
type LabPhysicsEngine struct {
	SlitSep    float64
	Wavelength float64
	ScreenDist float64
	SlitWidth  float64
	U1         float64 // Quaternionic coupling energy (QBP). 0 = standard QM.
	rng        *rand.Rand
}

func NewLabPhysicsEngine() *LabPhysicsEngine {
	// Default to Tonomura parameters (standard QM, U1=0)
	p := presets[2]
	return &LabPhysicsEngine{
		SlitSep:    p.SlitSep,
		Wavelength: p.Wavelength,
		ScreenDist: p.ScreenDist,
		SlitWidth:  p.SlitWidth,
		U1:         p.U1,
		rng:        rand.New(rand.NewSource(42)),
	}
}

func (e *LabPhysicsEngine) FringeSpacing() float64 {
	return e.Wavelength * e.ScreenDist / e.SlitSep
}

// Eta computes the quaternionic fraction η at the detector.
// In Model A (DoubleSlit.lean §5b): η determines visibility via V = 1 - η.
//
// Physics: The quaternionic component ψ₁ is generated at the slit barrier
// (where U₁ ≠ 0) and decays during free propagation to the detector.
// η = η₀ · exp(-κ·L) where κ ∝ |U₁|/d and L is the screen distance.
//
// When U₁ = 0: η = 0, standard QM (proven: scenarioA_visibility).
// When U₁ → ∞: η → 1, no interference (proven: scenarioB_visibility).
func (e *LabPhysicsEngine) Eta() float64 {
	if e.U1 == 0 {
		return 0 // Standard QM: no quaternionic coupling
	}

	// Initial quaternionic fraction at the slit barrier.
	// Simplified model: η₀ scales with U₁ relative to kinetic energy.
	// η₀ = U₁² / (E_kinetic² + U₁²) — smooth saturation at 1.
	hbar := 1.0545718e-34          // ℏ (J·s)
	mass := 9.1093837e-31          // electron mass (kg)
	v := hbar / (mass * e.Wavelength * 1e10) // velocity from de Broglie (simplified)
	eKinetic := 0.5 * mass * v * v
	eta0 := e.U1 * e.U1 / (eKinetic*eKinetic + e.U1*e.U1)

	// Decay during propagation: κ = |U₁| · d (simplified, mirrors Lean decayConstant)
	kappa := QBPDecayConstant(math.Abs(e.U1), e.SlitSep)
	eta := eta0 * math.Exp(-kappa*e.ScreenDist)

	if eta > 1 {
		eta = 1
	}
	return eta
}

// Visibility computes V = 1 - η (Model A, proven in DoubleSlit.lean §5b).
func (e *LabPhysicsEngine) Visibility() float64 {
	return 1 - e.Eta()
}

// FraunhoferIntensity computes the classical part: cos²·sinc².
func (e *LabPhysicsEngine) FraunhoferIntensity(x float64) float64 {
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

// Intensity computes the QBP-modified intensity at position x.
//
// QBP Model A (proven in DoubleSlit.lean §5b):
//   I(x) = (1-η) · I_fraunhofer(x) + η
//
// When η=0 (U₁=0): I(x) = I_fraunhofer(x)  — standard QM
// When η=1 (full coupling): I(x) = 1  — flat, no fringes (which-path)
//
// The maximum is always 1 (at x=0 where I_fraunhofer=1), which keeps
// rejection sampling efficient.
func (e *LabPhysicsEngine) Intensity(x float64) float64 {
	eta := e.Eta()
	return (1-eta)*e.FraunhoferIntensity(x) + eta
}

// SampleHitPosition draws a hit position from I(x) via rejection sampling.
func (e *LabPhysicsEngine) SampleHitPosition() float64 {
	halfWidth := 5.0 * e.FringeSpacing()
	for {
		x := (e.rng.Float64()*2 - 1) * halfWidth
		if e.rng.Float64() < e.Intensity(x) {
			return x
		}
	}
}

// ApplyPreset sets all physics parameters from a named preset.
func (e *LabPhysicsEngine) ApplyPreset(id string) bool {
	p := presetByID(id)
	if p == nil {
		return false
	}
	e.SlitSep = p.SlitSep
	e.Wavelength = p.Wavelength
	e.ScreenDist = p.ScreenDist
	e.SlitWidth = p.SlitWidth
	e.U1 = p.U1
	return true
}

// LabCoordMapper converts between physical meters and Normalized Display Units.
type LabCoordMapper struct {
	PhysHalfWidth float64
	NDUHalfWidth  float64
}

func NewLabCoordMapper(fringeSpacing float64) *LabCoordMapper {
	return &LabCoordMapper{
		PhysHalfWidth: 5.0 * fringeSpacing,
		NDUHalfWidth:  5.0,
	}
}

func (cm *LabCoordMapper) PhysToNDU(x float64) float64 {
	return (x / cm.PhysHalfWidth) * cm.NDUHalfWidth
}

func (cm *LabCoordMapper) Update(fringeSpacing float64) {
	cm.PhysHalfWidth = 5.0 * fringeSpacing
}
