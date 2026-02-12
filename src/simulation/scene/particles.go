// Package scene provides particle simulation for the Stern-Gerlach experiment.
package scene

import (
	"math"
	"math/rand"
	"sync"

	rl "github.com/gen2brain/raylib-go/raylib"

	"github.com/JamesPagetButler/QBP/simulation/physics"
)

// Particle represents a single quantum particle in the simulation.
type Particle struct {
	Pos      rl.Vector3
	Vel      rl.Vector3
	SpinUp   bool    // measurement outcome
	Alpha    float32 // opacity (fades as it travels)
	Active   bool
	Measured bool
}

// ParticleSystem manages the stream of particles through the apparatus.
type ParticleSystem struct {
	particles []Particle
	oracle    *physics.Oracle
	theta     float64 // current angle parameter
	mu        sync.Mutex
	emitRate  float32 // particles per second
	emitTimer float32
	maxParts  int
	rng       *rand.Rand

	// Statistics
	TotalUp   int
	TotalDown int
}

// NewParticleSystem creates a particle system with the given oracle and capacity.
func NewParticleSystem(oracle *physics.Oracle, maxParticles int) *ParticleSystem {
	return &ParticleSystem{
		particles: make([]Particle, 0, maxParticles),
		oracle:    oracle,
		theta:     math.Pi / 2, // default: 90 degrees
		emitRate:  30,
		maxParts:  maxParticles,
		rng:       rand.New(rand.NewSource(42)),
	}
}

// SetTheta updates the preparation angle (in radians).
func (ps *ParticleSystem) SetTheta(theta float64) {
	ps.mu.Lock()
	defer ps.mu.Unlock()
	ps.theta = theta
}

// Reset clears all particles and statistics.
func (ps *ParticleSystem) Reset() {
	ps.mu.Lock()
	defer ps.mu.Unlock()
	ps.particles = ps.particles[:0]
	ps.TotalUp = 0
	ps.TotalDown = 0
}

// Update advances the particle simulation by dt seconds.
func (ps *ParticleSystem) Update(dt float32) {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	// Emit new particles
	ps.emitTimer += dt
	emitInterval := float32(1.0) / ps.emitRate
	for ps.emitTimer >= emitInterval && len(ps.particles) < ps.maxParts {
		ps.emitTimer -= emitInterval
		ps.emit()
	}

	// Update existing particles
	magnetX := float32(0.0) // magnet center x position
	detectorX := float32(8.0)

	for i := range ps.particles {
		p := &ps.particles[i]
		if !p.Active {
			continue
		}

		// Move forward
		p.Pos.X += p.Vel.X * dt
		p.Pos.Y += p.Vel.Y * dt
		p.Pos.Z += p.Vel.Z * dt

		// When passing through magnet region, apply deflection
		if !p.Measured && p.Pos.X > magnetX-1 && p.Pos.X < magnetX+1 {
			p.Measured = true
			// Determine outcome based on oracle probability
			probUp := ps.oracle.ProbUp(ps.theta)
			if ps.rng.Float64() < probUp {
				p.SpinUp = true
				p.Vel.Y = 2.0 // deflect up
				ps.TotalUp++
			} else {
				p.SpinUp = false
				p.Vel.Y = -2.0 // deflect down
				ps.TotalDown++
			}
		}

		// Fade out as approaching detector
		if p.Pos.X > detectorX-2 {
			p.Alpha -= dt * 2
		}

		// Deactivate if past detector or fully faded
		if p.Pos.X > detectorX+1 || p.Alpha <= 0 {
			p.Active = false
		}
	}

	// Compact inactive particles
	ps.compact()
}

// emit creates a new particle at the source position.
func (ps *ParticleSystem) emit() {
	p := Particle{
		Pos:    rl.NewVector3(-8, 0, 0),
		Vel:    rl.NewVector3(6, 0, 0), // moving right
		Alpha:  1.0,
		Active: true,
	}
	// Small random spread
	p.Pos.Y += float32(ps.rng.Float64()-0.5) * 0.2
	p.Pos.Z += float32(ps.rng.Float64()-0.5) * 0.2
	ps.particles = append(ps.particles, p)
}

// compact removes inactive particles to free capacity.
func (ps *ParticleSystem) compact() {
	n := 0
	for i := range ps.particles {
		if ps.particles[i].Active {
			ps.particles[n] = ps.particles[i]
			n++
		}
	}
	ps.particles = ps.particles[:n]
}

// Draw renders all active particles.
func (ps *ParticleSystem) Draw() {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	for i := range ps.particles {
		p := &ps.particles[i]
		if !p.Active {
			continue
		}

		alpha := uint8(p.Alpha * 255)
		if alpha < 10 {
			continue
		}

		var color rl.Color
		if !p.Measured {
			// Before measurement: yellow (indeterminate)
			color = rl.NewColor(255, 255, 100, alpha)
		} else if p.SpinUp {
			// Spin up: bright cyan
			color = rl.NewColor(100, 255, 255, alpha)
		} else {
			// Spin down: orange
			color = rl.NewColor(255, 150, 50, alpha)
		}

		rl.DrawSphere(p.Pos, 0.12, color)

		// Draw spin arrow for measured particles
		if p.Measured {
			arrowLen := float32(0.4)
			dir := float32(1.0)
			if !p.SpinUp {
				dir = -1.0
			}
			arrowEnd := rl.NewVector3(p.Pos.X, p.Pos.Y+arrowLen*dir, p.Pos.Z)
			rl.DrawLine3D(p.Pos, arrowEnd, color)
		}
	}
}

// Stats returns current measurement statistics.
func (ps *ParticleSystem) Stats() (up, down, total int) {
	ps.mu.Lock()
	defer ps.mu.Unlock()
	return ps.TotalUp, ps.TotalDown, ps.TotalUp + ps.TotalDown
}
