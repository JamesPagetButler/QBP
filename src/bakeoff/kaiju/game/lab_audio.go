//go:build !editor

// Audio feedback for the QBP Virtual Lab.
//
// Implements the "Hear" dimension of the scientist UX:
//   - Particle click: short tick on each detector hit (rate-limited)
//   - Verdict ding: pleasant tone when V&V passes
//   - Verdict buzz: low tone when V&V fails
//
// Sounds are generated procedurally as WAV data — no external audio files needed.
// Uses Kaiju's SoLoud audio backend via host.Audio().

package main

import (
	"encoding/binary"
	"kaiju/engine"
	"kaiju/platform/audio"
	"math"
)

type LabAudio struct {
	host *engine.Host

	clickClip    *audio.AudioClip
	dingClip     *audio.AudioClip
	buzzClip     *audio.AudioClip
	hoverClip    *audio.AudioClip  // Subtle hover tick
	buttonClip   *audio.AudioClip  // Satisfying button click

	// Rate limiter for particle clicks (avoid 500 clicks/sec)
	clickBudget float64 // Accumulated time budget
	clickRate   float64 // Max clicks per second
	lastVerdict VVVerdict
}

func NewLabAudio(host *engine.Host) *LabAudio {
	la := &LabAudio{
		host:        host,
		clickRate:   15, // 15 clicks/sec max (Geiger counter feel)
		lastVerdict: VerdictCollecting,
	}
	la.generateSounds()
	return la
}

// OnParticleHit should be called each frame with the number of new hits.
// Rate-limits audio to avoid overwhelming the sound system.
func (la *LabAudio) OnParticleHit(dt float64, newHits int) {
	if la.clickClip == nil || newHits == 0 {
		return
	}

	la.clickBudget += dt * la.clickRate
	if la.clickBudget > 3 {
		la.clickBudget = 3 // Cap burst
	}

	if la.clickBudget >= 1 {
		la.host.Audio().Play(la.clickClip)
		la.clickBudget -= 1
	}
}

// OnVerdictChange plays a sound when the verdict changes.
func (la *LabAudio) OnVerdictChange(verdict VVVerdict) {
	if verdict == la.lastVerdict {
		return
	}
	la.lastVerdict = verdict

	switch verdict {
	case VerdictPass:
		if la.dingClip != nil {
			la.host.Audio().Play(la.dingClip)
		}
	case VerdictFail:
		if la.buzzClip != nil {
			la.host.Audio().Play(la.buzzClip)
		}
	}
}

// OnHover plays a subtle tick when the crosshair enters a new control.
func (la *LabAudio) OnHover() {
	if la.hoverClip != nil {
		la.host.Audio().Play(la.hoverClip)
	}
}

// OnButtonClick plays a satisfying mechanical click when a desk control is pressed.
func (la *LabAudio) OnButtonClick() {
	if la.buttonClip != nil {
		la.host.Audio().Play(la.buttonClip)
	}
}

func (la *LabAudio) generateSounds() {
	adb := la.host.AssetDatabase()
	a := la.host.Audio()

	// Click: 15ms white-noise burst with exponential decay
	clickWav := generateClick(44100, 0.015)
	adb.Cache("lab_click.wav", clickWav)
	la.clickClip, _ = a.LoadSound(adb, "lab_click.wav")

	// Ding: 200ms sine at 880Hz with decay (pleasant A5)
	dingWav := generateTone(44100, 0.2, 880, 0.4)
	adb.Cache("lab_ding.wav", dingWav)
	la.dingClip, _ = a.LoadSound(adb, "lab_ding.wav")

	// Buzz: 200ms sawtooth at 220Hz (low warning A3)
	buzzWav := generateBuzz(44100, 0.2, 220, 0.3)
	adb.Cache("lab_buzz.wav", buzzWav)
	la.buzzClip, _ = a.LoadSound(adb, "lab_buzz.wav")

	// Hover tick: 5ms very quiet click (subtle feedback)
	hoverWav := generateClick(44100, 0.005)
	adb.Cache("lab_hover.wav", hoverWav)
	la.hoverClip, _ = a.LoadSound(adb, "lab_hover.wav")

	// Button click: 30ms mid-frequency snap (satisfying mechanical feel)
	buttonWav := generateTone(44100, 0.03, 1200, 0.5)
	adb.Cache("lab_button.wav", buttonWav)
	la.buttonClip, _ = a.LoadSound(adb, "lab_button.wav")
}

// ---------------------------------------------------------------------------
// Procedural WAV generators
// ---------------------------------------------------------------------------

// generateClick creates a short noise burst with exponential decay.
func generateClick(sampleRate int, duration float64) []byte {
	numSamples := int(float64(sampleRate) * duration)
	samples := make([]int16, numSamples)

	// Simple LCG for deterministic noise (no rand dependency)
	seed := uint32(0xDEADBEEF)
	for i := range samples {
		seed = seed*1664525 + 1013904223
		noise := float64(int32(seed)) / float64(math.MaxInt32)
		decay := math.Exp(-float64(i) / float64(numSamples) * 6)
		samples[i] = int16(noise * decay * 16000)
	}
	return encodeWAV(samples, sampleRate)
}

// generateTone creates a sine wave with exponential decay.
func generateTone(sampleRate int, duration, freq, volume float64) []byte {
	numSamples := int(float64(sampleRate) * duration)
	samples := make([]int16, numSamples)

	for i := range samples {
		t := float64(i) / float64(sampleRate)
		decay := math.Exp(-t / duration * 4)
		val := math.Sin(2*math.Pi*freq*t) * decay * volume
		samples[i] = int16(val * 32000)
	}
	return encodeWAV(samples, sampleRate)
}

// generateBuzz creates a sawtooth wave with slight decay (warning tone).
func generateBuzz(sampleRate int, duration, freq, volume float64) []byte {
	numSamples := int(float64(sampleRate) * duration)
	samples := make([]int16, numSamples)

	period := float64(sampleRate) / freq
	for i := range samples {
		t := float64(i) / float64(sampleRate)
		decay := math.Exp(-t / duration * 2)
		phase := math.Mod(float64(i), period) / period
		saw := 2*phase - 1
		samples[i] = int16(saw * decay * volume * 32000)
	}
	return encodeWAV(samples, sampleRate)
}

// encodeWAV wraps 16-bit mono PCM samples in a WAV header.
func encodeWAV(samples []int16, sampleRate int) []byte {
	dataSize := len(samples) * 2
	fileSize := 44 + dataSize

	buf := make([]byte, fileSize)
	copy(buf[0:4], "RIFF")
	binary.LittleEndian.PutUint32(buf[4:8], uint32(fileSize-8))
	copy(buf[8:12], "WAVE")
	copy(buf[12:16], "fmt ")
	binary.LittleEndian.PutUint32(buf[16:20], 16) // Chunk size
	binary.LittleEndian.PutUint16(buf[20:22], 1)  // PCM
	binary.LittleEndian.PutUint16(buf[22:24], 1)  // Mono
	binary.LittleEndian.PutUint32(buf[24:28], uint32(sampleRate))
	binary.LittleEndian.PutUint32(buf[28:32], uint32(sampleRate*2)) // Byte rate
	binary.LittleEndian.PutUint16(buf[32:34], 2)                    // Block align
	binary.LittleEndian.PutUint16(buf[34:36], 16)                   // Bits per sample
	copy(buf[36:40], "data")
	binary.LittleEndian.PutUint32(buf[40:44], uint32(dataSize))

	for i, s := range samples {
		binary.LittleEndian.PutUint16(buf[44+i*2:46+i*2], uint16(s))
	}
	return buf
}
