-- Wave Mechanics: Interference and Superposition
-- Two waves of same frequency can constructively or destructively interfere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

-- ═══════════════════════════════════════════════════════════════════════════
-- BASIC WAVE STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════

structure Wave where
  amplitude : ℝ           -- Wave amplitude (A)
  frequency : ℝ           -- Frequency (f) in Hz
  phase : ℝ               -- Phase angle (φ) in radians
  wavelength : ℝ          -- Wavelength (λ) in meters
  h_amp_pos : 0 ≤ amplitude
  h_freq_pos : 0 < frequency
  h_wavelength_pos : 0 < wavelength

-- Wave velocity (v = fλ)
def wave_velocity (w : Wave) : ℝ :=
  w.frequency * w.wavelength

-- Wave number (k = 2π/λ)
def wave_number (w : Wave) : ℝ :=
  2 * Real.pi / w.wavelength

-- Angular frequency (ω = 2πf)
def angular_frequency (w : Wave) : ℝ :=
  2 * Real.pi * w.frequency

-- Wave function: y(x,t) = A sin(kx - ωt + φ)
def wave_function (w : Wave) (x t : ℝ) : ℝ :=
  w.amplitude * Real.sin (wave_number w * x - angular_frequency w * t + w.phase)

-- ═══════════════════════════════════════════════════════════════════════════
-- INTENSITY
-- ═══════════════════════════════════════════════════════════════════════════

-- Intensity is proportional to amplitude squared
def intensity (w : Wave) : ℝ :=
  w.amplitude ^ 2

theorem intensity_nonneg (w : Wave) :
  0 ≤ intensity w := by
  unfold intensity
  have h := w.h_amp_pos
  nlinarith [sq_nonneg w.amplitude]

-- ═══════════════════════════════════════════════════════════════════════════
-- PHASE DIFFERENCE
-- ═══════════════════════════════════════════════════════════════════════════

def phase_difference (w1 w2 : Wave) : ℝ :=
  w1.phase - w2.phase

-- Normalize phase difference to [-π, π]
def normalized_phase_diff (w1 w2 : Wave) : ℝ :=
  let diff := phase_difference w1 w2
  -- Wrap to [-π, π]
  if diff > Real.pi then diff - 2 * Real.pi
  else if diff < -Real.pi then diff + 2 * Real.pi
  else diff

-- ═══════════════════════════════════════════════════════════════════════════
-- SUPERPOSITION PRINCIPLE
-- ═══════════════════════════════════════════════════════════════════════════

-- When two waves meet, they add
instance : Add Wave where
  add w1 w2 := {
    amplitude := Real.sqrt (
      w1.amplitude^2 + w2.amplitude^2 +
      2 * w1.amplitude * w2.amplitude * Real.cos (phase_difference w1 w2)
    )
    frequency := w1.frequency  -- Assume same frequency
    phase := 0  -- Simplified
    wavelength := w1.wavelength
    h_amp_pos := by sorry
    h_freq_pos := w1.h_freq_pos
    h_wavelength_pos := w1.h_wavelength_pos
  }

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: Constructive Interference
-- ═══════════════════════════════════════════════════════════════════════════

-- When waves are in phase (φ = 0), amplitudes add
theorem constructive_interference (w1 w2 : Wave)
    (h_same_freq : w1.frequency = w2.frequency)
    (h_in_phase : phase_difference w1 w2 = 0) :
  (w1 + w2).amplitude = w1.amplitude + w2.amplitude := by
  unfold phase_difference at h_in_phase
  simp [Add.add]
  -- When cos(0) = 1:
  -- A = √(A₁² + A₂² + 2A₁A₂) = √((A₁ + A₂)²) = A₁ + A₂
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: Destructive Interference
-- ═══════════════════════════════════════════════════════════════════════════

-- When waves are out of phase (φ = π), amplitudes subtract
theorem destructive_interference (w1 w2 : Wave)
    (h_same_freq : w1.frequency = w2.frequency)
    (h_out_phase : phase_difference w1 w2 = Real.pi)
    (h_eq_amp : w1.amplitude = w2.amplitude) :
  (w1 + w2).amplitude = 0 := by
  unfold phase_difference at h_out_phase
  simp [Add.add]
  -- When cos(π) = -1 and A₁ = A₂:
  -- A = √(A₁² + A₂² - 2A₁A₂) = √((A₁ - A₂)²) = 0
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: Intensity of Superposed Waves
-- ═══════════════════════════════════════════════════════════════════════════

theorem interference_intensity (w1 w2 : Wave)
    (h_same_freq : w1.frequency = w2.frequency) :
  intensity (w1 + w2) =
    intensity w1 + intensity w2 +
    2 * Real.sqrt (intensity w1 * intensity w2) * Real.cos (phase_difference w1 w2) := by
  unfold intensity
  simp [Add.add]
  -- I = A² = A₁² + A₂² + 2A₁A₂cos(φ)
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 4: Intensity Bounds
-- ═══════════════════════════════════════════════════════════════════════════

-- Combined intensity is bounded
theorem intensity_bounds (w1 w2 : Wave)
    (h_same_freq : w1.frequency = w2.frequency) :
  (Real.sqrt (intensity w1) - Real.sqrt (intensity w2))^2 ≤
  intensity (w1 + w2) ∧
  intensity (w1 + w2) ≤
  (Real.sqrt (intensity w1) + Real.sqrt (intensity w2))^2 := by
  constructor
  · -- Minimum (destructive): I_min = (I₁^½ - I₂^½)²
    sorry
  · -- Maximum (constructive): I_max = (I₁^½ + I₂^½)²
    sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 5: Same Wavelength Requirement
-- ═══════════════════════════════════════════════════════════════════════════

-- For stable interference pattern, waves must have same frequency
theorem stable_interference_needs_same_frequency (w1 w2 : Wave) :
  w1.frequency = w2.frequency ↔
  ∃ (pattern : ℝ → ℝ → ℝ), ∀ x t,
    wave_function (w1 + w2) x t = pattern x t := by
  constructor
  · intro h_same_freq
    -- When frequencies match, pattern is stable
    use λ x t => wave_function (w1 + w2) x t
    intro x t
    rfl
  · intro h_stable
    -- If pattern is stable, frequencies must match
    sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- PRACTICAL EXAMPLES
-- ═══════════════════════════════════════════════════════════════════════════

-- Example 1: Two identical waves in phase → double amplitude
example : ∃ (w1 w2 : Wave),
  w1.amplitude = 1 ∧
  w2.amplitude = 1 ∧
  phase_difference w1 w2 = 0 ∧
  (w1 + w2).amplitude = 2 := by
  sorry

-- Example 2: Two identical waves out of phase → cancellation
example : ∃ (w1 w2 : Wave),
  w1.amplitude = 1 ∧
  w2.amplitude = 1 ∧
  phase_difference w1 w2 = Real.pi ∧
  (w1 + w2).amplitude = 0 := by
  sorry

-- Example 3: 90° phase shift → √2 amplitude (equal contribution)
example : ∃ (w1 w2 : Wave),
  w1.amplitude = 1 ∧
  w2.amplitude = 1 ∧
  phase_difference w1 w2 = Real.pi / 2 ∧
  (w1 + w2).amplitude = Real.sqrt 2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- PHYSICAL INSIGHT
-- ═══════════════════════════════════════════════════════════════════════════

-- This is why:
-- • Noise-canceling headphones work (destructive interference)
-- • Soap bubbles show colors (thin film interference)
-- • Radio dead zones exist (wave cancellation)
-- • Concert halls have "sweet spots" (constructive interference)

-- The key: phase difference determines if waves help or hurt each other!
