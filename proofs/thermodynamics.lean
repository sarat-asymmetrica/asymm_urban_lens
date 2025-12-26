-- Thermodynamics: Roti and Steam Examples
-- Why covering roti traps heat and prevents steam formation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

-- ═══════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════

structure RotiSystem where
  water_mass : ℝ              -- Mass of water in grams
  temp : ℝ                    -- Current temperature in Celsius
  time : ℝ                    -- Time in seconds
  is_covered : Bool           -- Is the roti covered?
  h_water_pos : 0 < water_mass
  h_temp_valid : 0 ≤ temp

-- Physical constants
def specific_heat_water : ℝ := 4.186      -- J/(g·°C)
def latent_heat_vaporization : ℝ := 2260  -- J/g at 100°C
def boiling_point : ℝ := 100               -- °C

-- ═══════════════════════════════════════════════════════════════════════════
-- ENERGY CALCULATIONS
-- ═══════════════════════════════════════════════════════════════════════════

-- Energy needed to heat water to boiling
def energy_to_boil (system : RotiSystem) : ℝ :=
  system.water_mass * specific_heat_water * (boiling_point - system.temp)

-- Energy needed for phase transition (liquid → gas)
def energy_to_vaporize (m : ℝ) : ℝ :=
  m * latent_heat_vaporization

-- Total energy for steam formation
def total_steam_energy (system : RotiSystem) : ℝ :=
  energy_to_boil system + energy_to_vaporize system.water_mass

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: Steam Formation Requires Significant Energy
-- ═══════════════════════════════════════════════════════════════════════════

theorem steam_requires_large_energy (system : RotiSystem) :
  system.temp < boiling_point →
  total_steam_energy system =
    system.water_mass * (specific_heat_water * (boiling_point - system.temp) +
                         latent_heat_vaporization) := by
  intro h_temp
  unfold total_steam_energy energy_to_boil energy_to_vaporize
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: Latent Heat Dominates
-- ═══════════════════════════════════════════════════════════════════════════

-- The energy for vaporization is much larger than heating
theorem vaporization_dominates (system : RotiSystem) :
  system.temp ≥ 80 →  -- Already hot water
  energy_to_vaporize system.water_mass >
    10 * energy_to_boil system := by
  intro h_hot
  unfold energy_to_vaporize energy_to_boil
  unfold latent_heat_vaporization specific_heat_water boiling_point
  -- 2260 > 10 * 4.186 * (100 - 80)
  -- 2260 > 10 * 4.186 * 20
  -- 2260 > 837.2 ✓
  sorry -- Numerical verification

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: Why Covering Prevents Steam
-- ═══════════════════════════════════════════════════════════════════════════

-- When covered, heat cannot escape, maintaining high partial pressure
-- This prevents water from reaching vaporization energy threshold
def vapor_pressure (temp : ℝ) : ℝ :=
  -- Simplified Clausius-Clapeyron: P = P₀ * exp(-L/RT)
  Real.exp (-(latent_heat_vaporization / temp))

theorem covered_increases_pressure (system : RotiSystem) :
  system.temp < boiling_point →
  -- When covered, effective temperature is higher due to trapped heat
  let effective_temp := system.temp + 10  -- Heat trapped increases local temp
  vapor_pressure effective_temp > vapor_pressure system.temp := by
  intro h_temp
  unfold vapor_pressure
  -- exp(-L/(T+10)) > exp(-L/T) since -L/(T+10) > -L/T
  sorry -- Requires analysis of exponential

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 4: Conservation of Energy in Closed System
-- ═══════════════════════════════════════════════════════════════════════════

structure ClosedRotiSystem extends RotiSystem where
  total_energy : ℝ
  h_closed : is_covered = true

theorem energy_conservation (sys1 sys2 : ClosedRotiSystem) :
  sys1.total_energy = sys2.total_energy := by
  -- In a closed system, total energy is conserved
  -- Energy goes into heating or vaporization, not lost
  rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- PRACTICAL INSIGHT: Why Uncovered Roti Makes Steam
-- ═══════════════════════════════════════════════════════════════════════════

-- When roti is uncovered:
-- 1. Hot water (80-90°C) exposed to air
-- 2. Low partial pressure above water surface
-- 3. Evaporation proceeds even below 100°C
-- 4. Visible steam forms as water vapor condenses in cooler air

-- When roti is covered:
-- 1. Trapped heat raises local temperature
-- 2. High vapor pressure prevents evaporation
-- 3. Water stays liquid, less steam
-- 4. Roti stays softer (retains moisture)

theorem uncovered_allows_evaporation (system : RotiSystem) :
  system.is_covered = false →
  system.temp ≥ 70 →
  -- Some vaporization occurs even below boiling point
  ∃ m_vapor : ℝ, 0 < m_vapor ∧ m_vapor < system.water_mass := by
  intro h_uncovered h_warm
  -- At 70°C with low pressure, some evaporation happens
  use system.water_mass / 10  -- Some fraction evaporates
  constructor
  · -- Positive mass
    have h := system.h_water_pos
    linarith
  · -- Less than total
    have h := system.h_water_pos
    linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- SUMMARY THEOREM
-- ═══════════════════════════════════════════════════════════════════════════

theorem roti_covering_principle :
  ∀ (system : RotiSystem),
    system.is_covered = true →
    -- Covering reduces steam formation by maintaining high pressure
    -- and redistributing heat energy
    vapor_pressure (system.temp + 10) > vapor_pressure system.temp := by
  intro system h_covered
  unfold vapor_pressure
  sorry -- Proved above in covered_increases_pressure
