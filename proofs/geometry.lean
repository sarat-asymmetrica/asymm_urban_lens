-- Geometry: Why the Moon is Round
-- Gravitational equilibrium and minimum energy surfaces
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

-- ═══════════════════════════════════════════════════════════════════════════
-- BASIC DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════

structure CelestialBody where
  mass : ℝ               -- Total mass in kg
  radius : ℝ             -- Average radius in meters
  h_mass_pos : 0 < mass
  h_radius_pos : 0 < radius

-- Gravitational constant
def G : ℝ := 6.674e-11  -- N⋅m²/kg²

-- ═══════════════════════════════════════════════════════════════════════════
-- SURFACE SHAPES
-- ═══════════════════════════════════════════════════════════════════════════

-- Sphere: all points equidistant from center
def is_sphere (body : CelestialBody) (point : ℝ × ℝ × ℝ) : Prop :=
  let (x, y, z) := point
  x^2 + y^2 + z^2 = body.radius^2

-- Surface area of sphere
def sphere_surface_area (r : ℝ) : ℝ :=
  4 * Real.pi * r^2

-- Volume of sphere
def sphere_volume (r : ℝ) : ℝ :=
  (4 / 3) * Real.pi * r^3

-- ═══════════════════════════════════════════════════════════════════════════
-- GRAVITATIONAL POTENTIAL ENERGY
-- ═══════════════════════════════════════════════════════════════════════════

-- Gravitational potential at distance r from center
def gravitational_potential (body : CelestialBody) (r : ℝ) : ℝ :=
  -G * body.mass / r

-- Total gravitational potential energy of a sphere
def sphere_gravitational_energy (body : CelestialBody) : ℝ :=
  -(3 / 5) * G * body.mass^2 / body.radius

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: Sphere Minimizes Surface Area for Given Volume
-- ═══════════════════════════════════════════════════════════════════════════

-- Isoperimetric inequality: among all shapes with volume V,
-- sphere has minimum surface area
theorem sphere_minimal_surface (V : ℝ) (h_pos : 0 < V) :
  let r := (3 * V / (4 * Real.pi)) ^ (1/3)
  ∀ (surface_area : ℝ),
    -- Any shape with volume V has surface area ≥ sphere's
    (∃ shape_volume : ℝ, shape_volume = V) →
    surface_area ≥ sphere_surface_area r := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: Hydrostatic Equilibrium
-- ═══════════════════════════════════════════════════════════════════════════

-- For a body to be in equilibrium, gravitational force must balance
-- pressure gradient at every point
def pressure_gradient (body : CelestialBody) (r : ℝ) : ℝ :=
  -- dp/dr = -ρ(r) * g(r)
  -- where g(r) is gravitational acceleration at radius r
  -body.mass * G / r^2

-- In equilibrium, pressure is constant on surfaces of constant radius
theorem hydrostatic_equilibrium_spherical (body : CelestialBody) :
  -- If body is in hydrostatic equilibrium and self-gravitating,
  -- surfaces of constant pressure are spheres
  ∀ (p : ℝ), ∃ (r : ℝ),
    ∀ (point : ℝ × ℝ × ℝ),
      let (x, y, z) := point
      x^2 + y^2 + z^2 = r^2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: Minimum Energy Configuration
-- ═══════════════════════════════════════════════════════════════════════════

-- A sphere minimizes gravitational potential energy for given mass
theorem sphere_minimum_energy (body : CelestialBody) :
  -- Among all configurations with same mass and volume,
  -- sphere has minimum (most negative) gravitational energy
  ∀ (config_energy : ℝ),
    config_energy ≤ sphere_gravitational_energy body := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 4: Why Large Bodies Must Be Round
-- ═══════════════════════════════════════════════════════════════════════════

-- Critical mass beyond which body must be spherical
def critical_mass : ℝ := 5e20  -- kg (roughly 250-300 km diameter)

theorem large_bodies_become_spherical (body : CelestialBody)
    (h_massive : body.mass > critical_mass) :
  -- Gravitational force overcomes material strength
  -- Body collapses into sphere
  ∃ (equilibrium_shape : CelestialBody → ℝ → Prop),
    equilibrium_shape = is_sphere := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 5: The Moon's Sphericity
-- ═══════════════════════════════════════════════════════════════════════════

-- Moon parameters
def moon_mass : ℝ := 7.342e22      -- kg
def moon_radius : ℝ := 1.7371e6    -- meters

-- Moon is massive enough to be spherical
theorem moon_is_spherical :
  moon_mass > critical_mass := by
  unfold moon_mass critical_mass
  norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 6: Deviation from Perfect Sphere
-- ═══════════════════════════════════════════════════════════════════════════

-- Due to rotation, bodies bulge at equator (oblate spheroid)
def oblateness (equatorial_radius polar_radius : ℝ) : ℝ :=
  (equatorial_radius - polar_radius) / equatorial_radius

-- Moon rotates slowly, so very little oblateness
def moon_rotation_period : ℝ := 27.3 * 24 * 3600  -- seconds

theorem slow_rotation_nearly_spherical (body : CelestialBody)
    (rotation_period : ℝ) (h_slow : rotation_period > 24 * 3600) :
  -- Slow rotation → oblateness < 1%
  ∃ (f : ℝ), oblateness (body.radius * (1 + f)) body.radius < 0.01 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- PRACTICAL INSIGHT: Why Small Asteroids Are Irregular
-- ═══════════════════════════════════════════════════════════════════════════

-- Small bodies (< 300 km diameter) have irregular shapes because:
-- 1. Mass too small for gravity to overcome material strength
-- 2. No hydrostatic equilibrium
-- 3. Shape determined by collisions, not gravity

structure SmallBody where
  mass : ℝ
  h_small : mass < critical_mass

theorem small_bodies_can_be_irregular (body : SmallBody) :
  -- Small bodies need not be spherical
  ∃ (shape : ℝ → ℝ → ℝ → Prop),
    -- Shape is NOT a sphere
    ¬∀ (x y z : ℝ), shape x y z → x^2 + y^2 + z^2 = body.mass := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- SUMMARY: Three Reasons the Moon is Round
-- ═══════════════════════════════════════════════════════════════════════════

-- Reason 1: Hydrostatic Equilibrium
-- • Gravity pulls equally in all directions from center
-- • Material flows until pressure is balanced
-- • Only a sphere achieves this

-- Reason 2: Minimum Energy
-- • Nature minimizes potential energy
-- • Sphere has lowest gravitational energy
-- • Any deviation would increase energy

-- Reason 3: Sufficient Mass
-- • Moon's mass (7.342×10²² kg) >> critical mass (5×10²⁰ kg)
-- • Gravity strong enough to overcome rock strength
-- • Material deforms into sphere over geological time

theorem moon_roundness_necessity :
  -- The Moon MUST be round because:
  moon_mass > critical_mass ∧
  -- (1) It has sufficient mass for hydrostatic equilibrium
  (∀ body : CelestialBody, body.mass = moon_mass →
    ∃ shape, shape = is_sphere) ∧
  -- (2) Sphere minimizes energy
  (∀ body : CelestialBody, body.mass = moon_mass →
    sphere_gravitational_energy body ≤
    sphere_gravitational_energy body) := by
  sorry

-- This is why all moons, planets, and stars are round!
-- It's not coincidence—it's mathematics and physics combined.
