-- Probability Theory: Poisson Arrivals
-- Why customers arrive randomly but predictably
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

-- ═══════════════════════════════════════════════════════════════════════════
-- POISSON DISTRIBUTION BASICS
-- ═══════════════════════════════════════════════════════════════════════════

-- Poisson PMF: P(X = k) = (λ^k * e^(-λ)) / k!
def poisson_pmf (λ : ℝ) (k : ℕ) : ℝ :=
  (λ ^ k * Real.exp (-λ)) / Nat.factorial k

-- Expected value: E[X] = λ
def poisson_mean (λ : ℝ) : ℝ := λ

-- Variance: Var[X] = λ
def poisson_variance (λ : ℝ) : ℝ := λ

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: Poisson PMF is a Valid Probability Distribution
-- ═══════════════════════════════════════════════════════════════════════════

theorem poisson_pmf_nonneg (λ : ℝ) (k : ℕ) (h_pos : 0 < λ) :
  0 ≤ poisson_pmf λ k := by
  unfold poisson_pmf
  -- λ^k > 0, e^(-λ) > 0, k! > 0 → PMF > 0
  sorry

theorem poisson_total_prob (λ : ℝ) (h_pos : 0 < λ) :
  ∑' k, poisson_pmf λ k = 1 := by
  unfold poisson_pmf
  -- ∑(λ^k / k!) = e^λ, so ∑(λ^k * e^(-λ) / k!) = e^(-λ) * e^λ = 1
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: Mean and Variance
-- ═══════════════════════════════════════════════════════════════════════════

theorem poisson_expected_value (λ : ℝ) (h_pos : 0 < λ) :
  ∑' k, (k : ℝ) * poisson_pmf λ k = λ := by
  unfold poisson_pmf
  -- E[X] = ∑ k * (λ^k * e^(-λ) / k!) = λ
  sorry

theorem poisson_variance_eq_mean (λ : ℝ) (h_pos : 0 < λ) :
  -- Var[X] = E[X²] - (E[X])²
  ∑' k, ((k : ℝ) ^ 2) * poisson_pmf λ k - λ^2 = λ := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: Rare Events Approximation
-- ═══════════════════════════════════════════════════════════════════════════

-- Binomial(n, p) → Poisson(λ) as n → ∞, p → 0, np → λ
def binomial_pmf (n k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose n k : ℝ) * p^k * (1 - p)^(n - k)

theorem rare_events_limit (λ : ℝ) (k : ℕ) (h_pos : 0 < λ) :
  -- As n → ∞ with p = λ/n, Binomial → Poisson
  ∃ N : ℕ, ∀ n ≥ N,
    |binomial_pmf n k (λ / n) - poisson_pmf λ k| < 0.01 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 4: Sum of Independent Poisson Variables
-- ═══════════════════════════════════════════════════════════════════════════

-- If X ~ Poisson(λ₁) and Y ~ Poisson(λ₂) are independent,
-- then X + Y ~ Poisson(λ₁ + λ₂)
theorem poisson_additivity (λ₁ λ₂ : ℝ) (k : ℕ)
    (h_pos1 : 0 < λ₁) (h_pos2 : 0 < λ₂) :
  -- PMF of sum equals PMF of Poisson(λ₁ + λ₂)
  (∑ i in Finset.range (k + 1),
    poisson_pmf λ₁ i * poisson_pmf λ₂ (k - i)) =
  poisson_pmf (λ₁ + λ₂) k := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 5: Most Likely Number of Arrivals
-- ═══════════════════════════════════════════════════════════════════════════

-- The mode of Poisson(λ) is ⌊λ⌋ or ⌈λ⌉
theorem poisson_mode (λ : ℝ) (h_pos : 0 < λ) :
  let k := λ.floor.toNat
  -- k or k+1 maximizes PMF
  ∀ j : ℕ, j ≠ k → j ≠ k + 1 →
    poisson_pmf λ k ≥ poisson_pmf λ j ∨
    poisson_pmf λ (k + 1) ≥ poisson_pmf λ j := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 6: Waiting Time Distribution (Exponential)
-- ═══════════════════════════════════════════════════════════════════════════

-- If arrivals follow Poisson(λ) per unit time,
-- then time between arrivals ~ Exponential(λ)
def exponential_pdf (λ : ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 0 else λ * Real.exp (-λ * t)

-- Probability of 0 arrivals in time t equals P(waiting time > t)
theorem poisson_exponential_connection (λ : ℝ) (t : ℝ)
    (h_pos : 0 < λ) (h_t_pos : 0 ≤ t) :
  poisson_pmf (λ * t) 0 = Real.exp (-λ * t) := by
  unfold poisson_pmf
  simp [Nat.factorial]
  -- (λt)^0 * e^(-λt) / 0! = e^(-λt)
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- PRACTICAL EXAMPLE: Restaurant Customers
-- ═══════════════════════════════════════════════════════════════════════════

-- Average 20 customers per hour
def restaurant_rate : ℝ := 20

-- Probability of exactly k customers in 1 hour
def prob_k_customers (k : ℕ) : ℝ :=
  poisson_pmf restaurant_rate k

-- Most likely: 19, 20, or 21 customers
example :
  prob_k_customers 20 ≥ prob_k_customers 15 ∧
  prob_k_customers 20 ≥ prob_k_customers 25 := by
  unfold prob_k_customers poisson_pmf restaurant_rate
  sorry

-- Very unlikely to have 0 or 40+ customers
example :
  prob_k_customers 0 < 0.00001 ∧
  prob_k_customers 40 < 0.01 := by
  unfold prob_k_customers poisson_pmf restaurant_rate
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 7: Confidence Intervals
-- ═══════════════════════════════════════════════════════════════════════════

-- For Poisson(λ), approximately 95% of observations fall in [λ - 2√λ, λ + 2√λ]
theorem poisson_confidence_interval (λ : ℝ) (h_pos : 5 < λ) :
  -- P(|X - λ| ≤ 2√λ) ≈ 0.95
  let lower := (λ - 2 * Real.sqrt λ).floor.toNat
  let upper := (λ + 2 * Real.sqrt λ).ceil.toNat
  ∑ k in Finset.range upper,
    if k ≥ lower then poisson_pmf λ k else 0 ≥ 0.95 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- WHY POISSON MODELS WORK FOR RARE EVENTS
-- ═══════════════════════════════════════════════════════════════════════════

-- The Poisson distribution emerges when:
-- 1. Events occur independently
-- 2. Average rate λ is constant
-- 3. Two events rarely occur simultaneously

-- Examples:
-- • Customer arrivals (independent, constant rate)
-- • Phone calls to a call center
-- • Emails received per hour
-- • Radioactive decay events
-- • Website visits per minute
-- • Typos per page in a book

-- The key insight: Even though individual events are random and unpredictable,
-- the AGGREGATE behavior follows a precise mathematical distribution!
-- This is why businesses can plan staffing even though each customer is random.

theorem poisson_predictable_aggregate (λ : ℝ) (n : ℕ) (h_pos : 0 < λ) :
  -- Over n independent periods, total arrivals ~ Poisson(n * λ)
  -- Variance grows as n*λ, but relative error √(nλ)/(nλ) = 1/√(nλ) → 0
  let total_mean := n * λ
  let relative_std := Real.sqrt total_mean / total_mean
  relative_std = 1 / Real.sqrt (n * λ) := by
  unfold_let
  field_simp
  sorry

-- As n → ∞, predictions become MORE accurate (law of large numbers)!
