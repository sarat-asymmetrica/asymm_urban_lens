-- Basic Arithmetic Proofs
-- Starter proofs for Asya platform

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Proof: 2 + 2 = 4 (the classic!)
theorem two_plus_two : 2 + 2 = 4 := by
  rfl

-- Proof: Addition is commutative
theorem add_comm_example : 3 + 5 = 5 + 3 := by
  ring

-- Proof: Addition is associative
theorem add_assoc_example : (2 + 3) + 4 = 2 + (3 + 4) := by
  ring

-- Proof: Zero is additive identity
theorem zero_add_example (n : ℕ) : 0 + n = n := by
  simp

-- Proof: Multiplication distributes over addition
theorem distrib_example : 2 * (3 + 4) = 2 * 3 + 2 * 4 := by
  ring

-- Proof: n + 0 = n for natural numbers
theorem add_zero (n : ℕ) : n + 0 = n := by
  simp

-- Proof: 1 is multiplicative identity
theorem one_mul (n : ℕ) : 1 * n = n := by
  simp

-- Proof: Multiplication by zero
theorem mul_zero (n : ℕ) : n * 0 = 0 := by
  simp

-- Proof: Successor function
theorem succ_eq_add_one (n : ℕ) : Nat.succ n = n + 1 := by
  rfl

-- Proof: Double is two times
theorem double_is_two_mul (n : ℕ) : n + n = 2 * n := by
  ring
