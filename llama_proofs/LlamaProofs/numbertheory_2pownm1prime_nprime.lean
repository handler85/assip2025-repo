-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that if $n$ is a positive integer and $2^n - 1$ is prime, then $n$ is prime.-/
theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that if $n$ is a positive integer and $2^n - 1$ is prime, then $n$ is prime.-/
theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  intro n h₀ h₁
  have h₂ : 2 ^ n - 1 ≠ 0 := by
    intro h₃
    have h₄ : 2 ^ n = 1 := by
      have h₅ : 2 ^ n - 1 = 0 := by linarith [h₃]
      have h₆ : 2 ^ n = 1 - 1 := by linarith [h₅]
      linarith [h₆]
    linarith [h₄, h₀]
  have h₅ : 2 ^ n - 1 ≠ 2 := by
    intro h₃
    have h₄ : 2 ^ n = 2 := by
      have h₅ : 2 ^ n - 1 = 0 := by linarith [h₃]
      have h₆ : 2 ^ n = 2 - 1 := by linarith [h₅]
      linarith [h₆]
    linarith [h₄, h₀]
  have h₆ : 2 ^ n - 1 ≠ 2 ^ n := by
    intro h₃
    have h₄ : 2 ^ n - 1 = 2 ^ n := by linarith [h₃]
    linarith [h₄, h₂]
  have h₇ : 2 ^ n - 1 ≠ 2 ^ n + 1 := by
    intro h₃
    have h₄ : 2 ^ n - 1 = 2 ^ n + 1 := by linarith [h₃]
    linarith [h₄, h₂]
  have h₈ : 2 ^ n - 1 ≠ 2 ^ n - 2 := by
    intro h₃
    have h₄ : 2 ^ n - 1 = 2 ^ n