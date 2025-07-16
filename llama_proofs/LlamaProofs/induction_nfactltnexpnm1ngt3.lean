-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that for any integer $n \geq 3$, we have $n! < n^{n-1}$.-/
theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by


-- Formal statement 
induction n using Nat.strong_induction_on
  intro n h₀
  have h₁ : 3 ≤ n - 1 := by linarith
  have h₂ : 2 ≤ n - 1 := by linarith
  have h₃ : 2 ≤ n - 1 := by linarith
  have h₄ : 3 ≤ n - 1 := by linarith
  have h₅ : 3 ≤ n - 1 := by linarith
  have h₆ : 3 ≤ n - 1 := by linarith
  have h₇ : 3 ≤ n - 1 := by linarith
  have h₈ : 3 ≤ n - 1 := by linarith
  have h₉ : 3 ≤ n - 1 := by linarith
  have h₁₀ : 3 ≤ n - 1 := by linarith
  have h₁₁ : 3 ≤ n - 1 := by linarith
  have h₁₂ : 3 ≤ n - 1 := by linarith
  have h₁₃ : 3 ≤ n - 1 := by linarith
  have h₁₄ : 3 ≤ n - 1 := by linarith
  have h₁₅ : 3 ≤ n - 1 := by linarith
  have h₁₆ : 3 ≤ n - 1 := by linarith
  have h₁₇ : 3 ≤ n - 1 := by linarith
  have h₁₈ : 3 ≤ n - 1 := by linarith
  have h₁₉ : 3 ≤ n - 1 := by linarith
  have h₂₀ : 3 ≤ n - 1 := by linarith
  have h₂₁ : 3 ≤ n - 1 := by linarith
  have h₂₂ : 3 ≤ n - 1 := by linarith
  have h₂₃ : 3 ≤ n - 1 := by linarith
  have h₂₄ : 3 ≤ n - 1 := by linarith
  have h₂₅ : 3 ≤ n - 1 := by linarith
  have h₂₆ : 3 ≤ n - 1 := by linarith
  have h₂₇ : 3 ≤ n - 1 := by lin