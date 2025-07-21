import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by
  have h_main : f x = 30 - x := by
    have h₃ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15) := h₂
    rw [h₃]
    have h₄ : x ≥ p := by linarith
    have h₅ : x ≤ 15 := by linarith
    have h₆ : x - p ≥ 0 := by linarith
    have h₇ : x - 15 ≤ 0 := by linarith
    have h₈ : x - p - 15 ≤ 0 := by linarith
    have h₉ : abs (x - p) = x - p := by
      rw [abs_of_nonneg] <;> linarith
    have h₁₀ : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos] <;> linarith
    have h₁₁ : abs (x - p - 15) = 15 - x + p := by
      rw [abs_of_nonpos] <;> linarith
    rw [h₉, h₁₀, h₁₁]
    <;> ring_nf
    <;> linarith

  have h_final : 15 ≤ f x := by
    rw [h_main]
    have h₃ : x ≤ 15 := by linarith
    have h₄ : 30 - x ≥ 15 := by linarith
    linarith

  exact h_final
