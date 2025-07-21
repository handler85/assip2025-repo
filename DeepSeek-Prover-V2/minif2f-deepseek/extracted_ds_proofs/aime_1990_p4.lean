import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  have h_main : x = 13 := by
    have h₅ : x^2 - 10 * x - 29 ≠ 0 := h₁
    have h₆ : x^2 - 10 * x - 45 ≠ 0 := h₂
    have h₇ : x^2 - 10 * x - 69 ≠ 0 := h₃
    have h₈ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0 := h₄
    field_simp at h₈
    ring_nf at h₈
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₅)
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₆)
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₇)
    nlinarith [sq_pos_of_ne_zero h₅, sq_pos_of_ne_zero h₆, sq_pos_of_ne_zero h₇,
      sq_nonneg (x - 13), sq_nonneg (x + 13), sq_nonneg (x^2 - 10 * x - 29),
      sq_nonneg (x^2 - 10 * x - 45), sq_nonneg (x^2 - 10 * x - 69)]
  exact h_main
